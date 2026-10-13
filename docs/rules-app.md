# PCS_open golf: app challenge rules

## TL;DR

Build the smallest, cheapest-to-check zero-knowledge proof of a private withdrawal that an Ethereum contract can verify with two new primitives: `MUL_FIELD`, which multiplies binary field elements, and `PCS_open`, which lets the contract hand Ethereum a few facts about committed polynomials to check later. The score is proof bytes times the contract's verification cycles, with each fact charged a published price, and the proof must be produced within 250 ms on four threads. Every entry proves in Lean that it is complete, knowledge sound and zero knowledge. This is a draft modeled on [sig.golf](https://github.com/Layr-Labs/sig.golf/blob/main/RULES.md): the Lean contract and the verifier exist and have passed a dry run, but no entry has been verified yet. [The design notes](design.md) explain why the challenge exists and list what is still open.

## What Ethereum provides

A post-quantum proof has two layers. A **polynomial commitment** lets a prover commit to large polynomials with a short 32-byte **root** and later show single values of them. A **PIOP** (polynomial interactive oracle proof) is the logic that checks the computation, mostly by asking for a few such values at random points and testing that they fit together.

In this challenge Ethereum supplies only the first layer, plus field arithmetic:

- **`MUL_FIELD`** multiplies two elements of a binary field, which the EVM cannot do cheaply on its own.
- **`PCS_open`** records a **claim**: "the polynomial behind root `R` has value `v` at point `p`". The contract does not prove the claim. The wallet attaches an **opening proof** for it, which travels in the mempool beside the transaction. Nodes that receive the transaction check the opening proof directly, an aggregator checks it again inside a recursive proof, and each block carries one recursive proof that all of its claims are true. A block containing a false claim is invalid.

Everything else is the application's own code. Entrants write the prover and the contract's verifier, choose any PIOP, and prove the result correct in Lean. The [opening challenge](rules-opening.md) works on the other layer: making each claim cheap for Ethereum to check.

## The statement

Every entry proves the same thing: "I know a secret whose leaf is in the tree with this root, and this nullifier belongs to it", without revealing the secret, the leaf or its position.

- **Hash.** `H64(a, b) = Keccak-256(a ‖ b)` for two 32-byte strings, which is Ethereum's `KECCAK256` and one Keccak-f[1600] permutation for a 64-byte input. Keccak also serves the transcript and the pool's own tree, so no third primitive is needed.
- **Public input** `x = root ‖ nullifier ‖ context`, 96 bytes. `context` stands for the transaction's signature hash. It is not part of the relation, but the transcript absorbs it first, so a proof made for one transaction cannot be replayed in another.
- **Witness** `w = secret ‖ index ‖ siblings`: a 32-byte secret, the leaf's position as a little-endian `u32`, and 32 sibling hashes of 32 bytes each (1,060 bytes). Bit `i` of the position is `(index >> i) & 1`.
- **Tags.** `TAG_LEAF` and `TAG_NULLIFIER` are 32 bytes, all zero except the last byte, which is 1 and 2 respectively.

The relation `R(x, w)` holds when `leaf = H64(secret, TAG_LEAF)`, `nullifier = H64(secret, TAG_NULLIFIER)`, and hashing up the tree from `node_0 = leaf` gives the root: for each level `i` from 0 to 31, `node_{i+1} = H64(node_i, siblings[i])` if bit `i` is 0 and `H64(siblings[i], node_i)` otherwise, with `node_32 = root`. One statement costs 34 Keccak-f permutations, and the proof must compute them in its constraints.

## What you submit

1. A **verifier**: a RISC-V program that stands in for the contract (see [the verifier machine](#the-verifier-machine)).
2. A **prover**: a Lean definition, used in the proofs, and a native implementation, which the harness times (see [prover budget](#prover-budget)).
3. Four numbers: `B`, the proof size in bytes; `N`, the number of claims the verifier makes; `C₀`, the most cycles the verifier spends on an honest proof outside its claims; and `M`, how many of those claims are on roots that come from the proof rather than from the fixed roots, which sets the [soundness margin](#knowledge-soundness).
4. The **fixed polynomials** the verifier relies on, if any (see [fixed polynomials](#fixed-polynomials)).
5. Two memory offsets, δ<sub>x</sub> and δ<sub>vk</sub>, where the verifier finds the public input and the fixed roots.
6. **Lean proofs** of the [required statements](#what-you-must-prove) for exactly these programs and numbers.

## Score

```text
score = B × (C₀ + N × CLAIM_CYCLES)
```

Lower is better, and ties go to the earlier submission. `B` is everything the proof puts in the transaction. Claims add nothing to `B`, because the contract builds them while it runs: the values are already in the proof, the points are computed by the contract, and the roots are in the proof or among the fixed roots. `C₀` is the verifier's work outside its claims, counted in cycles. `CLAIM_CYCLES` is the published price of one claim, so certificates prove `B`, `N` and `C₀` but never the price: when the price changes, every entry is re-ranked without new proofs. Each record is published with its estimated gas (16 per proof byte plus about 3 per cycle) and with `N`, so it can be compared at any price.

Proving time is a pass or fail test, not part of the score (see [prover budget](#prover-budget)).

## Parameters

These values form **parameter set v0**. Organizers change them only on announced dates, and then re-time and re-score every entry.

| Constant | Value | Meaning |
| --- | ---: | --- |
| `DEPTH` | 32 | Tree depth in the statement |
| `CLAIM_CYCLES` | 6,500 | Price of one claim in cycles, about 20,000 gas, an estimate for leanVM's hiding WHIR (see [Reference entry](rules-opening.md#reference-entry)) |
| `SECURITY_BITS` | 128 | Soundness target |
| `LIST_BITS` | 12 | Soundness margin per root, equal to the opening challenge's `MAX_LIST_BITS` (see [knowledge soundness](#knowledge-soundness)) |
| `ZK_BITS` | 128 | Zero-knowledge target |
| `FAILURE` | 2^-128 | Largest allowed chance that an honest proof is rejected |
| `MAX_PROOF_BYTES` | 16 KiB | Largest proof |
| `MAX_CLAIMS` | 8 | Most claims per proof |
| `MAX_POINTS` | 4 | Most points in one claim |
| `MAX_WORDS` | 2^28 | Largest committed polynomial, in 64-bit words |
| `CYCLE_LIMIT` | 2^24 | Every verifier run stops before this many cycles |
| `MAX_PROGRAM_BYTES` | 2^20 | Largest verifier program |
| `PROVER_BUDGET` | 250 ms | Median proving time on the official runner with at most 4 threads |
| Stand-in | leanVM `ed9ea362` | The commitment the timed prover must use: leanVM's hiding WHIR, called through an organizer adapter |

## Fields, polynomials and claims

**Fields.** Committed data lives in `K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, encoded as 8 little-endian bytes with bit `i` the coefficient of `x^i`. Points and values live in `E = K[y] / (y^3 + y + 1)`, the field leanVM's commitments open in; `c0 + c1·y + c2·y^2` is encoded as the 24 bytes `c0 ‖ c1 ‖ c2`.

**Polynomials.** A committed polynomial `f` is multilinear in `n` variables, given by its values on `{0,1}^n`. Its **kind** is either bits or words of `K`. The value at `b ∈ {0,1}^n` is table entry `Σ b_i 2^i`, so coordinate 0 is the least significant index bit. A bit polynomial is packed 64 to a word, entry `i` being bit `i mod 64` of word `⌊i / 64⌋`, so it takes `2^(n-6)` words; a word polynomial takes `2^n`. Either must fit in `MAX_WORDS`. A univariate polynomial `g(z) = Σ c_i z^i` can be committed as the multilinear polynomial with the same coefficients, so that `g(z)` is its value at `(z, z^2, z^4, …)`; its table then holds subset sums of the coefficients.

**Claims.** A claim is `(R, n, kind, p_1 … p_k, v_1 … v_k)` with `1 ≤ k ≤ MAX_POINTS`, each point in `E^n` and each value in `E`. It is true when `R` is the root of a polynomial of that size and kind and `f(p_j) = v_j` for every `j`. The network checks all `k` points with one opening proof, which costs about as much as one point, so a claim is priced the same however many points it has. Its **descriptor**, the bytes `PCS_open` receives, is the root (32 bytes), then `n`, the kind (0 for bits, 1 for words) and `k` as one byte each, five zero bytes, the `k · n` coordinates point by point, and the `k` values.

**One claim per root.** A verifier may claim each root at most once, with up to `MAX_POINTS` points in that claim. The opening challenge proves soundness and zero knowledge for one opening per root; a second opening of a hiding WHIR root would leak witness data, and a commitment that binds only to a short list could answer each claim from a different polynomial. The rule covers fixed roots too.

## The ideal model

The Lean proofs treat `PCS_open` as ideal. `COMMIT(f)` returns a fresh random 32-byte root and remembers `f` together with its size and kind, so a root is bound to one polynomial, one `n` and one kind from the moment it is created. A claim is true exactly as defined above. Roots reveal nothing about their polynomials, but claimed values are public, so the PIOP itself must keep them from leaking the witness. The [opening challenge](rules-opening.md) proves the matching properties for a real scheme, and an organizer lemma is meant to combine the two.

## On chain

These are the rules a client implementing `PCS_open` follows. They matter to entrants because they fix what a verifier may rely on.

- **Where claims can be made.** `PCS_open` succeeds only in an EIP-8141 frame of mode `VERIFY` that belongs to the transaction's validation prefix, whatever the call type. Recording a claim changes transaction state inside what is otherwise a static call, so claims are journaled with the approval context, as EIP-8141 has done for `APPROVE` since PR 12458: a claim made inside a call that reverts is discarded. Claims recorded in the validation prefix stand even if the execution body later reverts. `PCS_open`'s gas counts toward the gas the validation prefix may use.
- **Failure.** Any failed `PCS_open` call invalidates the whole transaction, even if the caller catches the failure. A call fails when its descriptor is malformed (the conditions under [system calls](#system-calls)), when it claims a root already claimed in the transaction, or when it runs out of gas.
- **A stable claim list.** Every client must derive the same claims, because they are the block proof's public input. A claim may depend only on the transaction and on contract code, not on storage and not on an EIP-7702 delegation, so fixed roots live in code. A transaction whose revalidation records a different claim list is evicted from the mempool, and under FOCIL an attester enforces a listed transaction only if its recorded claims equal those covered by opening proofs the attester checked.
- **The block's claims.** Each claim enters EIP-8288's sorted, deduplicated dependency list as the triple `(PCS_OPEN_SCHEME, hash(descriptor), R)`.
- **Where the proof travels.** The proof is the byte string of an EIP-8141 `ARBITRARY` signature with an empty message, which the verifier reads with `SIGDATACOPY`. These bytes are outside the signature hash, so the proof can absorb that hash as its `context`. `B` counts them.
- **Opening proofs in transit.** An opening proof that fails its check condemns only that opening proof and the peer that sent it, never the transaction, so a peer cannot block a transaction by forwarding a bad one.

## Fixed polynomials

A verifier may rely on public polynomials, such as a circuit's tables. Each one is a canonical byte file whose SHA-256 hash is listed in the submission, and its Lean definition is derived from those bytes, so the certified table is the one that runs. Setup commits to each one deterministically, without hiding, so anyone can recompute its root. The fixed roots sit at δ<sub>vk</sub>, 32 bytes each, in the order the submission declares. Because the polynomial is public, anyone can produce the opening of a fixed claim; the timed prover produces it in these rules. A claim on a fixed root costs the same as any other claim for now.

## The verifier machine

The verifier is a RISC-V program standing in for the contract. It runs on sig.golf's RV64IM machine ([RISC-V interface](https://github.com/Layr-Labs/sig.golf/blob/main/RULES.md#risc-v-interface)), which already has Lean semantics, with the same memory layout, alignment rules and faults. Ordinary instructions cost 1 cycle and multiplications or divisions 4. Only the inputs and the system calls differ.

**Inputs.** Before the run, memory is zero except for the program's embedded data, `x` at δ<sub>x</sub> and the fixed roots at δ<sub>vk</sub>. Both buffers are 8-byte aligned, do not overlap and end at or below `data_base`. The proof is not in memory: the verifier reads it in order with `READ`. A proof tape whose length is not exactly `B` is rejected.

**Transcript.** Every challenge comes from Fiat-Shamir: it is a hash of everything the verifier has seen so far. The hash `T` is Keccak-256, treated as a random oracle in the proofs. The transcript keeps a 32-byte state `s` and a byte buffer `β`. It starts with `s = T(DOMAIN ‖ x)`, where `DOMAIN` is the ASCII string `pcs_open.golf v0`; this first hash costs 8 cycles per Keccak-f permutation, like `SQUEEZE`. `READ` appends the bytes it reads to `β`. `SQUEEZE` sets `s ← T(s ‖ β)`, empties `β` and returns `s`. `SQUEEZE` is the only source of challenges, so every challenge depends on the public input and on every proof byte read before it.

### System calls

`ECALL` selects a service through `t0`. The numbering keeps sig.golf's `HALT`.

| `t0` | Service | Arguments and effect | Cycles |
| ---: | --- | --- | --- |
| 1 | `HALT` | `a0` = exit code, 0 to accept | 1 |
| 2 | `READ` | `a0` = destination, `a1` = byte count `n`: copy the next `n` proof bytes to memory and append them to `β` | 1 + ⌈n / 8⌉ |
| 3 | `SQUEEZE` | `a0` = destination: write the next 32-byte challenge | 8 per permutation, ⌈(33 + m) / 136⌉ permutations for `m` buffered bytes |
| 4 | `FMUL` | `a0`, `a1` = two `E` elements, `a2` = destination: write their product (`MUL_FIELD`) | 8 |
| 5 | `CLAIM` | `a0` = address of a claim descriptor: call `PCS_open` | 0 toward `C₀`; priced at `CLAIM_CYCLES` in the score |

Every address must be 8-byte aligned and every buffer must fit in memory; `FMUL` reads both inputs before writing its output, so buffers may overlap. `READ` past the end of the proof is a rejection, as is halting with 0 before the whole proof has been read. A `CLAIM` is a fault when its descriptor is malformed: `k` is 0 or above `MAX_POINTS`, the kind is not 0 or 1, the five padding bytes are not zero, the polynomial would exceed `MAX_WORDS`, the root has already been claimed in this run, or the run has already made `MAX_CLAIMS` claims. Any other `t0` is a fault, and a fault rejects.

`FMUL` costs twice a 64-bit multiplication because one product in `E` takes six base-field products; this assumes `MUL_FIELD` is an opcode. A Keccak-f permutation costs what a compression costs in sig.golf. `CLAIM_CYCLES` stands for `PCS_open`'s gas price at about 3 gas per cycle.

## What you must prove

All statements are proved in Lean 4 against the organizer's definitions, for exactly the submitted verifier and numbers, and may depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`. The Fiat-Shamir hash is a random oracle `T`, and every call to it, by anyone, is counted. Keccak also appears inside `R`; the model treats the two uses as independent oracles, which is an assumption rather than something the domain string guarantees.

### Completeness and cost

Run the honest prover on any `(x, w)` with `R(x, w)`, then the verifier on `x` and the proof. The run **succeeds** if the verifier accepts after reading all `B` bytes and every claim it made is true.

1. **Completeness:** the run succeeds with probability at least `1 - FAILURE`, over `T` and the prover's randomness.
2. **Cost:** whenever the run succeeds, the verifier made exactly `N` claims, each on a different root, and spent at most `C₀` cycles outside its `CLAIM` calls.

### Knowledge soundness

Nobody can produce an accepted proof without knowing a valid witness. An adversary `A` has unlimited computation and a budget of `Q ≥ 1` calls to `T` and `COMMIT` together. It picks a public input `x` and a proof. It **wins** if the verifier accepts, every claim is true, and the submission's **extractor** fails. The extractor is a Lean function that reads the polynomials `A` committed (the ideal model remembers them) and must return a witness `w'` with `R(x, w')`.

**Requirement:** for every `A` and `Q`, `Pr[A wins] ≤ Q / 2^(SECURITY_BITS + LIST_BITS × M)`, where `M` is the number of roots the verifier claims on that come from the proof rather than from the fixed roots.

The margin pays for the gap between the ideal model and a real commitment. The ideal model binds a root to one polynomial, but leanVM's WHIR binds it only to a list of up to 2^12, so every challenge drawn after a root is published loses up to 12 bits for that root. Proving `128 + 12·M` bits in the ideal model keeps 128 with the real scheme, before the opening's own error, which the organizer's composition lemma adds.

Challenges must come from `SQUEEZE`. A design that computes Fiat-Shamir inside its own circuit, for example to verify an inner proof, cannot meet this statement, because the model cannot treat a hash computed inside a circuit as an oracle.

### Zero knowledge

The proof and its claims reveal nothing about the witness. The submission defines a **simulator** in Lean that sees only `x`, may create roots, and may choose `T`'s answers on inputs nobody has queried yet. A distinguisher picks statements with valid witnesses, receives either honest proofs and claims or simulated ones, and makes at most `Q` oracle calls.

**Requirement:** its advantage is at most `Q / 2^ZK_BITS`.

### Termination and admission

**Termination:** for every public input, proof, oracle and set of committed polynomials, the verifier halts in fewer than `CYCLE_LIMIT` cycles.

**Admission:** the program fits in `MAX_PROGRAM_BYTES`, `B ≤ MAX_PROOF_BYTES`, `N ≤ MAX_CLAIMS`, every claim respects `MAX_POINTS` and `MAX_WORDS`, and the input buffers follow the layout rules above.

## Prover budget

Proving time is measured on real hardware, following the [Flock BLAKE3 benchmark](https://github.com/Layr-Labs/flock-challenge):

- **Runner.** One official machine, named with the parameter set. Threads are limited to 4 by the operating system, not by the prover.
- **Commitments.** The native prover makes every commitment and opening through the stand-in, a library the harness owns behind a fixed interface; its time counts. The prover returns the proof and an **opening bundle**, the opening proofs that would travel in the mempool, which the harness checks against the claims; the bundle is not scored.
- **Offline phase.** Work that does not depend on the instance, such as building fixed tables, may run once before timing. Its time and memory are reported.
- **Trials.** Each trial starts a fresh sandboxed worker and writes it a fresh instance `(x, w)` drawn from a private seed, plus a seed for the prover's coins. The clock runs from writing the instance to capturing the proof and bundle. One untimed warm-up proof on a fixed seed is followed by 25 measured trials.
- **Pass.** Every proof is accepted with true claims, the median time is at most `PROVER_BUDGET`, and no trial takes more than twice it. On some trials the harness proves the same instance with a second coin seed and rejects identical proofs, so a prover cannot skip its blinding.

## Known limitations

- **Ideal commitments.** These proofs treat `PCS_open` as ideal; the opening challenge proves the real scheme, and the lemma that combines the two is not written yet.
- **Bits in the stand-in.** A bit claim's opening in leanVM sends 64 bit-slice values that reveal linear functions of the bits, and leanVM's opening is zero knowledge only inside its own outer proof. Until a standalone opening hides them, the stand-in does not give the ideal model's hiding for bit claims (see open questions in [the design notes](design.md)).
- **Cycles, not gas.** `C₀` counts RISC-V cycles. A contract performs the same reads, hashes and multiplications, but its exact gas comes only from an EVM port.
- **Claim price.** `CLAIM_CYCLES` is an estimate. Each claim also puts an opening proof of roughly 150 KB into the mempool until it is aggregated, which the score does not count.
- **Non-malleability.** The transcript binds each proof to its context, but the soundness game gives the adversary no honest proofs to start from, so simulation extractability is not proven.
- **Prover implementation.** Completeness and zero knowledge are proven for the Lean prover. The timed native prover is checked only through its accepted proofs and the second-seed test, so reviewers compare it with the Lean one.
- **Statement size.** 34 Keccak-f permutations, about two thirds of a two-input MSP spend.

