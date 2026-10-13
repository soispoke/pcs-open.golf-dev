# PCS_open golf: opening challenge rules

## TL;DR

Design the polynomial commitment behind `PCS_open`: how a wallet commits to its data with a 32-byte root, and how it proves a claim about that data cheaply enough for every node and aggregator to check. The score is opening proof bytes times verification cycles, measured on a 2^20-word polynomial opened at two points, and committing plus opening must stay within twice the reference's time. Entries prove in Lean that openings are complete, sound for every root an adversary publishes, and zero knowledge. The commitment format is frozen into Ethereum when `PCS_open` launches, so this challenge matters most before launch. It is a draft modeled on [sig.golf](https://github.com/Layr-Labs/sig.golf/blob/main/RULES.md): the Lean contract and the verifier exist and have passed a dry run, but no entry has been verified yet.

## The idea

A wallet commits to its data as a polynomial and puts a 32-byte root in its transaction. The application's contract then makes a **claim**: "the polynomial behind this root has value `v` at point `p`". The wallet backs the claim with an **opening proof**, which travels beside the transaction in the mempool. The nodes that receive it check it directly, and an aggregator checks it again inside a recursive proof, as EIP-8288 does for whole proofs. From then on nodes pass on the aggregate instead, and later proofs, up to the block's, check only aggregates.

So a claim costs the network the opening proof's bytes, which travel only until an aggregate covers them, and the work of checking it once at each node that receives it and once in the aggregator. That work sets the claim's price in the [app challenge](rules-app.md). Today the opening is leanVM's hiding WHIR, at roughly 150 KB and 20,000 gas per claim. Entrants design a scheme, both how it commits and how it opens, that does better. The opening can be replaced by later forks; the commitment format cannot.

## Claims

The definitions are the app challenge's ([Fields, polynomials and claims](rules-app.md#fields-polynomials-and-claims)): data in `K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, points and values in `E = K[y] / (y^3 + y + 1)`, multilinear polynomials whose values are bits or words of `K`, the same table layout and bit packing, and the same claim descriptor `(R, n, kind, k, points, values)` with `1 ≤ k ≤ MAX_POINTS`.

A root must bind its polynomial's size `n` and kind as well as its values: an opening for a descriptor whose `n` or kind differs from the committed ones must fail. How the scheme packs, encodes and hashes data into the root is the entrant's choice, but the root is exactly 32 bytes, and anything else the verifier needs, such as an out-of-domain answer, goes in the opening proof. A scheme may pad a small polynomial up to its own minimum size. The scored instance is a bit claim, because applications that compute Keccak work on bits, but word claims must be supported too.

## What you submit

1. **Commit and open**: Lean definitions, used in the proofs, and a native implementation, which the harness times (see [prover budget](#prover-budget)).
2. **A verifier**: a RISC-V program that checks an opening proof against a claim (see [the verifier machine](#the-verifier-machine)).
3. Three numbers: `S`, the largest honest opening proof in bytes on the scored instance; `C`, the most cycles the verifier spends on an honest opening of it; and `L`, the list size in bits for which [evaluation soundness](#evaluation-soundness) is proven.
4. Two memory offsets, δ<sub>claim</sub> and δ<sub>proof</sub>, where the verifier finds its inputs.
5. **Lean proofs** of the [required statements](#what-you-must-prove) for exactly these programs and numbers.

## Score

```text
score = S × C
```

Both numbers are taken on the scored instance: a hiding commitment to a bit polynomial of `2^26` bits (`2^20` words), opened at two points. Two points is the common case, because most PIOPs read their commitment at a challenge and at the next row. Lower is better, and ties go to the earlier submission. Commit-plus-open time is a pass or fail test, not part of the score.

## Parameters

| Constant | Value | Meaning |
| --- | ---: | --- |
| `SCORED_WORDS` | 2^20 | Size of the scored polynomial in 64-bit words (2^26 bits) |
| `POINTS` | 2 | Points in the scored claim |
| `MAX_WORDS` | 2^28 | Every size up to this must be supported |
| `MAX_POINTS` | 4 | Every point count up to this must be supported |
| `SECURITY_BITS` | 128 | Soundness target |
| `MAX_LIST_BITS` | 12 | Largest list a root may bind to, in bits (see [evaluation soundness](#evaluation-soundness)) |
| `ZK_BITS` | 128 | Zero-knowledge target |
| `FAILURE` | 2^-128 | Largest allowed chance that an honest opening is rejected |
| `MAX_OPENING_BYTES` | 1 MiB | Largest opening proof |
| `CYCLE_LIMIT` | 2^28 | Every verifier run stops before this many cycles |
| `MAX_PROGRAM_BYTES` | 2^20 | Largest verifier program |
| `PROVER_BUDGET` | 2 × reference | Median commit-plus-open time against the [reference](#reference-entry), with at most 4 threads on the same runner |

## The verifier machine

The verifier runs on sig.golf's RV64IM machine ([RISC-V interface](https://github.com/Layr-Labs/sig.golf/blob/main/RULES.md#risc-v-interface)) with its memory layout, alignment rules, faults and costs: ordinary instructions 1 cycle, multiplications and divisions 4.

**Inputs.** Before the run, memory is zero except for embedded data, the claim descriptor at δ<sub>claim</sub> (whose first 32 bytes are the root) and the opening proof at δ<sub>proof</sub>, in a `MAX_OPENING_BYTES` buffer that is zero after the proof. Both buffers are 8-byte aligned and do not overlap. As in sig.golf, the verifier pays `⌈S / 256⌉` cycles for receiving the proof, and this charge counts toward `C`.

**System calls.** `ECALL` selects a service through `t0`:

| `t0` | Service | Arguments and effect | Cycles |
| ---: | --- | --- | --- |
| 0 | `HASH` | `H` on `a1` bytes at `a0`, the 32-byte answer written at `a2`, exactly as in sig.golf | 8 per compression |
| 1 | `HALT` | `a0` = exit code, 0 to accept | 1 |
| 2 | `FMUL` | multiply the `E` elements at `a0` and `a1`, write the product at `a2` | 8 |

`HASH`'s argument rules are sig.golf's. `FMUL`'s addresses must be 8-byte aligned and its buffers fit in memory; it reads both inputs before writing. Any other `t0` is a fault. In the proofs `H` is sig.golf's random oracle on inputs of 64·k bytes; natively it is unkeyed BLAKE2s-256 of the whole input, one compression per 64-byte block.

**Transcript.** There is no transcript service: Fiat-Shamir is the entrant's own code built on `HASH`. It must start from the whole claim descriptor (root, size, kind, number of points, points and values), which is the opening's only link to the application, whose transcript is separate. Merkle hashing, Fiat-Shamir and any grinding all use `H`, so every hash anyone computes counts toward the adversary's budget `Q`.

## What you must prove

All statements are proved in Lean 4 against the organizer's definitions, for both kinds, every size up to `MAX_WORDS` and every point count up to `MAX_POINTS`, and may depend only on `propext`, `Classical.choice` and `Quot.sound`.

### Completeness and cost

1. **Completeness:** for every polynomial and every set of points, committing and then opening honestly gives the true values, and the verifier accepts with probability at least `1 - FAILURE` over `H` and the prover's randomness.
2. **Cost:** for every bit polynomial of the scored size, every pair of points, every oracle and every choice of the prover's randomness, the honest opening is at most `S` bytes and the verifier spends at most `C` cycles, including the `⌈S / 256⌉` receiving charge.

### Evaluation soundness

Once a root is published, nobody can make the verifier accept a false claim about it. An adversary `A` has unlimited computation and a budget of `Q ≥ 1` calls to `H`. It publishes roots one at a time, adaptively. Each time it publishes a root, the submission's **extractor**, a Lean function that reads `A`'s calls to `H` so far, outputs a list of at most `2^L` polynomials for that root, with `L ≤ MAX_LIST_BITS`. For a root computed by honest commitment, including setup's deterministic roots for public polynomials, the list must be exactly that polynomial. `A` then makes claims on its roots, each with points and values that may depend on the lists, and opening proofs for them. It **wins** if the verifier accepts some claim whose values match no polynomial in that root's list.

**Requirement:** for every `A` and `Q`, `Pr[A wins] ≤ Q / 2^SECURITY_BITS`.

The list exists because a code decoded beyond half its minimum distance pins a root only to a short list of polynomials; leanVM's WHIR binds to up to 2^12. A scheme that binds to exactly one polynomial proves the statement with `L = 0`. The app challenge charges every application root `MAX_LIST_BITS` of extra soundness whatever the record's `L`, so a smaller list makes applications safer than required but is not scored.

### Zero knowledge

The opening proof is public in the mempool, so it must reveal nothing about the polynomial beyond the claimed values. The submission defines a **simulator** in Lean that sees only the size, kind, number of points, points and values, and may set `H`'s answers on inputs nobody has queried yet. For any polynomial and points, a distinguisher making at most `Q` calls to `H` must not tell the honest root and opening from the simulated ones with advantage above `Q / 2^ZK_BITS`. The statement covers one opening per root, with up to `MAX_POINTS` points, which is all the app challenge allows.

### Termination and admission

**Termination:** for every input, the verifier halts in fewer than `CYCLE_LIMIT` cycles, and for every descriptor of an admitted size and kind and every opening proof, honest or not, in at most `4 × C` cycles, so a node cannot be made to spend much more on a bad opening than on a good one.

**Admission:** the program fits in `MAX_PROGRAM_BYTES`, `L ≤ MAX_LIST_BITS`, and the honest opening of every supported size, kind and point count fits in `MAX_OPENING_BYTES`.

## Prover budget

The wallet commits and opens, so a cheaper claim must not cost the wallet much more time. The protocol is the app challenge's ([Prover budget](rules-app.md#prover-budget)): an official runner, at most 4 threads enforced by the operating system, a fresh sandboxed worker per trial, one untimed warm-up, and 25 measured trials on fresh random polynomials and points of the scored size. Commit and open are timed as two phases and reported separately. Every opening must be accepted, the median of commit plus open must be at most twice the reference's median on the same runner image, and no trial may take more than twice that limit. The reference is measured once per runner image.

## Reference entry

The reference is leanVM's hiding WHIR at rate 1/4 with ring switching for bit claims, from its zero-knowledge branch (PR 624 at `ed9ea362`). The scored instance needs leanVM's 2^21-word stack, since a hiding stack holds at most 60 data lanes. From its configuration, an opening checks 112, 45, 28 and 20 queries across four levels: about 3,200 to 3,600 BLAKE2s compressions and 16,000 to 21,000 field multiplications, so `C` is roughly 155,000 to 200,000 cycles and the opening about 130 to 155 KB plus the bit slices, varying with Merkle path pruning. These are estimates from the configuration. Porting it is a new verifier, since leanVM's transcript is a BLAKE2s duplex rather than this machine's `HASH`.

The reference is not a valid entry. It has no Lean proofs of these statements, its hiding bound is about 2^-120 rather than `ZK_BITS`, and its opening is zero knowledge only inside leanVM's own outer proof: on its own it sends the 64 ring-switching slices of a bit claim and sums from before the lane fold, which reveal linear functions of the bits. A standalone version would need its own key commitment and about 12 more bits of grinding, roughly doubling its cost by one estimate. The reference sets the prover budget and a score to beat.

The interim app price, 20,000 gas per claim, scales EIP-8288's price for a leanSPHINCS verification by the reference's compression count; scaling instead from EIP-8288's 30,000-gas price for a whole STARK gives 12,500 to 21,500 gas.

## How the record feeds the app challenge

The app challenge treats `PCS_open` as ideal and charges each claim the published `CLAIM_CYCLES` plus `MAX_LIST_BITS` of extra soundness per root. Organizers update the app challenge's parameter set only on announced dates: the claim price follows the current record's verification cost, and the record's implementation becomes the stand-in that app provers are timed with. Before it does, a record must pass a grid of sizes, both kinds and every point count, not just the scored instance. Because app certificates never include the price and always use the maximum list margin, a new record re-ranks app entries without new proofs. An organizer lemma should show that the app challenge's ideal-model statements and this challenge's statements together give the real ones, so neither group of entrants proves the combination.

## Known limitations

- **Cycles as a proxy.** `C` stands for two real costs: the check at each node that receives the opening, and the same check inside an aggregator's leanVM recursion. Here a field multiplication costs as much as a hash compression, but in leanVM's recursion a compression costs far more than a product, so a record that saves field work lowers the price more than it lowers the aggregator's real work (see open questions in [the design notes](design.md)).
- **Bytes in the mempool.** `S` counts what the wallet sends before an aggregate replaces the opening. The opening never reaches a block, but the score still values a smaller one because it lowers mempool bandwidth.
- **One opening per root.** Zero knowledge is required for a single opening of each root, which is all the app challenge allows.
- **Scored size.** Only 2^20 words are scored. A scheme that is better at other sizes gains nothing here, although every size must be supported, proven and bounded by the termination rule.

