# PCS_open golf: design notes

## TL;DR

PCS_open golf is a pair of sig.golf-style challenges that test whether two small additions to Ethereum, `PCS_open` and `MUL_FIELD`, let private applications verify post-quantum proofs as cheaply as Groth16 does today. Checking such a proof splits into two jobs. The application's contract checks the proof's logic and ends with a few claims about committed data, and Ethereum checks those claims through opening proofs aggregated in the mempool. The [app challenge](rules-app.md) makes the first job small, with the smallest proof of a Keccak Merkle withdrawal. The [opening challenge](rules-opening.md) makes the second job cheap, with the best commitment scheme for one claim. Both require Lean proofs of completeness, soundness and zero knowledge. The pipeline has passed a private dry run, but no existing design meets either bar yet, so there are no entries.

## Why these challenges

Private applications use Groth16 proofs, which a quantum computer could break. The replacement should not make transactions larger, costlier or slower to prove: today a shielded-pool transfer carries a 288-byte proof that costs about 215,000 gas to verify and about a second to prove.

EIP-8288 would have Ethereum verify each application's whole proof as a declared dependency, at 30,000 gas and 96 transaction bytes each, against a backend's verification key or a program run by a VM that Ethereum enshrines. Agreeing on that VM is the slow part. `PCS_open` is meant to ship faster: Ethereum checks only polynomial openings and adds `MUL_FIELD` for field arithmetic, and each application runs the rest of its proof, its PIOP, in its own contract. No VM and no PIOP is enshrined.

A private transaction's verification then costs two things:

1. **The application's own check:** the proof's bytes in the transaction and the contract's computation. The contract creates its claims by calling `PCS_open`, so claims add no bytes.
2. **Ethereum's check of each claim:** an opening proof that travels with the transaction until an aggregate covers it. With leanVM's hiding WHIR this is roughly 150 KB of mempool data and 20,000 gas per claim, both estimates: about 3,600 BLAKE2s compressions to verify one opening, priced at EIP-8288's rate for a leanSPHINCS dependency.

The second part is the largest single cost, so both need work, by different people: the first by each application, the second by the protocol, once for everyone.

## The two challenges

| | App challenge | Opening challenge |
| --- | --- | --- |
| Entrants design | A PIOP and its contract verifier | A polynomial commitment scheme (commit and open) |
| Fixed | The withdrawal statement and an ideal `PCS_open` | The claim format, 32-byte roots and the fields |
| Score | Proof bytes × (cycles outside claims + claims × published price) | Opening bytes × verification cycles, for 2^26 bits at two points |
| Prover limit | 250 ms median on four threads | Commit plus open within twice leanVM's WHIR |
| Lean proofs | Completeness, knowledge soundness at `Q / 2^(128 + 12 × roots)`, zero knowledge | Completeness, soundness for every published root with lists of at most 2^12, zero knowledge for one opening per root |
| Rules | [the app rules](rules-app.md) | [the opening rules](rules-opening.md) |

They connect in one direction. The app challenge treats `PCS_open` as ideal, charges each claim a published price and adds 12 bits of soundness margin per root. Organizers update the price, and the commitment the app prover is timed with, from the opening challenge's record, but only on announced dates and as one numbered parameter set. App certificates never include the price and always use the full 12-bit margin, so a new opening record re-ranks app entries without new proofs.

## What they should tell us

1. **Are two primitives enough?** With Keccak, yes on the protocol side: `KECCAK256` serves Fiat-Shamir and the pool's tree, and `MUL_FIELD` supplies the field multiplications the EVM lacks.
2. **How small can the application's proof get?** By bytes, six shielded-pool transfers fit in an 8 KiB inclusion list today, and keeping six needs a proof under about 375 bytes. By FOCIL's candidate 2^20 validation-gas budget, Groth16 fits four, and six would need at most about 175,000 declared gas per transfer. Our gas model finds no Keccak design under 375 bytes that also proves fast.
3. **How cheap can a claim get?** This sets how many claims an application can afford, and the commitment format must be chosen before launch, because it is frozen for good while the opening can be replaced by later forks.

An earlier comparison of proof interfaces preferred program claims under EIP-8288 as the first scheme, under a different goal: that immutable applications never migrate when the proving backend changes. It has not been reconciled with the goal behind these challenges, shipping fastest.

## Decided

- **Scores:** proof bytes times verification cycles in both challenges, as in sig.golf, with proving time as a pass or fail limit. Gas follows from these numbers and is reported beside each record, not scored. An earlier gas score, at 30,000 gas per claim, let a proof grow by up to 1,875 bytes to save one claim.
- **Claims through `PCS_open`:** the contract creates claims by calling `PCS_open` in the validation prefix, so they add no transaction bytes; declaring them as EIP-8288 dependency entries would cost 96 bytes each. The app rules spell out the consensus rules this needs: where the call may happen, that a failed call invalidates the transaction, that claims depend only on the transaction and contract code, and how claims enter the block's dependency list.
- **One claim per root:** a verifier claims each root at most once, with up to four points, matching the opening challenge's single opening per root.
- **Claim price outside certificates:** the app score is `B × (C₀ + N × CLAIM_CYCLES)`. Certificates prove `B`, `N` and `C₀`, and organizers publish the price.
- **A fixed list margin:** applications prove 12 extra bits of soundness for every root taken from the proof, the opening challenge's maximum list size, so no opening record can invalidate an app certificate.
- **Hash:** Keccak-256 for the application's statement.
- **Fields:** `GF(2^64)` for data and `GF(2^192)` for points and values, as in leanVM. A 128-bit track was dropped: a quotient check over a Keccak-size circuit would need over 30 bits of grinding, sumcheck designs stay above about 640 bytes in either field, and it would have needed WHIR over `GF(2^128)` with new parameters.
- **Launch:** a private dry run passed on 2026-10-13 (eight fixtures with known verdicts, see `tools/dry_run.py`). The repositories are public as a draft, with no entries.

## Still open

1. **Gates beside the score.** The product can rank a 500-byte entry with one claim above a 250-byte entry with three, although the second fits more transfers per list. Options: a size gate (for example at 375 bytes), a validation-gas gate, or reporting only.
2. **The opening machine's prices.** It charges a field multiplication like a hash compression, while in leanVM's recursion a compression costs far more. Options: recursion-weighted prices (for example 32 cycles per compression and 1 per multiplication), or scoring the verifier's committed words directly.
3. **Hiding bit claims.** leanVM's opening reveals a bit claim's 64 slices outside its own outer proof. A standalone opening needs a key commitment or a key region reserved in the frozen commitment format, and until one exists the app challenge must either reveal the slices to its zero-knowledge distinguisher or allow only word claims.
4. **Caps on claims.** `MAX_CLAIMS = 8` allows more mempool evidence per transaction than EIP-8288's 512 KB limit (about three claims), so either shrink it or size the protocol's per-transaction caps to admit it.
5. **`MUL_FIELD` as an opcode or a precompile.** `FMUL`'s price of 8 cycles assumes an opcode; a precompile call costs at least 100 gas, about 40 cycles.
6. **The opening prover limit.** Twice the reference is a judgment call; a tighter bound tied to the app challenge's 250 ms would keep a slower record from pushing app entries over their limit.
7. **Statement size.** A depth-32 membership proof plus a nullifier (34 Keccak-f permutations), rather than a full two-input spend (about 50), keeps the Lean relation small.
8. **Wallet calibration.** 250 ms on four threads should match about a second on a phone, which needs a phone run to confirm.
9. **The verifier machine.** Both challenges use sig.golf's RISC-V machine because its Lean semantics exist. EVM bytecode would give exact gas, but only tested against a Lean reference, since no tooling yet proves a contract against a specification.
10. **Fiat-Shamir inside a circuit.** Excluded, because the Lean model cannot treat a hash computed in a circuit as an oracle. Designs like Flock plus a small wrapper need it; a relaxed track could allow it as an explicit assumption.
11. **Cheaper claims on fixed roots.** Anyone can open a public polynomial, and a block can open all of its claims on one together, so these claims could cost far less than the rules charge.
12. **The `PCS_open` interface.** The claim price, claims on bits and several points per claim are our design answers, not yet confirmed by the proposal's author.

## Remaining work

- **Lean:** the lemma that combines the two challenges' statements into the real ones, and a shared lemma deriving Fiat-Shamir statements from round-by-round soundness with grinding, so entrants need not. The Lean contract has not yet been reviewed line by line against the rules.
- **Native tooling:** an emulator differential-tested against the Lean machine, the stand-in adapter around leanVM `ed9ea362`, field implementations, the timing harness for the prover limits, and a submission policy for data files and native sources.
- **Reference entries:** none passes either bar. For the app challenge, a no-round PIOP with Lean proofs of completeness, knowledge soundness and zero knowledge exists but assumes an algebraic hash and needs its zero-knowledge lemma restated for data in `K` and challenges in `E`, and Flock's sumcheck PIOP has no Lean proofs. For the opening challenge, leanVM's hiding WHIR must be ported and measured, and it is not a standalone zero-knowledge opening.
- **Calibration:** a phone run for the wallet limit, and an EVM port of an app entry to report real gas.

## History

A six-role review of the rule drafts on 2026-10-13 found two blockers, both closed by the decisions above (one claim per root, and the price outside certificates). Its clarifications and most of its significant issues are fixed in the rules, and the issues that need a decision are the open questions above.
