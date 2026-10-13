# pcs-open.golf: submission rules

pcs-open.golf is a Lean-kernel-verified competition with two tracks. The **app** track asks for the smallest withdrawal proof that an Ethereum contract can check with two new primitives, `MUL_FIELD` and `PCS_open`. The **opening** track asks for the cheapest polynomial commitment scheme behind one `PCS_open` claim. [docs/rules-app.md](docs/rules-app.md) and [docs/rules-opening.md](docs/rules-opening.md) explain the rules for reading; this file is the precise specification of what a submission is and how it is checked. [docs/design.md](docs/design.md) explains why the challenge exists and what is still open.

This is a draft. The contract is `pcs-open-v1-draft`; the pipeline passed a private dry run on 2026-10-13, and no entry has been verified yet.

## Layout

```
formal/                              the Lean project (lake root)
  PcsOpenGolf/Parameters.lean        constants, byte types, polynomial kinds
  PcsOpenGolf/Field.lean             K = GF(2^64) and E = K[y]/(y^3 + y + 1)
  PcsOpenGolf/Keccak.lean            Keccak-f[1600] and Keccak-256
  PcsOpenGolf/Relation.lean          the withdrawal relation R
  PcsOpenGolf/Polynomial.lean        multilinear evaluation and claim truth
  PcsOpenGolf/Oracle.lean            the transcript oracle T and the ideal COMMIT oracle
  PcsOpenGolf/Rv64.lean              RV64IM decoding and execution, adapted from sig.golf
  PcsOpenGolf/Machine.lean           the app verifier machine and its system calls
  PcsOpenGolf/Submission.lean        what an app entry consists of
  PcsOpenGolf/Security.lean          the app completeness, soundness and zero-knowledge games
  PcsOpenGolf/Statements.lean        the app statements and Certificate
  PcsOpenGolf/Opening/*.lean         the same for the opening track
  PcsOpenGolf/Challenge/*.lean.in    challenge stubs, rendered with the claimed numbers
  Submissions/<Root>/                a submission root; lives in the submissions repository
  scripts/check-axioms.lean          audit: the contract uses only the three standard axioms
verifier/                            policy checks, contract pin, comparator configs, verify.py
challenges.json                      tracks, claim fields, limits, protected files
scoring.json                         the published claim price (not part of the pinned contract)
```

Protected files are listed in `challenges.json` and pinned in `verifier/protected.sha256`. The verifier lays a submission root over a copy of the trusted tree, so every protected file comes from the contract. The core repository holds no proofs; reference entries are ordinary submissions.

## Tracks

| Track | Root | Solution module | Claim fields | Score |
|---|---|---|---|---|
| `app` | `formal/Submissions/App/` | `Submissions.App.Solution` | `B`, `N`, `C0`, `M` | `B × (C0 + N × CLAIM_CYCLES)` |
| `opening` | `formal/Submissions/Opening/` | `Submissions.Opening.Solution` | `S`, `C`, `L` | `S × C` |

Lower is better in both tracks. `CLAIM_CYCLES` comes from the parameter set in force in `scoring.json`, so certificates prove `B`, `N`, `C0` and `M` but never the price, and a price change re-ranks entries without new proofs.

## What a submission exports

`Solution.lean` is the module the verifier exports from. It must declare, in the track's namespace, the two names of the rendered stub with exactly the stub's types:

```lean
import PcsOpenGolf.Statements

namespace PcsOpenGolf.Challenge.App

noncomputable def submission : PcsOpenGolf.Submission := ...

theorem certificate : PcsOpenGolf.Certificate submission
    { proofBytes := 408, claims := 5, cycles := 1425, proofRoots := 1 } := ...

end PcsOpenGolf.Challenge.App
```

The numbers in `certificate` are the ones in `claim.json`; the verifier renders `formal/PcsOpenGolf/Challenge/App.lean.in` with them and comparator checks that the solution proves that exact statement. The opening track is the same with `import PcsOpenGolf.Opening.Statements`, namespace `PcsOpenGolf.Challenge.Opening`, `submission : PcsOpenGolf.Opening.Scheme` and `certificate : PcsOpenGolf.Opening.Certificate submission { openingBytes := S, cycles := C, listBits := L }`.

`submission` is a definition hole: comparator checks its name and type and the axioms it uses, not that it is a sensible entry. As comparator's documentation requires for definition holes, the organizers read every record's `submission` before publishing it. The certificate's admission, cost and termination statements tie the declared numbers to the definition, but a human still checks that the image, prover, extractor and simulator are what the notes say.

## Rules for the submission root

1. **Flat.** One directory containing only identifier-named `.lean` files, `claim.json`, and optional `NOTES.md` and `README.md`. `Solution.lean` is required.
2. **Claim.** `claim.json` is a JSON object, at most 512 bytes, with exactly the track's claim fields as keys. Each value is a nonnegative decimal integer within the bounds `challenges.json` gives:

   | Track | Field | Meaning | Bounds |
   |---|---|---|---|
   | `app` | `B` | proof bytes | 1 to 16,384 |
   | `app` | `N` | claims per proof | 0 to 8 |
   | `app` | `C0` | verifier cycles outside claims | 0 to 2^24 − 1 |
   | `app` | `M` | claims on proof roots | 0 to 8 |
   | `opening` | `S` | opening bytes on the scored instance | 1 to 2^20 |
   | `opening` | `C` | verifier cycles on the scored instance | 1 to 2^26 − 1 |
   | `opening` | `L` | list size in bits | 0 to 12 |

   The opening bound on `C` keeps the termination statement's `4 × C` below the machine's cycle limit of 2^28.
3. **Source-header imports.** In every submitted `.lean` file, use one ordinary `import Module.Name` per line, with dot-separated, unquoted ASCII identifiers. `module`, `prelude` and modified imports are not admitted. Header imports may name `Mathlib` and `VCVio` modules, the track's contract modules (exact names, never prefixes), and sibling files of the same root as `Submissions.<Root>.<File>`:

   | Root | Contract modules |
   |---|---|
   | `App` | `PcsOpenGolf.{Parameters, Field, Keccak, Relation, Polynomial, Oracle, Rv64, Machine, Submission, Security, Statements}` |
   | `Opening` | `PcsOpenGolf.{Parameters, Field, Keccak, Polynomial, Rv64}` and `PcsOpenGolf.Opening.{Oracle, Machine, Scheme, Security, Statements}` |

   This restricts explicit header imports only. Dependencies of permitted modules are available transitively. Exported declarations must still pass comparator's statement comparison, axiom checks and kernel replay.
4. **Axioms.** Exported declarations may depend only on `propext`, `Quot.sound` and `Classical.choice`. `sorry` and `native_decide` (which adds `Lean.ofReduceBool`) are refused.
5. **Limits.** 200 files, 8 MiB per file, 16 MiB per root. Verification gets 20 minutes of wall clock, 24 GiB of memory and 4 MiB of combined output, beyond which output is truncated and may cause rejection.
6. **Toolchain.** Exactly `formal/lean-toolchain` (Lean v4.33.1) and `formal/lake-manifest.json`, both protected.

## What is not checked automatically yet

- **Prover budget.** The rules give each track a wallet time limit, measured by timing the native prover. That harness is not built; until it is, the organizers time a record's prover by hand under the protocol in the rules.
- **Price.** `scoring.json` is published by the organizers on announced dates. It is outside the pin on purpose.
- **The meaning of `submission`.** See the definition-hole note above.

## Check locally

From this repository, with a submissions checkout next to it:

```sh
verifier/setup_tools.sh                                                  # once: comparator, lean4export
(cd formal && lake exe cache get && lake build && lake env lean scripts/check-axioms.lean)   # Mathlib cache, contract, audit
python3 verifier/check_submission.py app --root ../pcs-open.golf-submissions   # policy only
python3 verifier/verify.py app --source ../pcs-open.golf-submissions          # the full pipeline
```

Replace `app` by `opening` for the other track. `verify.py` copies the trusted tree, lays the track's root from `--source` over it, checks the pin and the policy, attaches a fresh clone of the warm `.lake` without this track's build products, renders the stub with `claim.json`, and runs comparator under the contract's limits. It reports `verified`, `rejected`, `policy_rejected`, `timeout` or `failed`. On macOS comparator runs with its fake landrun shim, which is not a sandbox: that is fine for trusted local development only. Linux runs fail closed unless systemd, Landlock ABI 3 and isolated work storage are present (`verifier/linux_storage.py`).

`python3 tools/check_repo.py --formal --official --submissions ../pcs-open.golf-submissions` runs every check above, the verifier's unit tests and the Lean regression tests in one go.

## Submitting

There is no hosted verifier yet. An entry is a pull request to [pcs-open.golf-submissions](https://github.com/soispoke/pcs-open.golf-submissions) that creates or changes one track's root and nothing else. Check it locally with `verify.py` first; the organizers run the same pipeline on the pull request's head commit, read the `submission` definition by hand, and report the verdict on the pull request.

## Maintaining the contract

After editing any protected file, re-pin and re-audit:

```sh
python3 verifier/pin_contract.py pin
(cd formal && lake exe cache get && lake build && lake env lean scripts/check-axioms.lean && lake env lean PcsOpenGolfTests.lean)
python3 -m unittest discover -s verifier/tests
```

`pin_contract.py id` prints the contract id, the hash of the pin file, which together with the version name identifies exactly which statements a score refers to.
