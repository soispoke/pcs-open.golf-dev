# pcs-open.golf

Can two small additions to Ethereum, `PCS_open` and `MUL_FIELD`, let private applications verify post-quantum proofs as cheaply as Groth16 today?

pcs-open.golf is a draft competition in the style of [sig.golf](https://github.com/Layr-Labs/sig.golf) and ots.golf, where every entry is a Lean proof about a pinned contract. Checking a proof under `PCS_open` splits into two jobs, and each has a track:

| Track | Entrants build | Score | Rules |
|---|---|---|---|
| `app` | the smallest withdrawal proof (a 32-level Keccak Merkle path and a nullifier) that a contract checks while making claims about committed polynomials | proof bytes × (verifier cycles outside claims + claims × `CLAIM_CYCLES`) | [docs/rules-app.md](docs/rules-app.md) |
| `opening` | the cheapest commitment scheme behind one claim, commit and open | opening bytes × cycles to verify it | [docs/rules-opening.md](docs/rules-opening.md) |

The opening record sets the claim price the app track charges, so the two scores together give the cost of a private transaction. [docs/design.md](docs/design.md) explains why and lists what is still open. [AGENTS.md](AGENTS.md) is the precise specification of a submission.

This repository, **pcs-open.golf-dev**, is the core: the Lean contract and the verifier. It holds no proofs; entries are roots `formal/Submissions/<Root>/` in [pcs-open.golf-submissions](https://github.com/soispoke/pcs-open.golf-submissions). The pipeline has passed a private dry run (`tools/dry_run.py`), but no design has the Lean proofs a certificate needs yet, so there are no entries.

## Quick start

```sh
verifier/setup_tools.sh
(cd formal && lake build && lake env lean scripts/check-axioms.lean && lake env lean PcsOpenGolfTests.lean)
python3 verifier/verify.py app --source ../pcs-open.golf-submissions
```

`verify.py` takes only the track's root from `--source`; the contract and tooling come from this checkout. On macOS comparator runs unsandboxed, for trusted local development only.

## Repository map

| Path | Contents |
|---|---|
| [`AGENTS.md`](AGENTS.md) | submission specification |
| [`challenges.json`](challenges.json) | tracks, claim fields, limits, protected files |
| [`scoring.json`](scoring.json) | the published claim price, outside the pin |
| [`formal/PcsOpenGolf/`](formal/PcsOpenGolf/) | the contract for both tracks, and the challenge stubs in `Challenge/` |
| [`formal/PcsOpenGolfTests.lean`](formal/PcsOpenGolfTests.lean) | executable checks: Keccak-256 against Ethereum and OpenSSL vectors, field laws on samples, polynomial evaluation and claims, the two machines' system calls |
| [`verifier/`](verifier/) | `verify.py`, policy checks, contract pin, comparator configs, tests |
| [`tools/`](tools/) | `check_repo.py`, every local check in one command |
| [`docs/`](docs/README.md) | the rules for each track and the design notes |

## Credits

The contract, verifier and layout are adapted from [sig.golf](https://github.com/Layr-Labs/sig.golf) and ots.golf; see [NOTICE](NOTICE). License: Apache 2.0.
