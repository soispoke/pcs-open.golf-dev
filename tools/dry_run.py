#!/usr/bin/env python3
"""Private dry run of the whole verification pipeline, with fixtures whose verdicts are known.

    python3 tools/dry_run.py [--work DIR] [--only CASE ...]

No known design has the Lean proofs a real certificate needs, so the dry run cannot verify a real
entry yet. It checks instead that every verdict the pipeline can return comes out where it must:

  app-sorry, opening-sorry   the real tracks, the rendered statement with `sorry` proofs: rejected
  app-wrong-import           a header import from the other track: policy_rejected
  app-wrong-claim            a claim outside its bounds: policy_rejected
  submissions-repo           the real, still empty submissions checkout: policy_rejected
  selftest-ok                a self-test track added to a copy of the contract, proven: verified
  selftest-mismatch          the same, proving a different statement: rejected
  selftest-native-decide     the same, closed with `native_decide`: rejected

The self-test track exists only in a temporary copy of the trusted tree, which is re-pinned there;
the real contract is never edited. Results go to `<work>/results.json`.
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SUBMISSIONS = ROOT.parent / "pcs-open.golf-submissions"

APP_CLAIM = {"B": 408, "N": 5, "C0": 1425, "M": 1}
OPENING_CLAIM = {"S": 150000, "C": 29000, "L": 12}

SELFTEST_TRACK = {
    "slug": "selftest",
    "title": "Pipeline self-test (dry run only)",
    "summary": "Not a track.",
    "direction": "-",
    "claim_fields": {"X": {"meaning": "a number", "min": 0, "max": 100}},
    "score": "X",
    "submission_root": "formal/Submissions/SelfTest",
    "module_prefix": "Submissions.SelfTest",
    "solution_module": "Submissions.SelfTest.Solution",
    "challenge_template": "formal/PcsOpenGolf/Challenge/SelfTest.lean.in",
    "challenge_file": "formal/PcsOpenGolf/Challenge/SelfTest.lean",
    "challenge_module": "PcsOpenGolf.Challenge.SelfTest",
    "comparator_config": "verifier/comparator-selftest.json",
    "allowed_import_prefixes": ["PcsOpenGolf.Parameters"],
}

SELFTEST_STUB = """import PcsOpenGolf.Parameters

/-! Pipeline self-test for the dry run, not a track: a definition hole and a theorem over it. -/

namespace PcsOpenGolf.Challenge.SelfTest

def submission : Nat := sorry

theorem certificate : submission = {{X}} ∧ PcsOpenGolf.MAX_CLAIMS = 8 := sorry

end PcsOpenGolf.Challenge.SelfTest
"""


def selftest_solution(value: int, proof: str) -> str:
    return f"""import PcsOpenGolf.Parameters

namespace PcsOpenGolf.Challenge.SelfTest

def submission : Nat := 8

theorem certificate : submission = {value} ∧ PcsOpenGolf.MAX_CLAIMS = 8 := {proof}

end PcsOpenGolf.Challenge.SelfTest
"""


def rendered_stub(slug: str, claim: dict) -> str:
    name = {"app": "App", "opening": "Opening"}[slug]
    text = (ROOT / f"formal/PcsOpenGolf/Challenge/{name}.lean.in").read_text()
    for key, value in claim.items():
        text = text.replace("{{" + key + "}}", str(value))
    return text


def write_root(source: Path, root: str, files: dict[str, str]) -> None:
    d = source / root
    d.mkdir(parents=True)
    for name, text in files.items():
        (d / name).write_text(text)


def selftest_trusted(work: Path) -> Path:
    """A copy of the trusted tree with the self-test track, re-pinned in the copy."""
    trusted = work / "trusted-selftest"
    skip = shutil.ignore_patterns(".lake", ".tools", ".work", "__pycache__", ".git")
    shutil.copytree(ROOT, trusted, ignore=skip)
    (trusted / "verifier/.tools").mkdir()
    shutil.copyfile(ROOT / "verifier/.tools/env.sh", trusted / "verifier/.tools/env.sh")
    cfg = json.loads((trusted / "challenges.json").read_text())
    cfg["tracks"].append(SELFTEST_TRACK)
    cfg["protected"] += [SELFTEST_TRACK["challenge_template"], SELFTEST_TRACK["comparator_config"]]
    (trusted / "challenges.json").write_text(json.dumps(cfg, indent=2) + "\n")
    (trusted / SELFTEST_TRACK["challenge_template"]).write_text(SELFTEST_STUB)
    (trusted / SELFTEST_TRACK["comparator_config"]).write_text(json.dumps({
        "challenge_module": SELFTEST_TRACK["challenge_module"],
        "solution_module": SELFTEST_TRACK["solution_module"],
        "theorem_names": ["PcsOpenGolf.Challenge.SelfTest.certificate"],
        "definition_names": ["PcsOpenGolf.Challenge.SelfTest.submission"],
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "enable_nanoda": False}, indent=2) + "\n")
    subprocess.run([sys.executable, str(trusted / "verifier/pin_contract.py"), "pin", "--root", str(trusted)],
                   check=True, capture_output=True)
    return trusted


def cases(work: Path) -> list[dict]:
    fx = work / "fixtures"
    out = []

    def case(name, slug, expect, files=None, root=None, source=None, trusted=ROOT):
        if source is None:
            source = fx / name
            write_root(source, root, files)
        out.append({"case": name, "track": slug, "expect": expect, "source": source, "trusted": trusted})

    app, opening = "formal/Submissions/App", "formal/Submissions/Opening"
    notes = "Dry-run fixture: the rendered statement with `sorry` proofs. Not an entry.\n"
    case("app-sorry", "app", "rejected", {"Solution.lean": rendered_stub("app", APP_CLAIM),
         "claim.json": json.dumps(APP_CLAIM), "NOTES.md": notes}, app)
    case("opening-sorry", "opening", "rejected", {"Solution.lean": rendered_stub("opening", OPENING_CLAIM),
         "claim.json": json.dumps(OPENING_CLAIM), "NOTES.md": notes}, opening)
    case("app-wrong-import", "app", "policy_rejected", {"Solution.lean": "import PcsOpenGolf.Opening.Statements\n",
         "claim.json": json.dumps(APP_CLAIM)}, app)
    case("app-wrong-claim", "app", "policy_rejected", {"Solution.lean": rendered_stub("app", APP_CLAIM),
         "claim.json": json.dumps({**APP_CLAIM, "N": 9})}, app)
    if SUBMISSIONS.is_dir():
        case("submissions-repo", "app", "policy_rejected", source=SUBMISSIONS)
    trusted = selftest_trusted(work)
    st = "formal/Submissions/SelfTest"
    case("selftest-ok", "selftest", "verified", {"Solution.lean": selftest_solution(8, "⟨rfl, rfl⟩"),
         "claim.json": json.dumps({"X": 8})}, st, trusted=trusted)
    case("selftest-mismatch", "selftest", "rejected", {"Solution.lean": selftest_solution(7, "sorry"),
         "claim.json": json.dumps({"X": 8})}, st, trusted=trusted)
    case("selftest-native-decide", "selftest", "rejected", {"Solution.lean": selftest_solution(8, "by native_decide"),
         "claim.json": json.dumps({"X": 8})}, st, trusted=trusted)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--work", type=Path)
    ap.add_argument("--only", nargs="*")
    a = ap.parse_args()
    work = (a.work or ROOT / ".work" / time.strftime("dry-run-%Y%m%d-%H%M%S")).resolve()
    work.mkdir(parents=True, exist_ok=False)
    results = []
    for c in cases(work):
        if a.only and c["case"] not in a.only:
            continue
        print(f"\n== {c['case']} ({c['track']}), expecting {c['expect']}", flush=True)
        run_dir = work / "runs" / c["case"]
        run_dir.parent.mkdir(parents=True, exist_ok=True)
        cmd = [sys.executable, str(ROOT / "verifier/verify.py"), c["track"], "--source", str(c["source"]),
               "--trusted", str(c["trusted"]), "--lake", str(ROOT / "formal/.lake"), "--work", str(run_dir),
               "--keep", "--json"]
        started = time.monotonic()
        proc = subprocess.run(cmd, capture_output=True, text=True)
        try:
            verdict = json.loads(proc.stdout)
        except ValueError:
            verdict = {"status": "crashed", "stderr": proc.stderr[-2000:]}
        ok = verdict.get("status") == c["expect"]
        results.append({"case": c["case"], "track": c["track"], "expect": c["expect"], "status": verdict.get("status"),
                        "ok": ok, "seconds": round(time.monotonic() - started, 1),
                        "detail": verdict.get("errors") or verdict.get("reason") or verdict.get("tail", "")[-600:],
                        "claim": verdict.get("claim"), "score": verdict.get("score")})
        print(f"   {verdict.get('status')} in {results[-1]['seconds']}s {'ok' if ok else 'UNEXPECTED'}", flush=True)
    contract = subprocess.run([sys.executable, str(ROOT / "verifier/pin_contract.py"), "id"],
                              capture_output=True, text=True).stdout.strip()
    (work / "results.json").write_text(json.dumps({"contract": contract, "results": results}, indent=2) + "\n")
    print(f"\n{sum(r['ok'] for r in results)}/{len(results)} cases as expected; contract {contract[:16]}; {work}/results.json")
    return 0 if all(r["ok"] for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
