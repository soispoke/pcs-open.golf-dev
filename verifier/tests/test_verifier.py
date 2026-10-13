"""Regression tests for the pre-compilation trust boundary; no Lean or network needed.

The header-policy and export tests follow ots.golf-dev's (8b140a99afa5, Apache-2.0); the claim,
score and rendering tests cover what pcs-open.golf changes: claims with several named fields.
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

VERIFIER = Path(__file__).resolve().parents[1]
REPO = VERIFIER.parent
sys.path.insert(0, str(VERIFIER))
from check_submission import check, header_imports  # noqa: E402
from contract import ContractError, load_challenges, parameter_set, read_claim, score, track  # noqa: E402
from render_challenge import render  # noqa: E402
from verify import PolicyReject, export_submission  # noqa: E402

APP_CLAIM = {"B": 408, "N": 5, "C0": 1425, "M": 1}
OPENING_CLAIM = {"S": 150000, "C": 29000, "L": 12}
APP_SOLUTION = "import PcsOpenGolf.Statements\n\nnamespace PcsOpenGolf.Challenge.App\nend PcsOpenGolf.Challenge.App\n"


class Fixture(unittest.TestCase):
    """A temporary trusted tree: the real contract files, plus one submission root per test."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name) / "repo"
        self.root.mkdir()
        for rel in ("challenges.json", "scoring.json"):
            shutil.copyfile(REPO / rel, self.root / rel)
        for rel in ("formal/PcsOpenGolf/Challenge/App.lean.in", "formal/PcsOpenGolf/Challenge/Opening.lean.in"):
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(REPO / rel, self.root / rel)
        self.cfg = load_challenges(self.root)
        self.rel = "formal/Submissions/App"
        self.sub = self.root / self.rel
        self.sub.mkdir(parents=True)
        (self.sub / "Solution.lean").write_text(APP_SOLUTION)
        (self.sub / "claim.json").write_text(json.dumps(APP_CLAIM))

    def tearDown(self):
        self.tmp.cleanup()

    def errors(self, slug="app"):
        return check(self.root, slug)["errors"]


class ClaimTests(Fixture):
    def test_valid_app_root(self):
        res = check(self.root, "app")
        self.assertTrue(res["ok"], res["errors"])
        self.assertEqual(res["claim"], APP_CLAIM)
        self.assertEqual(res["score"], 408 * (1425 + 5 * 6500))
        self.assertEqual(res["parameter_set"], "P0")

    def test_claim_must_hold_exactly_the_fields(self):
        fields = track(self.cfg, "app")["claim_fields"]
        for value in ({"B": 1, "N": 0, "C0": 0}, {**APP_CLAIM, "S": 1}, {"b": 1, "N": 0, "C0": 0, "M": 0}):
            with self.subTest(value=value):
                (self.sub / "claim.json").write_text(json.dumps(value))
                with self.assertRaises(ContractError):
                    read_claim(self.sub / "claim.json", fields)

    def test_claim_values_are_bounded_canonical_integers(self):
        fields = track(self.cfg, "app")["claim_fields"]
        bad = ['{"B": 1.0, "N": 0, "C0": 0, "M": 0}', '{"B": true, "N": 0, "C0": 0, "M": 0}',
               '{"B": "1", "N": 0, "C0": 0, "M": 0}', '{"B": -1, "N": 0, "C0": 0, "M": 0}',
               '{"B": 0, "N": 0, "C0": 0, "M": 0}', '{"B": 16385, "N": 0, "C0": 0, "M": 0}',
               '{"B": 1, "N": 9, "C0": 0, "M": 0}', '{"B": 1, "N": 0, "C0": 16777216, "M": 0}',
               '{"B": 1e3, "N": 0, "C0": 0, "M": 0}', '{"B": NaN, "N": 0, "C0": 0, "M": 0}',
               '[1, 0, 0, 0]', 'not json']
        for text in bad:
            with self.subTest(text=text):
                (self.sub / "claim.json").write_text(text)
                with self.assertRaises(ContractError):
                    read_claim(self.sub / "claim.json", fields)

    def test_claim_size_is_bounded_before_parsing(self):
        (self.sub / "claim.json").write_text('{"B": 1, "N": 0, "C0": 0, "M": 0}' + " " * 600)
        with self.assertRaises(ContractError):
            read_claim(self.sub / "claim.json", track(self.cfg, "app")["claim_fields"])

    def test_opening_claim_bounds(self):
        fields = track(self.cfg, "opening")["claim_fields"]
        path = self.sub / "claim.json"
        path.write_text(json.dumps(OPENING_CLAIM))
        self.assertEqual(read_claim(path, fields), OPENING_CLAIM)
        for value in ({**OPENING_CLAIM, "L": 13}, {**OPENING_CLAIM, "C": 2 ** 26}, {**OPENING_CLAIM, "S": 0}):
            with self.subTest(value=value):
                path.write_text(json.dumps(value))
                with self.assertRaises(ContractError):
                    read_claim(path, fields)

    def test_missing_claim_is_a_policy_error(self):
        (self.sub / "claim.json").unlink()
        self.assertIn("claim.json is required", self.errors())

    def test_old_claim_txt_is_not_admitted(self):
        (self.sub / "claim.txt").write_text("1\n")
        self.assertTrue(any("claim.txt" in e for e in self.errors()))


class ScoreTests(Fixture):
    def test_scores_follow_the_formulas(self):
        params = parameter_set(self.root, self.cfg)
        self.assertEqual(score(track(self.cfg, "app"), APP_CLAIM, params), 13_841_400)
        self.assertEqual(score(track(self.cfg, "opening"), OPENING_CLAIM, params), 150000 * 29000)

    def test_latest_parameter_set_is_in_force(self):
        data = json.loads((self.root / "scoring.json").read_text())
        data["parameter_sets"].append({"id": "P1", "from": "2027-01-01", "CLAIM_CYCLES": 1000})
        (self.root / "scoring.json").write_text(json.dumps(data))
        params = parameter_set(self.root, self.cfg)
        self.assertEqual(params["id"], "P1")
        self.assertEqual(score(track(self.cfg, "app"), APP_CLAIM, params), 408 * (1425 + 5 * 1000))
        self.assertEqual(parameter_set(self.root, self.cfg, "P0")["CLAIM_CYCLES"], 6500)

    def test_score_formula_is_not_evaluated_as_python(self):
        t = dict(track(self.cfg, "app"), score="__import__('os').system('true')")
        with self.assertRaises(ContractError):
            score(t, APP_CLAIM, parameter_set(self.root, self.cfg))


class RenderTests(Fixture):
    def test_render_substitutes_every_field(self):
        out, claim = render(self.root, "app", None)
        text = out.read_text()
        self.assertEqual(claim, APP_CLAIM)
        self.assertIn("{ proofBytes := 408, claims := 5, cycles := 1425, proofRoots := 1 }", text)
        self.assertNotIn("{{", text)

    def test_render_opening(self):
        (self.sub / "claim.json").write_text(json.dumps(OPENING_CLAIM))
        out, _ = render(self.root, "opening", self.sub / "claim.json")
        self.assertIn("{ openingBytes := 150000, cycles := 29000, listBits := 12 }", out.read_text())

    def test_template_must_hold_each_placeholder_once(self):
        tpl = self.root / "formal/PcsOpenGolf/Challenge/App.lean.in"
        tpl.write_text(tpl.read_text().replace("{{M}}", "0"))
        with self.assertRaises(ContractError):
            render(self.root, "app", None)

    def test_template_with_an_undeclared_placeholder_is_refused(self):
        tpl = self.root / "formal/PcsOpenGolf/Challenge/App.lean.in"
        tpl.write_text(tpl.read_text() + "\n-- {{EXTRA}}\n")
        with self.assertRaises(ContractError):
            render(self.root, "app", None)


class HeaderPolicyTests(Fixture):
    def write(self, text, name="Solution.lean"):
        (self.sub / name).write_text(text)

    def test_contract_modules_are_exact_imports(self):
        self.write("import PcsOpenGolf.Statements\nimport PcsOpenGolf.Machine\n")
        self.assertEqual(self.errors(), [])
        self.write("import PcsOpenGolf.Challenge.App\n")
        self.assertTrue(self.errors())
        self.write("import PcsOpenGolf\n")
        self.assertTrue(self.errors())

    def test_tracks_admit_only_their_own_contract_modules(self):
        self.write("import PcsOpenGolf.Opening.Statements\n")
        self.assertTrue(self.errors("app"))

    def test_library_submodules_and_siblings(self):
        self.write("import Mathlib.Data.Nat.Basic\nimport VCVio\nimport Submissions.App.Helper\n")
        self.write("theorem t : True := trivial\n", "Helper.lean")
        self.assertEqual(self.errors(), [])
        self.write("import Submissions.App.Missing\n")
        self.assertTrue(self.errors())
        self.write("import Submissions.Opening.Solution\n")
        self.assertTrue(self.errors())

    def test_header_bypasses_are_rejected(self):
        for text in ("prelude\n", "module\nimport Mathlib\n", "public import Mathlib\n",
                     "import «PcsOpenGolf».Statements\n", "import Mathlib.Data /- -/ .Nat\n"):
            with self.subTest(text=text):
                self.assertIsNotNone(header_imports(text)[1])

    def test_comments_cannot_hide_header_commands(self):
        imports, err = header_imports("/- import Bad -/\nimport Mathlib\n-- import Bad\n")
        self.assertIsNone(err)
        self.assertEqual(imports, ["Mathlib"])

    def test_solution_is_required(self):
        (self.sub / "Solution.lean").unlink()
        self.assertIn("Solution.lean is required", self.errors())

    def test_flat_regular_files_only(self):
        (self.sub / "dir").mkdir()
        self.assertTrue(any("subdirectories" in e for e in self.errors()))
        (self.sub / "dir").rmdir()
        (self.sub / "data.bin").write_bytes(b"\0")
        self.assertTrue(any("only `.lean` files" in e for e in self.errors()))


class ExportTests(Fixture):
    def export(self, dest="out", **kwargs):
        return export_submission(str(self.root), None, self.rel, self.root / dest, **kwargs)

    def test_worktree_export_copies_the_root_byte_for_byte(self):
        self.assertEqual(self.export(), "worktree")
        self.assertEqual((self.root / "out" / self.rel / "claim.json").read_text(), json.dumps(APP_CLAIM))

    def test_symlink_is_rejected_before_read(self):
        os.symlink("/etc/hosts", self.sub / "Link.lean")
        with self.assertRaises(PolicyReject):
            self.export()

    def test_limits_apply_before_copy(self):
        with self.assertRaises(PolicyReject):
            self.export("out1", max_file_bytes=10)
        with self.assertRaises(PolicyReject):
            self.export("out2", max_files=1)
        self.assertEqual(list((self.root / "out1" / self.rel).iterdir()), [])

    def test_git_export_reads_the_commit_not_the_worktree(self):
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        subprocess.run(["git", "-C", str(self.root), "add", "."], check=True)
        subprocess.run(["git", "-C", str(self.root), "-c", "user.name=t", "-c", "user.email=t@invalid.example",
                        "-c", "commit.gpgsign=false", "commit", "-qm", "fixture"], check=True)
        (self.sub / "claim.json").write_text("changed after the commit")
        full = export_submission(str(self.root), "HEAD", self.rel, self.root / "out")
        self.assertRegex(full, r"^[0-9a-f]{40}$")
        self.assertEqual((self.root / "out" / self.rel / "claim.json").read_text(), json.dumps(APP_CLAIM))


class ContractPinTests(unittest.TestCase):
    def test_the_repository_pin_matches(self):
        res = subprocess.run([sys.executable, str(VERIFIER / "pin_contract.py"), "check", "--root", str(REPO)],
                             capture_output=True, text=True)
        self.assertEqual(res.returncode, 0, res.stderr)

    def test_every_track_file_is_protected(self):
        cfg = load_challenges(REPO)
        for t in cfg["tracks"]:
            for key in ("challenge_template", "comparator_config"):
                self.assertIn(t[key], cfg["protected"])
            comparator = json.loads((REPO / t["comparator_config"]).read_text())
            self.assertEqual(comparator["challenge_module"], t["challenge_module"])
            self.assertEqual(comparator["solution_module"], t["solution_module"])
            self.assertEqual(comparator["permitted_axioms"], cfg["permitted_axioms"])
            template = (REPO / t["challenge_template"]).read_text()
            for field in t["claim_fields"]:
                self.assertEqual(template.count("{{" + field + "}}"), 1)


if __name__ == "__main__":
    unittest.main()
