#!/usr/bin/env python3
"""Render a track's challenge stub from its template with the submission's claimed numbers.

    render_challenge.py TRACK [--claim FILE] [--root DIR]

The numbers come from `<submission_root>/claim.json` unless `--claim` names another file. Each
field `X` of the track replaces the placeholder `{{X}}` in the template. The rendered file is
what comparator compares the submission against, so the numbers in the kernel-checked statement
are exactly the numbers the leaderboard reads.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from contract import CLAIM_FILE, ContractError, load_challenges, read_claim, repo_root, track  # noqa: E402


def render(root: Path, slug: str, claim_file: Path | None) -> tuple[Path, dict]:
    cfg = load_challenges(root)
    t = track(cfg, slug)
    claim = read_claim(claim_file or root / t["submission_root"] / CLAIM_FILE, t["claim_fields"])
    text = (root / t["challenge_template"]).read_text(encoding="utf-8")
    for key, value in claim.items():
        placeholder = "{{" + key + "}}"
        if text.count(placeholder) != 1:
            raise ContractError(f"{t['challenge_template']} must hold {placeholder} exactly once")
        text = text.replace(placeholder, str(value))
    if "{{" in text:
        raise ContractError(f"{t['challenge_template']} has a placeholder the track does not declare")
    out = root / t["challenge_file"]
    out.write_text(text, encoding="utf-8")
    return out, claim


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("track")
    ap.add_argument("--claim", type=Path)
    ap.add_argument("--root", type=Path)
    a = ap.parse_args()
    try:
        out, claim = render(a.root or repo_root(), a.track, a.claim)
    except ContractError as exc:
        print(f"render_challenge: {exc}", file=sys.stderr)
        return 1
    print(f"{out} (claim {claim})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
