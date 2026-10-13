#!/usr/bin/env python3
"""Pin or check the protected files of the contract.

    pin_contract.py pin   [--root DIR]   # (re)write verifier/protected.sha256
    pin_contract.py check [--root DIR]   # exit 0 iff every protected file matches the pin
    pin_contract.py id    [--root DIR]   # print the contract id (sha256 of the pin file)

The protected list lives in challenges.json. The contract id is what a leaderboard displays: the
version name plus this hash identify exactly which statement every score refers to.
"""
from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from contract import ContractError, load_challenges, repo_root, sha256_file  # noqa: E402


def digest_lines(root: Path, cfg: dict) -> list[str]:
    lines = []
    for rel in sorted(cfg["protected"]):
        p = root / rel
        if not p.is_file():
            raise ContractError(f"protected file missing: {rel}")
        lines.append(f"{sha256_file(p)}  {rel}")
    return lines


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["pin", "check", "id"])
    ap.add_argument("--root", type=Path)
    a = ap.parse_args()
    root = a.root or repo_root()
    try:
        cfg = load_challenges(root)
        pin = root / cfg["contract"]["pin_file"]
        if a.cmd == "pin":
            content = "\n".join(digest_lines(root, cfg)) + "\n"
            pin.write_text(content, encoding="utf-8")
            print(f"pinned {len(cfg['protected'])} files; contract id {hashlib.sha256(content.encode()).hexdigest()}")
            return 0
        if not pin.is_file():
            raise ContractError(f"pin file missing: {pin}")
        content = pin.read_text(encoding="utf-8")
        if a.cmd == "id":
            print(hashlib.sha256(content.encode()).hexdigest())
            return 0
        expected = dict(line.split("  ", 1)[::-1] for line in content.splitlines() if line.strip())
        actual = dict(line.split("  ", 1)[::-1] for line in digest_lines(root, cfg))
        bad = [rel for rel in sorted(set(expected) | set(actual)) if expected.get(rel) != actual.get(rel)]
        for rel in bad:
            print(f"protected file differs from the pin: {rel}", file=sys.stderr)
        if not bad:
            print(f"contract ok: {cfg['contract']['version']} {hashlib.sha256(content.encode()).hexdigest()[:16]}")
        return 0 if not bad else 1
    except ContractError as exc:
        print(f"pin_contract: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
