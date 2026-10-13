#!/usr/bin/env python3
"""Run the local checks without network access.

    python3 tools/check_repo.py                       # pin, verifier tests, shell syntax
    python3 tools/check_repo.py --formal              # also build Lean, audit axioms, run Lean tests
    python3 tools/check_repo.py --formal --official --submissions ../pcs-open.golf-submissions

--official runs the full pipeline for every track whose root exists in the submissions checkout.
Adapted from ots.golf-dev (8b140a99afa5, Apache-2.0).
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--formal', action='store_true', help='build Lean, audit the contract, run the Lean tests')
    parser.add_argument('--official', action='store_true', help='verify every root present in --submissions')
    parser.add_argument('--submissions', type=Path, help='submissions checkout verified by --official')
    args = parser.parse_args()
    if args.official and not args.submissions:
        parser.error('--official needs --submissions PATH')

    def check(label: str, command: list[str], cwd: Path = ROOT) -> None:
        print(f'\nChecking {label}', flush=True)
        subprocess.run(command, cwd=cwd, check=True)

    try:
        check('contract pin', [sys.executable, 'verifier/pin_contract.py', 'check'])
        check('verifier tests', [sys.executable, '-m', 'unittest', 'discover', '-s', 'verifier/tests'])
        for script in sorted((ROOT / 'verifier').glob('*.sh')):
            check(str(script.relative_to(ROOT)), ['bash', '-n', str(script)])
        if args.formal or args.official:
            check('Lean contract', ['lake', 'build'], ROOT / 'formal')
            check('contract axioms', ['lake', 'env', 'lean', 'scripts/check-axioms.lean'], ROOT / 'formal')
            check('Lean regression tests', ['lake', 'env', 'lean', 'PcsOpenGolfTests.lean'], ROOT / 'formal')
        if args.official:
            cfg = json.loads((ROOT / 'challenges.json').read_text())
            source = args.submissions.resolve()
            present = [t for t in cfg['tracks'] if (source / t['submission_root'] / 'Solution.lean').is_file()]
            if not present:
                print(f'No submission roots found in {source}', file=sys.stderr)
                return 1
            for track in present:
                check(f"official pipeline {track['slug']}",
                      [sys.executable, 'verifier/verify.py', track['slug'], '--source', str(source)])
    except (subprocess.CalledProcessError, OSError) as error:
        print(f'Check failed: {error}', file=sys.stderr)
        return 1
    print('\nRequested local checks passed.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
