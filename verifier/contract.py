"""Shared helpers for the pcs-open.golf verifier scripts. Standard library only.

Adapted from ots.golf-dev (8b140a99afa5, Apache-2.0). A claim here is not one integer but a
small JSON object whose keys are the track's `claim_fields`, as in sig.golf's `claim.json`.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

LEAN_FILE_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*\.lean")
CLAIM_FILE = "claim.json"
CLAIM_MAX_BYTES = 512
# A canonical integer as it appears in the claim file: no sign, no leading zero, no exponent.
INTEGER_RE = re.compile(r"(?:0|[1-9][0-9]*)")
SCORE_RE = re.compile(r"[A-Z][A-Z0-9_]*|[0-9]+|[()*+]")


class ContractError(Exception):
    pass


def repo_root(start: Path | None = None) -> Path:
    p = (start or Path(__file__).resolve().parent).resolve()
    for cand in (p, *p.parents):
        if (cand / "challenges.json").is_file():
            return cand
    raise ContractError("challenges.json not found above %s" % p)


def load_challenges(root: Path) -> dict:
    try:
        return json.loads((root / "challenges.json").read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise ContractError(f"cannot read challenges.json: {exc}") from exc


def track(cfg: dict, slug: str) -> dict:
    for t in cfg["tracks"]:
        if t["slug"] == slug:
            return t
    raise ContractError(f"unknown track {slug!r}; known: {[t['slug'] for t in cfg['tracks']]}")


def read_claim(path: Path, fields: dict) -> dict[str, int]:
    """The claim file is a JSON object with exactly the track's fields, each a canonical integer
    within its bounds. Bytes are read with a bound before parsing."""
    try:
        with path.open("rb") as stream:
            raw = stream.read(CLAIM_MAX_BYTES + 1)
    except OSError as exc:
        raise ContractError(f"cannot read {path}: {exc}") from exc
    if len(raw) > CLAIM_MAX_BYTES:
        raise ContractError(f"{path.name} exceeds {CLAIM_MAX_BYTES} bytes")
    try:
        value = json.loads(raw.decode("utf-8"), parse_float=_reject, parse_constant=_reject)
    except (UnicodeError, ValueError) as exc:
        raise ContractError(f"{path.name}: not a JSON object of integers: {exc}") from exc
    if not isinstance(value, dict) or set(value) != set(fields):
        raise ContractError(f"{path.name} must contain exactly {sorted(fields)}")
    out = {}
    for key, bound in fields.items():
        v = value[key]
        if type(v) is not int or not INTEGER_RE.fullmatch(str(v)):
            raise ContractError(f"{path.name}: {key} must be a nonnegative decimal integer")
        if not bound["min"] <= v <= bound["max"]:
            raise ContractError(f"{path.name}: {key} = {v} is outside [{bound['min']}, {bound['max']}]")
        out[key] = v
    return out


def _reject(text):
    raise ValueError(f"non-integer number {text!r}")


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def parameter_set(root: Path, cfg: dict, set_id: str | None = None) -> dict:
    """The published price in force (the latest set), or the named one."""
    try:
        sets = json.loads((root / cfg["contract"]["scoring_file"]).read_text(encoding="utf-8"))["parameter_sets"]
    except (OSError, ValueError, KeyError) as exc:
        raise ContractError(f"cannot read the scoring file: {exc}") from exc
    if set_id is None:
        return max(sets, key=lambda s: s["from"])
    for s in sets:
        if s["id"] == set_id:
            return s
    raise ContractError(f"unknown parameter set {set_id!r}")


def score(t: dict, claim: dict[str, int], params: dict) -> int:
    """Evaluate the track's score formula: integers, field names, published parameters, `+`, `*`
    and parentheses only. No `eval`."""
    tokens = SCORE_RE.findall(t["score"].replace(" ", ""))
    if "".join(tokens) != t["score"].replace(" ", ""):
        raise ContractError(f"bad score formula {t['score']!r}")
    env = {**{k: v for k, v in params.items() if isinstance(v, int)}, **claim}
    pos = 0

    def atom() -> int:
        nonlocal pos
        tok = tokens[pos]
        pos += 1
        if tok == "(":
            v = expr()
            if tokens[pos] != ")":
                raise ContractError("unbalanced score formula")
            pos += 1
            return v
        if tok.isdigit():
            return int(tok)
        if tok not in env:
            raise ContractError(f"score formula names unknown {tok!r}")
        return env[tok]

    def term() -> int:
        nonlocal pos
        v = atom()
        while pos < len(tokens) and tokens[pos] == "*":
            pos += 1
            v *= atom()
        return v

    def expr() -> int:
        nonlocal pos
        v = term()
        while pos < len(tokens) and tokens[pos] == "+":
            pos += 1
            v += term()
        return v

    v = expr()
    if pos != len(tokens):
        raise ContractError("trailing tokens in score formula")
    return v


def improves(direction: str, new: int, record: int) -> bool:
    return new > record if direction == "+" else new < record
