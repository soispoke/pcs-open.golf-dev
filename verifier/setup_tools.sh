#!/usr/bin/env bash
# Build the verification tools next to the project: comparator, lean4export and (on Linux) landrun.
# Adapted from ots.golf-dev (8b140a99afa5, Apache-2.0); sig.golf pins the same revisions.
#
#   verifier/setup_tools.sh          # builds into verifier/.tools/ and runs comparator's test suite
#
# Policy: the judge must be compiled with the project's exact Lean release, because it replays the
# export through the kernel it was compiled with and lean4export reads the project's .olean files.
# We therefore pin the comparator revision whose declared toolchain has the SAME MINOR VERSION as
# ours and override only the patch digit. Anything else (different minor, or patching comparator's
# checks) is refused here on purpose.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tools="${root}/verifier/.tools"
export PATH="${HOME}/.elan/bin:${PATH}"

# leanprover/comparator @ 2026-08-10 (merge of PR #70): declared toolchain v4.33.0, the last
# revision before the v4.34.0-rc1 bump. Its own manifest pins the matching lean4export.
readonly comparator_rev="c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809"
# Zouuup/landrun (Linux only)
readonly landrun_rev="811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"

minor() { sed -E 's/^leanprover\/lean4:v([0-9]+\.[0-9]+)\..*$/\1/' "$1"; }

if ! command -v elan >/dev/null 2>&1; then
  echo "elan is required; install and verify it before bootstrapping the pinned verification tools" >&2
  exit 1
fi

clone_at() {  # url rev dest
  if [[ ! -d "$3/.git" ]]; then
    git clone --filter=blob:none --no-checkout "$1" "$3"
  fi
  # A checkout already at the pinned revision needs no fetch, so an offline host can reuse one
  # (for example a copy of sig.golf's identical comparator checkout). The checks below still run.
  if [[ "$(git -C "$3" rev-parse -q --verify HEAD 2>/dev/null || true)" != "$2" ]]; then
    git -C "$3" fetch --depth=1 origin "$2"
  fi
  git -C "$3" checkout --detach --force "$2"
  # Old untracked source files must not become inputs to the pinned build. Ignored build
  # caches remain, and Lake checks their source hashes before reusing them.
  git -C "$3" clean -ffd
  [[ "$(git -C "$3" rev-parse HEAD)" == "$2" ]]
  [[ -z "$(git -C "$3" status --porcelain --untracked-files=no)" ]] || { echo "dirty checkout: $3" >&2; exit 1; }
}

mkdir -p "${tools}"
clone_at https://github.com/leanprover/comparator.git "${comparator_rev}" "${tools}/comparator"

ours="$(minor "${root}/formal/lean-toolchain")"
theirs="$(minor "${tools}/comparator/lean-toolchain")"
if [[ "${ours}" != "${theirs}" ]]; then
  echo "refusing: project toolchain minor ${ours} differs from comparator's declared ${theirs}" >&2
  exit 1
fi
echo "comparator declares $(cat "${tools}/comparator/lean-toolchain"); building with $(cat "${root}/formal/lean-toolchain")"
cp "${root}/formal/lean-toolchain" "${tools}/comparator/lean-toolchain"
( cd "${tools}/comparator" && lake build lean4export comparator )

lean4export_bin="${tools}/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
comparator_bin="${tools}/comparator/.lake/build/bin/comparator"
[[ -x "${lean4export_bin}" && -x "${comparator_bin}" ]]

if [[ "$(uname -s)" == Linux ]]; then
  command -v go >/dev/null 2>&1 || { echo "Go 1.24+ is required to build landrun" >&2; exit 1; }
  clone_at https://github.com/Zouuup/landrun.git "${landrun_rev}" "${tools}/landrun"
  ( cd "${tools}/landrun" && go build -trimpath -o landrun ./cmd/landrun )
  landrun_bin="${tools}/landrun/landrun"
else
  echo "non-Linux host: landrun not built; local runs use comparator's fake-landrun shim (NOT a sandbox)" >&2
  landrun_bin="${tools}/comparator/scripts/fake-landrun.sh"
fi

# Acceptance: comparator's own test suite must pass on this toolchain.
echo "running comparator's test suite"
( cd "${tools}/comparator" && \
  COMPARATOR_LANDRUN="${landrun_bin}" COMPARATOR_LEAN4EXPORT="${lean4export_bin}" lean --run runtests.lean )

cat > "${tools}/env.sh" <<ENV
export COMPARATOR_BIN="${comparator_bin}"
export COMPARATOR_LEAN4EXPORT="${lean4export_bin}"
export COMPARATOR_LANDRUN="${landrun_bin}"
ENV
echo "tools ready; source ${tools}/env.sh"
echo "  lean4export rev: $(python3 -c "import json;print([p['rev'] for p in json.load(open('${tools}/comparator/lake-manifest.json'))['packages'] if p['name']=='lean4export'][0])")"
