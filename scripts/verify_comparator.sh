#!/usr/bin/env bash
# Run leanprover/comparator on the root comparator.json, including NanoDa.
# Verification script, released under Apache-2.0.
# Usage: scripts/verify_comparator.sh [StabilityOfMatter]
set -euo pipefail
if [ "$#" -gt 1 ] || { [ "$#" -eq 1 ] && [ "$1" != StabilityOfMatter ]; }; then
  echo "usage: scripts/verify_comparator.sh [StabilityOfMatter]" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/.." && pwd)
cache=${LT_COMPARATOR_CACHE:-"$HOME/.cache/lieb-thirring-comparator"}
comparator_commit=32bd61da1d68fbaa310234964e9b820b03a0f82f
lean4export_commit=6cea97789dc088ea47fcea15692db85685aedac5

# Use pinned builds: globally installed exporters may use another .olean format.
# Explicit overrides may point to existing toolchain-compatible binaries.
comparator=${COMPARATOR_BIN:-"$cache/comparator/.lake/build/bin/comparator"}
lean4export=${COMPARATOR_LEAN4EXPORT:-"$cache/lean4export/.lake/build/bin/lean4export"}
checkout_tool() {
  local name=$1 commit=$2
  mkdir -p "$cache"
  [ -d "$cache/$name/.git" ] || git clone -q --filter=blob:none \
    "https://github.com/leanprover/$name.git" "$cache/$name"
  git -C "$cache/$name" fetch -q --depth 1 origin "$commit"
  git -C "$cache/$name" checkout -q --detach "$commit"
  [ "$(tr -d '[:space:]' < "$cache/$name/lean-toolchain")" = \
    "$(tr -d '[:space:]' < "$root/lean-toolchain")" ] || {
    echo "error: $name toolchain differs from the project's" >&2; exit 1;
  }
  [ -x "$cache/$name/.lake/build/bin/$name" ] || \
    (cd "$cache/$name" && LEAN_NUM_THREADS=2 nice -n 10 lake build "$name")
}
if [ -z "${COMPARATOR_BIN:-}" ]; then
  checkout_tool comparator "$comparator_commit"
  comparator="$cache/comparator/.lake/build/bin/comparator"
fi
if [ -z "${COMPARATOR_LEAN4EXPORT:-}" ]; then
  checkout_tool lean4export "$lean4export_commit"
  lean4export="$cache/lean4export/.lake/build/bin/lean4export"
fi
landrun=${COMPARATOR_LANDRUN:-$(command -v landrun || true)}
nanoda=${COMPARATOR_NANODA:-$(command -v nanoda_bin || true)}
for tool in "$comparator" "$lean4export" "$landrun" "$nanoda"; do
  [ -n "$tool" ] && [ -x "$tool" ] || {
    echo "error: comparator, lean4export, landrun and nanoda_bin must be executable" >&2
    exit 1
  }
done

cd "$root"
[ -f comparator.json ] || { echo "error: comparator.json not found" >&2; exit 1; }

# Discard only this audit library's artifacts so both environments are freshly built.
rm -rf "$root/.lake/build/lib/lean/LiebThirringAudit" "$root/.lake/build/ir/LiebThirringAudit"
echo "=== comparator: StabilityOfMatter"
mapfile -t modules < <(python3 -I -c \
  'import json,sys; c=json.load(open(sys.argv[1])); print(c["challenge_module"]); print(c["solution_module"])' \
  comparator.json)
[ ${#modules[@]} -eq 2 ] || { echo "error: invalid comparator config" >&2; exit 1; }
# Prebuild with bounded parallelism; comparator's sandboxed builds find warm artifacts.
LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1} nice -n 10 lake build "${modules[@]}" || {
  echo "=== StabilityOfMatter: FAIL (build)"; exit 1;
}
if COMPARATOR_LEAN4EXPORT="$lean4export" COMPARATOR_NANODA="$nanoda" \
  COMPARATOR_LANDRUN="$landrun" LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2} \
  nice -n 10 lake env "$comparator" comparator.json; then
  echo "=== StabilityOfMatter: PASS"
else
  echo "=== StabilityOfMatter: FAIL"; exit 1
fi
