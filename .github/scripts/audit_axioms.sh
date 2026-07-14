#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
if command -v lake >/dev/null 2>&1; then
  lake_cmd="$(command -v lake)"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  lake_cmd="$HOME/.elan/bin/lake"
else
  echo "lake is not available" >&2
  exit 127
fi
if ! output="$($lake_cmd env lean .github/scripts/audit_axioms.lean 2>&1)"; then
  printf '%s\n' "$output" >&2
  exit 1
fi
printf '%s\n' "$output"
if printf '%s\n' "$output" | rg -q 'sorryAx'; then
  echo "sorryAx found in public declarations" >&2
  exit 1
fi
