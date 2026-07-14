#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
if command -v lake >/dev/null 2>&1; then
  lake_cmd="$(command -v lake)"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  lake_cmd="$HOME/.elan/bin/lake"
else
  echo "lake is not available" >&2
  exit 127
fi
output="$($lake_cmd env lean scripts/audit_axioms.lean 2>&1)"
printf '%s\n' "$output"
if printf '%s\n' "$output" | grep -E 'sorryAx' >/dev/null; then
  echo "sorryAx found in public declarations" >&2
  exit 1
fi
