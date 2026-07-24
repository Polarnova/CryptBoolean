#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
if (( $# > 1 )); then
  echo "usage: $0 [lake-workspace]" >&2
  exit 2
fi
workspace="${1:-$root}"
if [[ ! -d "$workspace" ]]; then
  echo "Lake workspace does not exist: $workspace" >&2
  exit 2
fi
workspace="$(cd "$workspace" && pwd)"
cd "$root"
if command -v lake >/dev/null 2>&1; then
  lake_cmd="$(command -v lake)"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  lake_cmd="$HOME/.elan/bin/lake"
else
  echo "lake is not available" >&2
  exit 127
fi
if ! output="$(
  "$lake_cmd" -d="$workspace" env lean "$root/.github/scripts/audit_axioms.lean" 2>&1
)"; then
  printf '%s\n' "$output" >&2
  exit 1
fi
printf '%s\n' "$output"
if [[ "$output" == *sorryAx* ]]; then
  echo "sorryAx found in public declarations" >&2
  exit 1
fi
