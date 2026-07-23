#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
pattern='(^|[^[:alnum:]_])(sorry|admit|axiom|unsafe|native_decide)([^[:alnum:]_]|$)'
status=0
set +e
output="$(
  grep -RInE --include='*.lean' -- "$pattern" \
    CryptBoolean CryptBoolean.lean
)"
status=$?
set -e
case "$status" in
  0)
    printf '%s\n' "$output" | tail -n 200 >&2
    echo "forbidden Lean token found" >&2
    exit 1
    ;;
  1)
    ;;
  *)
    echo "forbidden-token scan failed with status $status" >&2
    exit "$status"
    ;;
esac
