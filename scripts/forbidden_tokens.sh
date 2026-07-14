#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
if grep -RInE '\b(sorry|admit|axiom|unsafe|native_decide)\b' CryptBoolean CryptBoolean.lean; then
  echo "forbidden Lean token found" >&2
  exit 1
fi
