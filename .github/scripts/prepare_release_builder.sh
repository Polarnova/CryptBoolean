#!/usr/bin/env bash

set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <consumer-directory>" >&2
  exit 2
fi

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
consumer_dir="$1"

mkdir -p "$consumer_dir"
cp "$root/lean-toolchain" "$consumer_dir/lean-toolchain"
{
  echo 'name = "CryptBooleanReleaseBuilder"'
  echo 'version = "0.0.0"'
  echo
  echo '[[require]]'
  echo 'name = "CryptBooleanFunction"'
  printf 'path = "%s"\n' "$root"
} > "$consumer_dir/lakefile.toml"

lake -d="$consumer_dir" update
lake -d="$consumer_dir" exe cache get
"$root/.github/scripts/require_latest_fabl_release.sh" "$consumer_dir"
