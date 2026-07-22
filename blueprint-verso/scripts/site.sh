#!/usr/bin/env bash

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
packages_dir="$(jq -er '.packagesDir // ".lake/packages"' "$root/lake-manifest.json")"
packages_root="$(cd "$root/$packages_dir" && pwd)"
output="$root/_out/site"
profile="${2:-release}"

case "$profile" in
  dev|release)
    ;;
  *)
    echo "invalid Blueprint profile '$profile'; expected dev or release" >&2
    exit 2
    ;;
esac

export BLUEPRINT_PROFILE="$profile"

if command -v lake >/dev/null 2>&1; then
  lake_cmd="$(command -v lake)"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  lake_cmd="$HOME/.elan/bin/lake"
else
  echo "lake is not available" >&2
  exit 127
fi

build_site() {
  cd "$root"
  python3 "$root/scripts/check_statement_style.py"
  echo "Reusing the checked production-library artifacts..."
  "$lake_cmd" --no-build build @CryptBoolean/CryptBoolean
  echo "Building the Blueprint modules..."
  "$lake_cmd" build @/CryptBooleanBlueprint
  rm -rf -- "$output/html-multi"
  export CRYPTBOOLEAN_SOURCE_REVISION="${GITHUB_SHA:-$(git -C "$root/.." rev-parse HEAD)}"
  export FABL_SOURCE_REVISION="$(
    git -C "$packages_root/FABL" rev-parse HEAD
  )"
  export MATHLIB_SOURCE_REVISION="$(
    git -C "$packages_root/mathlib" rev-parse HEAD
  )"
  "$lake_cmd" lean CryptBooleanBlueprintMain.lean -- --run \
    CryptBooleanBlueprintMain.lean --output "$output" --depth 2
  test -f "$output/html-multi/index.html"
  test -f "$output/html-multi/-verso-data/blueprint-manifest.json"
  "$lake_cmd" exe vbp check --site "$output" >/dev/null
  python3 "$root/scripts/validate_manifest.py" \
    "$output/html-multi/-verso-data/blueprint-manifest.json"
  touch "$output/html-multi/.nojekyll"
  touch "$output/html-multi/favicon.ico"
}

case "${1:-build}" in
  build)
    build_site
    ;;
  serve)
    build_site
    exec python3 -m http.server --directory "$output/html-multi" "${PORT:-8000}"
    ;;
  *)
    echo "usage: $0 [build|serve] [release|dev]" >&2
    exit 2
    ;;
esac
