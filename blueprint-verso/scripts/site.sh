#!/usr/bin/env bash

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output="$root/_out/site"

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
  "$lake_cmd" build CryptBooleanBlueprint
  rm -rf -- "$output/html-multi"
  "$lake_cmd" exe blueprint-gen --output "$output" --depth 2
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
    echo "usage: $0 [build|serve]" >&2
    exit 2
    ;;
esac
