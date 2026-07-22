#!/usr/bin/env bash

set -euo pipefail

workspace="$(cd "${1:-.}" && pwd)"
manifest="$workspace/lake-manifest.json"

test -f "$manifest"

curl_args=(-fsSL -H "Accept: application/vnd.github+json")
if [[ -n "${GH_TOKEN:-}" ]]; then
  curl_args+=(-H "Authorization: Bearer $GH_TOKEN")
fi

latest_tag="$(curl "${curl_args[@]}" \
  https://api.github.com/repos/Polarnova/FABL/releases/latest | jq -er '.tag_name')"
pinned_tag="$(jq -er '.packages[] | select(.name == "FABL") | .inputRev' "$manifest")"
test "$pinned_tag" = "$latest_tag"

if command -v lake >/dev/null 2>&1; then
  lake_cmd="$(command -v lake)"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  lake_cmd="$HOME/.elan/bin/lake"
else
  printf 'lake is not available\n' >&2
  exit 127
fi

"$lake_cmd" -d="$workspace" build @ProbabilityApproximation:release
"$lake_cmd" -d="$workspace" build @FABL:release

packages_dir="$(jq -r '.packagesDir // ".lake/packages"' "$manifest")"
fabl_package="$(cd "$workspace" && cd "$packages_dir/FABL" && pwd)"
"$fabl_package/scripts/verify_probability_approximation_release.sh" "$workspace"
"$fabl_package/scripts/verify_release.sh" "$workspace"
"$lake_cmd" --quiet --no-build -d="$workspace" build @FABL/FABL

printf 'Using latest FABL release: %s\n' "$pinned_tag"
