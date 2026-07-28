#!/usr/bin/env python3
"""Validate the rendered chapter and section hierarchy."""

from __future__ import annotations

import re
import sys
from pathlib import Path


DEEP_SECTION_NUMBER = re.compile(r'class="(?:num|number)">(\d+(?:\.\d+){2,}\.?)(?:</td>|</span>)')
EXPECTED = {
    Path("index.html"): (
        "Generalities on Boolean functions",
        "Boolean functions and coding",
        "Boolean functions and cryptography",
        "Classes with Provable Spectra and Weights",
    ),
    Path("Boolean-functions-and-cryptography/index.html"): (
        '<td class="num">3.1.</td>',
        "Distribution of algebraic degree",
        "Nonlinearity",
        "Higher-order nonlinearity",
        "Other criteria",
    ),
    Path("Classes-with-Provable-Spectra-and-Weights/index.html"): (
        '<td class="num">4.1.</td>',
        "Affine functions",
        "Quadratic functions",
        "Indicators of flats",
        "Normal functions",
        "Functions admitting partial covering sequences",
        "Functions with low univariate degree",
    ),
}


def main() -> None:
    """Reject rendered headings below the section level and missing required titles."""
    root = Path(sys.argv[1])
    errors: list[str] = []
    for path in sorted(root.rglob("*.html")):
        text = path.read_text()
        for match in DEEP_SECTION_NUMBER.finditer(text):
            errors.append(f"{path.relative_to(root)}: rendered section number {match.group(1)} is deeper than x.y")
    for relative, snippets in EXPECTED.items():
        path = root / relative
        if not path.is_file():
            errors.append(f"{relative}: rendered page is missing")
            continue
        text = path.read_text()
        for snippet in snippets:
            if snippet not in text:
                errors.append(f"{relative}: missing rendered outline text {snippet!r}")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        raise SystemExit(1)
    print("rendered outline ok: chapter and section numbers stop at x.y")


if __name__ == "__main__":
    main()
