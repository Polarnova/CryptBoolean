#!/usr/bin/env python3
"""Validate mathematical presentation, source structure, and completion metadata."""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = ROOT / "CryptBooleanBlueprint" / "Carlet"
PUBLIC_SOURCES = (ROOT / "CryptBooleanBlueprint" / "Blueprint.lean",)
START = re.compile(
    r'^:::(definition|theorem|proposition|corollary|lemma_?)\s+"([^"]+)"(.*)$'
)
LABEL = re.compile(r"^\*[^*]+\.\*(?:\s|$)")
MARKDOWN_LINK = re.compile(r"\[[^]]+\]\([^)]+\)")
IMPLEMENTATION_TERMS = re.compile(
    r"\b(?:Lean|Mathlib|FABL|repository|library|declaration|implementation|implemented|"
    r"formalized|compiled|delegated|reuses?|upstream|source-open)\b",
    re.IGNORECASE,
)
READER_PROSE_TERMS = re.compile(
    r"\b(?:bridge|bridges|pipeline|interface|schema|node|nodes|compiled|associated|"
    r"source-facing|implementation|formalized|declaration|declarations)\b",
    re.IGNORECASE,
)
DISALLOWED_LABEL = "Formalization" + " note"
DISALLOWED_CONTRAST = "rather" + " than"
NUMBERED_HEADING = re.compile(r"^#{1,6}\s+\d+(?:\.\d+)*\.?\s+")
DEEP_HEADING = re.compile(r"^#{2,6}\s+")
REQUIRED_VOLUME_GROUPS = (
    "Chapter 1: Generalities on Boolean functions",
    "Chapter 2: Boolean functions and coding",
    "Chapter 3: Boolean functions and cryptography",
    "Chapter 4: Classes with Provable Spectra and Weights",
)
REQUIRED_PUBLIC_HEADINGS = {
    Path("Chapter02.lean"): (
        "# Representation of Boolean functions",
        "# The discrete Fourier transform on pseudo-Boolean and on Boolean functions",
        "# Fourier support and Cayley graphs",
    ),
    Path("Chapter03.lean"): ("# Reed--Muller codes",),
    Path("Chapter04.lean"): (
        "# Algebraic degree",
        "# Nonlinearity",
        "# Balancedness and resiliency",
        "# Strict avalanche and propagation criteria",
        "# Linear structures",
        "# Algebraic immunity",
        "# Autocorrelation",
        "# Maximum correlation",
        "# Other criteria",
    ),
    Path("Chapter05/Classes.lean"): (
        "# Affine functions",
        "# Quadratic functions",
        "# Indicators of flats",
        "# Normal functions",
        "# Functions admitting partial covering sequences",
        "# Functions with low univariate degree",
    ),
}
REQUIRED_OUTLINE_ORDER = {
    Path("Chapter02.lean"): (
        "# Representation of Boolean functions",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter02.Foundations}",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter02.ANF}",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter02.ANFExistence}",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter02.AlgebraicDegree}",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter02.FiniteField}",
        "# The discrete Fourier transform on pseudo-Boolean and on Boolean functions",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter02.NumericalNormalForm}",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter02.WalshTransform}",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter02.FourierOperations}",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter02.Fourier}",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter02.Derivatives}",
        "# Fourier support and Cayley graphs",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter02.SpectralSupport}",
    ),
    Path("Chapter03.lean"): (
        "# Reed--Muller codes",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter03.ReedMuller}",
    ),
    Path("Chapter04.lean"): (
        "# Algebraic degree",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter04.AlgebraicDegree}",
        "# Nonlinearity",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter04.Nonlinearity}",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter04.HigherOrderNonlinearity}",
        "# Balancedness and resiliency",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter04.Resiliency}",
        "# Strict avalanche and propagation criteria",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter04.Propagation}",
        "# Linear structures",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter04.LinearStructures}",
        "# Algebraic immunity",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter04.AlgebraicImmunity}",
        "# Autocorrelation",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter04.Autocorrelation}",
        "# Maximum correlation",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter04.MaximumCorrelation}",
        "# Other criteria",
        "{include 2 CryptBooleanBlueprint.Carlet.Chapter04.OtherCriteria}",
    ),
}


@dataclass(frozen=True)
class StatementBlock:
    path: Path
    line: int
    identifier: str
    header: str
    body: str


def statement_blocks(path: Path) -> list[StatementBlock]:
    """Parse top-level Verso statement directives from one source file."""
    lines = path.read_text().splitlines()
    blocks: list[StatementBlock] = []
    index = 0
    while index < len(lines):
        match = START.match(lines[index])
        if match is None:
            index += 1
            continue
        start = index
        index += 1
        body: list[str] = []
        while index < len(lines) and lines[index].strip() != ":::":
            body.append(lines[index])
            index += 1
        if index == len(lines):
            raise ValueError(f"unterminated statement: {path}:{start + 1}")
        blocks.append(
            StatementBlock(
                path=path,
                line=start + 1,
                identifier=match.group(2),
                header=lines[start],
                body="\n".join(body).strip(),
            )
        )
        index += 1
    return blocks


def main() -> None:
    """Validate every source-facing statement and report the formalized/open split."""
    blocks = [
        block
        for path in sorted(SOURCE_ROOT.rglob("*.lean"))
        for block in statement_blocks(path)
    ]
    errors: list[str] = []
    for path in (*PUBLIC_SOURCES, *sorted(SOURCE_ROOT.rglob("*.lean"))):
        text = path.read_text()
        location = path.relative_to(ROOT)
        for line_number, line in enumerate(text.splitlines(), start=1):
            if NUMBERED_HEADING.match(line):
                errors.append(f"{location}:{line_number}: public heading contains a written number")
            if DEEP_HEADING.match(line):
                errors.append(f"{location}:{line_number}: public heading is deeper than x.y")
        term = READER_PROSE_TERMS.search(text)
        if term is not None:
            line = text.count("\n", 0, term.start()) + 1
            errors.append(f"{location}:{line}: disallowed reader term {term.group(0)!r}")
        for phrase in (DISALLOWED_LABEL, DISALLOWED_CONTRAST, "affine-slice schema"):
            offset = text.lower().find(phrase.lower())
            if offset >= 0:
                line = text.count("\n", 0, offset) + 1
                errors.append(f"{location}:{line}: disallowed reader phrase {phrase!r}")
    root_lines = PUBLIC_SOURCES[0].read_text().splitlines()
    group_positions = [
        root_lines.index(group) if group in root_lines else -1 for group in REQUIRED_VOLUME_GROUPS
    ]
    for group, position in zip(REQUIRED_VOLUME_GROUPS, group_positions):
        if position < 0:
            errors.append(f"CryptBooleanBlueprint/Blueprint.lean: missing volume group {group!r}")
    if all(position >= 0 for position in group_positions) and group_positions != sorted(
        group_positions
    ):
        errors.append("CryptBooleanBlueprint/Blueprint.lean: volume groups are out of order")
    for relative, headings in REQUIRED_PUBLIC_HEADINGS.items():
        path = SOURCE_ROOT / relative
        lines = path.read_text().splitlines()
        positions = [lines.index(heading) if heading in lines else -1 for heading in headings]
        for heading, position in zip(headings, positions):
            if position < 0:
                errors.append(f"{path.relative_to(ROOT)}: missing public heading {heading!r}")
        if all(position >= 0 for position in positions) and positions != sorted(positions):
            errors.append(f"{path.relative_to(ROOT)}: public headings are out of order")
    for relative, outline in REQUIRED_OUTLINE_ORDER.items():
        path = SOURCE_ROOT / relative
        lines = path.read_text().splitlines()
        positions = [lines.index(item) if item in lines else -1 for item in outline]
        for item, position in zip(outline, positions):
            if position < 0:
                errors.append(f"{path.relative_to(ROOT)}: missing outline item {item!r}")
        if all(position >= 0 for position in positions) and positions != sorted(positions):
            errors.append(f"{path.relative_to(ROOT)}: public outline is out of order")
    for block in blocks:
        location = f"{block.path.relative_to(ROOT)}:{block.line}"
        first_line = next((line.strip() for line in block.body.splitlines() if line.strip()), "")
        has_lean = "(lean :=" in block.header
        is_open = "source-open" in block.header
        if LABEL.match(first_line) is None:
            errors.append(f"{location}: {block.identifier} lacks an italicized mathematical label")
        if "$`" not in block.body:
            errors.append(f"{location}: {block.identifier} contains no mathematical notation")
        if MARKDOWN_LINK.search(block.body):
            errors.append(f"{location}: {block.identifier} contains a link inside the statement")
        term = IMPLEMENTATION_TERMS.search(block.body)
        if term is not None:
            errors.append(
                f"{location}: {block.identifier} contains implementation term {term.group(0)!r}"
            )
        if has_lean == is_open:
            expected = "a Lean association" if is_open else "the source-open tag"
            errors.append(f"{location}: {block.identifier} must have {expected}, but not both")
    formalized = sum("(lean :=" in block.header for block in blocks)
    open_count = sum("source-open" in block.header for block in blocks)
    if (len(blocks), formalized, open_count) != (149, 146, 3):
        errors.append(
            "expected 149 statements split into 146 formalized and 3 open; "
            f"found {len(blocks)}, {formalized}, and {open_count}"
        )
    if errors:
        print("\n".join(errors), file=sys.stderr)
        raise SystemExit(1)
    print(f"statement style ok: {len(blocks)} statements ({formalized} formalized, {open_count} open)")


if __name__ == "__main__":
    main()
