#!/usr/bin/env python3
"""Reject implementation prose and incomplete source metadata in Blueprint statements."""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = ROOT / "CryptBooleanBlueprint" / "Carlet"
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
        if "Formalization note" in block.body:
            errors.append(f"{location}: {block.identifier} contains a formalization note")
        if has_lean == is_open:
            expected = "a Lean association" if is_open else "the source-open tag"
            errors.append(f"{location}: {block.identifier} must have {expected}, but not both")
    formalized = sum("(lean :=" in block.header for block in blocks)
    open_count = sum("source-open" in block.header for block in blocks)
    if (len(blocks), formalized, open_count) != (116, 115, 1):
        errors.append(
            "expected 116 statements split into 115 formalized and 1 open; "
            f"found {len(blocks)}, {formalized}, and {open_count}"
        )
    if errors:
        print("\n".join(errors), file=sys.stderr)
        raise SystemExit(1)
    print(f"statement style ok: {len(blocks)} statements ({formalized} formalized, {open_count} open)")


if __name__ == "__main__":
    main()
