#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
TAG_PATTERN = re.compile(r"^v\d+\.\d+\.\d+$")


@dataclass(frozen=True)
class Replacement:
    pattern: str
    value: str


@dataclass(frozen=True)
class TransformResult:
    text: str
    errors: tuple[str, ...]


def replace_once(text: str, replacement: Replacement) -> TransformResult:
    updated, count = re.subn(
        replacement.pattern,
        replacement.value,
        text,
        count=1,
        flags=re.MULTILINE,
    )
    errors = () if count == 1 else (replacement.pattern,)
    return TransformResult(updated, errors)


def transform(text: str, replacements: tuple[Replacement, ...]) -> TransformResult:
    current = TransformResult(text, ())
    for replacement in replacements:
        next_result = replace_once(current.text, replacement)
        current = TransformResult(
            next_result.text,
            current.errors + next_result.errors,
        )
    return current


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("fabl_tag")
    parser.add_argument("lean_tag")
    args = parser.parse_args()

    if TAG_PATTERN.fullmatch(args.fabl_tag) is None:
        return 2
    if TAG_PATTERN.fullmatch(args.lean_tag) is None:
        return 2

    toolchain = f"leanprover/lean4:{args.lean_tag}\n"
    errors: tuple[str, ...] = ()

    updates = (
        (
            ROOT / "lakefile.lean",
            (
                Replacement(
                    r'^(require FABL from git "[^"]+" @ ")[^"]+("$)',
                    rf"\g<1>{args.fabl_tag}\g<2>",
                ),
            ),
        ),
        (
            ROOT / "blueprint-verso" / "lakefile.lean",
            (
                Replacement(
                    r'^(require VersoBlueprint from git "[^"]+" @ ")[^"]+("$)',
                    rf"\g<1>{args.lean_tag}\g<2>",
                ),
            ),
        ),
        (
            ROOT / "AGENTS.md",
            (
                Replacement(
                    r"(FABL is imported from the exact release tag `)v\d+\.\d+\.\d+(`)",
                    rf"\g<1>{args.fabl_tag}\g<2>",
                ),
            ),
        ),
        (
            ROOT / ".agents" / "SPEC.md",
            (
                Replacement(
                    r"(The Lean package pins FABL at release `)v\d+\.\d+\.\d+(`)",
                    rf"\g<1>{args.fabl_tag}\g<2>",
                ),
            ),
        ),
        (
            ROOT / ".agents" / "PLAN.md",
            (
                Replacement(
                    r"(CryptBoolean pins FABL at release `)v\d+\.\d+\.\d+(`)",
                    rf"\g<1>{args.fabl_tag}\g<2>",
                ),
            ),
        ),
        (
            ROOT / "README.md",
            (
                Replacement(
                    r"(The repository pins Lean and Mathlib `)v\d+\.\d+\.\d+(`)",
                    rf"\g<1>{args.lean_tag}\g<2>",
                ),
                Replacement(
                    r"(latest stable FABL release, currently\n`)v\d+\.\d+\.\d+(`)",
                    rf"\g<1>{args.fabl_tag}\g<2>",
                ),
            ),
        ),
    )

    planned_updates = tuple(
        (path, transform(path.read_text(), replacements))
        for path, replacements in updates
    )
    for path, result in planned_updates:
        errors += tuple(f"{path}: {pattern}" for pattern in result.errors)

    if errors:
        for error in errors:
            print(error)
        return 1

    for path, result in planned_updates:
        path.write_text(result.text)
    (ROOT / "lean-toolchain").write_text(toolchain)
    (ROOT / "blueprint-verso" / "lean-toolchain").write_text(toolchain)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
