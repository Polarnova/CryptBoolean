#!/usr/bin/env python3
"""Generate the kernel-checked normalized weight-sixteen candidate table."""

from __future__ import annotations

import argparse
import hashlib
import math
import os
from dataclasses import dataclass
from itertools import combinations, permutations
from pathlib import Path
import sys
import tempfile
import time
from typing import NoReturn, Sequence


PATTERNS: tuple[tuple[str, tuple[int, ...]], ...] = (
    ("twoE8", (0, 1, 2, 3, 4, 5, 6, 7, 64, 72, 80, 88, 96, 104, 112, 120)),
    ("d16Plus", (0, 1, 2, 4, 8, 16, 32, 64, 127, 126, 125, 123, 119, 111, 95, 63)),
    ("f16", (0, 1, 2, 4, 8, 16, 32, 64, 126, 87, 55, 17, 31, 5, 3, 105)),
)
CLASS_CODES = {name: code for code, (name, _) in enumerate(PATTERNS)}
EXPECTED_CANDIDATE_COUNT = 2969
EXPECTED_PREFIX_COUNT = 278
EXPECTED_LOGICAL_SHA256 = "d35e0733be92ccaad2437f29159b74d57f9043107907cf76f6c29a1cb48ddf73"
LOW_64_BITS = (1 << 64) - 1
FIXED_POINTS = frozenset((0, 1, 2, 4, 8, 16, 32, 64))
PARITY = tuple(bin(value).count("1") & 1 for value in range(128))


LEAN_PREAMBLE = """/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.RankSevenPatterns

/-!
# Generated normalized weight-sixteen candidates

Each leaf records a canonical class, an invertible affine normalization,
the resulting 128-bit support mask, and its systematic 64-bit column code.
Candidate trees are sharded by the low sixteen bits of the systematic code so
that each kernel-checked finite classification problem remains small.
-/

@[expose] public section

namespace CryptBoolean

/-- One normalized-pattern certificate.  The affine code stores the source origin
in its low seven bits, followed by the seven rows of the normalizing linear map. -/
structure NormalizedWeightSixteenCandidate where
  patternClass : RankSevenWeightSixteenPatternClass
  affineCode : BitVec 56
  maskLow : BitVec 64
  maskHigh : BitVec 64
  systematicCode : BitVec 64

/-- A balanced tree keeps finite classification reduction logarithmic in the
number of certificates in one prefix shard. -/
inductive NormalizedWeightSixteenCandidateTree where
  | leaf (candidate : NormalizedWeightSixteenCandidate)
  | node (left right : NormalizedWeightSixteenCandidateTree)

namespace NormalizedWeightSixteenCandidateTree

/-- Whether the tree contains a certificate with the given systematic code. -/
def containsSystematicCode :
    NormalizedWeightSixteenCandidateTree → BitVec 64 → Bool
  | .leaf candidate, code => candidate.systematicCode == code
  | .node left right, code =>
      left.containsSystematicCode code || right.containsSystematicCode code

/-- Propositional membership in a generated candidate tree. -/
inductive Member (candidate : NormalizedWeightSixteenCandidate) :
    NormalizedWeightSixteenCandidateTree → Prop
  | leaf : Member candidate (.leaf candidate)
  | left {left right} : Member candidate left → Member candidate (.node left right)
  | right {left right} : Member candidate right → Member candidate (.node left right)

end NormalizedWeightSixteenCandidateTree

"""


class GenerationError(Exception):
    pass


class OneLineArgumentParser(argparse.ArgumentParser):
    def error(self, message: str) -> NoReturn:
        raise GenerationError(message)


@dataclass(frozen=True)
class Candidate:
    pattern_class: str
    class_code: int
    affine_code: int
    mask_low: int
    mask_high: int
    systematic_code: int


@dataclass(frozen=True)
class Deadline:
    expires_at: float

    def check(self, stage: str) -> None:
        if time.monotonic() >= self.expires_at:
            raise GenerationError(f"deadline exceeded during {stage}")


def inverse_rows(columns: Sequence[int]) -> tuple[int, ...] | None:
    rows = []
    for row_index in range(7):
        row = 0
        for column_index, column in enumerate(columns):
            row |= ((column >> row_index) & 1) << column_index
        rows.append(row | (1 << (7 + row_index)))
    for column in range(7):
        pivot = next(
            (row for row in range(column, 7) if (rows[row] >> column) & 1),
            None,
        )
        if pivot is None:
            return None
        rows[column], rows[pivot] = rows[pivot], rows[column]
        for row in range(7):
            if row != column and ((rows[row] >> column) & 1):
                rows[row] ^= rows[column]
    return tuple(row >> 7 for row in rows)


def coordinates(inverse: Sequence[int], value: int) -> int:
    result = 0
    for index, row in enumerate(inverse):
        result |= PARITY[row & value] << index
    return result


def permute_point(point: int, permutation: Sequence[int]) -> int:
    result = 0
    for target, source in enumerate(permutation):
        result |= ((point >> source) & 1) << target
    return result


def coordinate_permutation_tables(
    deadline: Deadline,
) -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    result = []
    for index, permutation in enumerate(permutations(range(7))):
        if index % 64 == 0:
            deadline.check("coordinate permutation tables")
        result.append(
            (
                permutation,
                tuple(permute_point(point, permutation) for point in range(128)),
            )
        )
    return tuple(result)


def normalized_pattern_masks(
    points: Sequence[int],
    permutation_tables: Sequence[tuple[tuple[int, ...], tuple[int, ...]]],
    deadline: Deadline,
) -> dict[int, tuple[int, tuple[int, ...]]]:
    masks: dict[int, tuple[int, tuple[int, ...]]] = {}
    basis_index = 0
    for origin in points:
        differences = [point ^ origin for point in points if point != origin]
        for basis in combinations(differences, 7):
            if basis_index % 256 == 0:
                deadline.check("affine basis enumeration")
            basis_index += 1
            inverse = inverse_rows(basis)
            if inverse is None:
                continue
            mask = 0
            for point in points:
                mask |= 1 << coordinates(inverse, point ^ origin)
            masks.setdefault(mask, (origin, inverse))

    ordered_masks: dict[int, tuple[int, tuple[int, ...]]] = {}
    for mask_index, (mask, (origin, inverse)) in enumerate(masks.items()):
        deadline.check("normalized mask permutation")
        support = tuple(point for point in range(128) if (mask >> point) & 1)
        for permutation_index, (permutation, table) in enumerate(permutation_tables):
            if permutation_index % 256 == 0:
                deadline.check("normalized mask permutation")
            transformed = 0
            for point in support:
                transformed |= 1 << table[point]
            ordered_inverse = tuple(inverse[source] for source in permutation)
            ordered_masks.setdefault(transformed, (origin, ordered_inverse))
        if mask_index % 16 == 0:
            deadline.check("normalized mask permutation")
    return ordered_masks


def systematic_column(point: int) -> int:
    return (1 ^ PARITY[point]) | (point << 1)


def generate_candidates(deadline: Deadline) -> tuple[Candidate, ...]:
    permutation_tables = coordinate_permutation_tables(deadline)
    candidates = []
    for pattern_class, points in PATTERNS:
        ordered_masks = normalized_pattern_masks(points, permutation_tables, deadline)
        for mask, (origin, inverse) in sorted(ordered_masks.items()):
            affine_code = origin
            for index, row in enumerate(inverse):
                affine_code |= row << (7 * (index + 1))
            mask_low = mask & LOW_64_BITS
            mask_high = mask >> 64
            columns = sorted(
                systematic_column(point)
                for point in range(128)
                if ((mask >> point) & 1) and point not in FIXED_POINTS
            )
            if len(columns) != 8:
                raise GenerationError("normalized mask does not have eight free columns")
            systematic_code = sum(
                column << (8 * index) for index, column in enumerate(columns)
            )
            candidates.append(
                Candidate(
                    pattern_class=pattern_class,
                    class_code=CLASS_CODES[pattern_class],
                    affine_code=affine_code,
                    mask_low=mask_low,
                    mask_high=mask_high,
                    systematic_code=systematic_code,
                )
            )
        deadline.check(f"{pattern_class} candidate generation")
    return tuple(candidates)


def logical_tsv(candidates: Sequence[Candidate]) -> bytes:
    lines = ["class_code\taffine_code\tmask_low\tmask_high\tsystematic_code"]
    lines.extend(
        "\t".join(
            str(value)
            for value in (
                candidate.class_code,
                candidate.affine_code,
                candidate.mask_low,
                candidate.mask_high,
                candidate.systematic_code,
            )
        )
        for candidate in candidates
    )
    return ("\n".join(lines) + "\n").encode("utf-8")


def candidate_buckets(candidates: Sequence[Candidate]) -> dict[int, list[Candidate]]:
    buckets: dict[int, list[Candidate]] = {}
    for candidate in candidates:
        buckets.setdefault(candidate.systematic_code & 0xFFFF, []).append(candidate)
    return buckets


def validate_candidates(candidates: Sequence[Candidate]) -> tuple[str, dict[int, list[Candidate]]]:
    if len(candidates) != EXPECTED_CANDIDATE_COUNT:
        raise GenerationError(
            f"candidate count {len(candidates)} != {EXPECTED_CANDIDATE_COUNT}"
        )
    systematic_codes = {candidate.systematic_code for candidate in candidates}
    if len(systematic_codes) != EXPECTED_CANDIDATE_COUNT:
        raise GenerationError("systematic candidate codes are not unique")
    buckets = candidate_buckets(candidates)
    if len(buckets) != EXPECTED_PREFIX_COUNT:
        raise GenerationError(f"prefix count {len(buckets)} != {EXPECTED_PREFIX_COUNT}")
    digest = hashlib.sha256(logical_tsv(candidates)).hexdigest()
    if digest != EXPECTED_LOGICAL_SHA256:
        raise GenerationError(
            f"logical SHA256 {digest} != {EXPECTED_LOGICAL_SHA256}"
        )
    return digest, buckets


def render_candidate_tree(
    candidates: Sequence[Candidate],
    indent: int,
    lines: list[str],
    deadline: Deadline,
) -> None:
    deadline.check("Lean candidate tree rendering")
    spaces = " " * indent
    if len(candidates) == 1:
        candidate = candidates[0]
        lines.extend(
            (
                f"{spaces}(.leaf",
                f"{spaces}  {{ patternClass := .{candidate.pattern_class}",
                f"{spaces}    affineCode := BitVec.ofNat 56 {candidate.affine_code}",
                f"{spaces}    maskLow := BitVec.ofNat 64 {candidate.mask_low}",
                f"{spaces}    maskHigh := BitVec.ofNat 64 {candidate.mask_high}",
                f"{spaces}    systematicCode := BitVec.ofNat 64 {candidate.systematic_code} }})",
            )
        )
        return
    midpoint = len(candidates) // 2
    lines.append(f"{spaces}(.node")
    render_candidate_tree(candidates[:midpoint], indent + 2, lines, deadline)
    render_candidate_tree(candidates[midpoint:], indent + 2, lines, deadline)
    lines.append(f"{spaces})")


def render_lean(
    buckets: dict[int, list[Candidate]], deadline: Deadline
) -> bytes:
    lines = [LEAN_PREAMBLE.rstrip("\n")]
    for prefix in sorted(buckets):
        deadline.check("Lean bucket rendering")
        suffix = f"{prefix:04x}"
        lines.extend(
            (
                "",
                f"/-- Generated candidate shard for systematic prefix 0x{suffix}. -/",
                f"def normalizedWeightSixteenCandidateBucket_{suffix} :",
                "    NormalizedWeightSixteenCandidateTree :=",
            )
        )
        render_candidate_tree(buckets[prefix], 2, lines, deadline)
    lines.extend(
        (
            "",
            "/-- Select the generated candidate shard determined by the first two sorted columns. -/",
            "def normalizedWeightSixteenCandidateBucket (codePrefix : BitVec 16) :",
            "    Option NormalizedWeightSixteenCandidateTree :=",
            "  match codePrefix.toNat with",
        )
    )
    for prefix in sorted(buckets):
        lines.append(
            f"  | {prefix} => some normalizedWeightSixteenCandidateBucket_{prefix:04x}"
        )
    lines.extend(("  | _ => none", "", "end CryptBoolean"))
    return ("\n".join(lines) + "\n").encode("utf-8")


def atomic_write(path: Path, content: bytes, deadline: Deadline) -> None:
    parent = path.parent if path.parent != Path("") else Path(".")
    if not parent.is_dir():
        raise GenerationError(f"output directory does not exist: {parent}")
    deadline.check("atomic output")
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=parent
    )
    temporary_path = Path(temporary_name)
    try:
        os.fchmod(descriptor, 0o644)
        with os.fdopen(descriptor, "wb") as output:
            output.write(content)
            output.flush()
            os.fsync(output.fileno())
        deadline.check("atomic output")
        os.replace(temporary_path, path)
    except BaseException:
        try:
            os.close(descriptor)
        except OSError:
            pass
        temporary_path.unlink(missing_ok=True)
        raise


def parse_arguments(argv: Sequence[str]) -> argparse.Namespace:
    parser = OneLineArgumentParser(
        description="Generate normalized rank-seven weight-sixteen Lean certificates."
    )
    parser.add_argument("--lean-output", type=Path)
    parser.add_argument("--check", type=Path)
    parser.add_argument("--timeout-seconds", type=float, default=60.0)
    arguments = parser.parse_args(argv)
    if arguments.lean_output is None and arguments.check is None:
        raise GenerationError("one of --lean-output or --check is required")
    if not math.isfinite(arguments.timeout_seconds) or arguments.timeout_seconds <= 0:
        raise GenerationError("--timeout-seconds must be finite and positive")
    return arguments


def run(argv: Sequence[str]) -> int:
    arguments = parse_arguments(argv)
    started_at = time.monotonic()
    deadline = Deadline(started_at + arguments.timeout_seconds)
    candidates = generate_candidates(deadline)
    digest, buckets = validate_candidates(candidates)
    lean = render_lean(buckets, deadline)
    actions = []
    if arguments.check is not None:
        deadline.check("Lean output check")
        actual = arguments.check.read_bytes()
        if actual != lean:
            actual_digest = hashlib.sha256(actual).hexdigest()
            expected_digest = hashlib.sha256(lean).hexdigest()
            raise GenerationError(
                f"Lean output mismatch actual={actual_digest} generated={expected_digest}"
            )
        actions.append(f"checked={arguments.check}")
    if arguments.lean_output is not None:
        atomic_write(arguments.lean_output, lean, deadline)
        actions.append(f"wrote={arguments.lean_output}")
    elapsed = time.monotonic() - started_at
    print(
        "normalized-weight-sixteen "
        f"candidates={len(candidates)} prefixes={len(buckets)} "
        f"logical-sha256={digest} lean-bytes={len(lean)} "
        f"elapsed={elapsed:.2f}s {' '.join(actions)}"
    )
    return 0


def main() -> int:
    try:
        return run(sys.argv[1:])
    except (GenerationError, OSError) as error:
        print(f"normalized-weight-sixteen error={error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
