#!/usr/bin/env python3
"""Validate the generated CryptBoolean Blueprint manifest."""
from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path


EXPECTED_STATEMENTS = 43
EXPECTED_FORMALIZED = 41
EXPECTED_DECLARATIONS = 180
EXPECTED_EDGES = 64
EXPECTED_CHAPTERS = {
    "chapter-2": 36,
    "chapter-3": 7,
}
EXPECTED_GROUPS = {
    "«carlet-chapter-2»": 36,
    "«carlet-chapter-3»": 7,
}
EXPECTED_OPEN = {
    "carlet-2-trace-monomial-degree",
    "carlet-3-prop-12",
}


def fail(message: str) -> None:
    print(message, file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    manifest_path = (
        Path(sys.argv[1])
        if len(sys.argv) > 1
        else Path("_out/site/html-multi/-verso-data/blueprint-manifest.json")
    )
    if not manifest_path.exists():
        fail(f"manifest missing: {manifest_path}")
    data = json.loads(manifest_path.read_text())
    previews = data.get("previews", [])
    blocks = [
        preview
        for preview in previews
        if preview.get("targetKind") == "block" and preview.get("facet") == "statement"
    ]
    lean_decls = [p for p in previews if p.get("targetKind") == "leanDecl"]
    block_decls = {
        block["authoredLabel"]: ((block.get("codeData") or {}).get("external") or {}).get("decls", [])
        for block in blocks
    }
    formalized_blocks = [label for label, decls in block_decls.items() if decls]
    open_blocks = [label for label, decls in block_decls.items() if not decls]
    if data.get("vbpInternalSchemaVersion") != 3:
        fail("unexpected Blueprint schema version")
    if len(blocks) != EXPECTED_STATEMENTS:
        fail(f"expected {EXPECTED_STATEMENTS} statement blocks, found {len(blocks)}")
    if len(formalized_blocks) != EXPECTED_FORMALIZED:
        fail(f"expected {EXPECTED_FORMALIZED} formalized blocks, found {len(formalized_blocks)}")
    if set(open_blocks) != EXPECTED_OPEN:
        fail("unexpected open statement set: " + ", ".join(sorted(open_blocks)))
    if len(previews) != len(blocks) + len(lean_decls):
        fail("manifest contains previews other than statements and associated Lean declarations")

    labels = [block["authoredLabel"] for block in blocks]
    duplicate_labels = sorted(label for label, count in Counter(labels).items() if count != 1)
    if duplicate_labels:
        fail("duplicate statement labels: " + ", ".join(duplicate_labels))
    for chapter, expected in EXPECTED_CHAPTERS.items():
        actual = sum(chapter in block.get("tags", []) for block in blocks)
        if actual != expected:
            fail(f"expected {expected} {chapter} statements, found {actual}")
    malformed_metadata = [
        block["authoredLabel"]
        for block in blocks
        if "carlet" not in block.get("tags", [])
        or sum(chapter in block.get("tags", []) for chapter in EXPECTED_CHAPTERS) != 1
        or not block.get("sourceLocation", {}).get("ok")
    ]
    if malformed_metadata:
        fail("invalid statement metadata: " + ", ".join(malformed_metadata))
    wrong_open_tags = [
        block["authoredLabel"]
        for block in blocks
        if ((block["authoredLabel"] in EXPECTED_OPEN) != ("source-open" in block.get("tags", [])))
    ]
    if wrong_open_tags:
        fail("source-open tags do not match declaration state: " + ", ".join(wrong_open_tags))

    if len(data.get("graphs", [])) != 1:
        fail("expected exactly one dependency graph")
    graph = data["graphs"][0]
    if len(graph.get("nodes", [])) != len(blocks):
        fail("graph node count does not match statement block count")
    if len(graph.get("edges", [])) != EXPECTED_EDGES:
        fail(
            f"expected {EXPECTED_EDGES} statement dependency edges, "
            f"found {len(graph.get('edges', []))}"
        )
    block_keys = {p["key"] for p in blocks}
    node_keys = {n.get("previewKey") for n in graph.get("nodes", [])}
    if block_keys != node_keys:
        fail("graph nodes do not match statement preview keys")
    malformed_edges = [edge for edge in graph.get("edges", []) if edge.get("axes") != ["statement"]]
    if malformed_edges:
        fail("dependency graph contains a non-statement edge")
    statement_uses = sum(len(block.get("statementUses", [])) for block in blocks)
    rendered_uses = sum(len(block.get("uses", [])) for block in blocks)
    if statement_uses != EXPECTED_EDGES or rendered_uses != EXPECTED_EDGES:
        fail("statement dependency counts disagree with the graph")
    if any(block.get("proofUses") for block in blocks):
        fail("proof-only dependency edges are not permitted in this Blueprint")
    groups = graph.get("groups", [])
    group_sizes = {
        group.get("label"): len(group.get("children", []))
        for group in groups
        if group.get("declared")
    }
    if group_sizes != EXPECTED_GROUPS:
        fail(f"unexpected dependency graph groups: {group_sizes}")
    parent_sizes = Counter(node.get("parent") for node in graph.get("nodes", []))
    if dict(parent_sizes) != EXPECTED_GROUPS:
        fail(f"unexpected dependency graph parents: {dict(parent_sizes)}")
    variants = graph.get("variants", [])
    expected_variants = {
        "full",
        "group",
        *(f"parent:{group}" for group in EXPECTED_GROUPS),
    }
    if {variant.get("key") for variant in variants} != expected_variants:
        fail("dependency graph is missing a chapter view")
    if any((variant.get("options") or {}).get("direction") != "LR" for variant in variants):
        fail("dependency graph does not default to LR")

    decls = [decl for declarations in block_decls.values() for decl in declarations]
    if len(decls) != EXPECTED_DECLARATIONS:
        fail(f"expected {EXPECTED_DECLARATIONS} associated declarations, found {len(decls)}")
    if len(lean_decls) != len(decls):
        fail("Lean declaration preview count does not match associated declarations")
    declaration_names = [decl.get("canonical") for decl in decls]
    duplicate_declarations = sorted(
        name for name, count in Counter(declaration_names).items() if count != 1
    )
    if duplicate_declarations:
        fail("declarations are associated more than once: " + ", ".join(duplicate_declarations))
    block_preview_keys = [
        key for block in blocks for key in block.get("leanCodePreviewKeys", [])
    ]
    lean_preview_keys = [preview.get("key") for preview in lean_decls]
    if Counter(block_preview_keys) != Counter(lean_preview_keys):
        fail("statement declaration-preview links are not a bijection")
    missing = [d.get("canonical") for d in decls if not d.get("present")]
    if missing:
        fail("missing external declarations: " + ", ".join(missing))
    unproved = [d.get("canonical") for d in decls if d.get("provedStatus") != "proved"]
    if unproved:
        fail("unproved external declarations: " + ", ".join(unproved))
    unrendered = [d.get("canonical") for d in decls if "ok" not in d.get("render", {})]
    if unrendered:
        fail("unrendered external declarations: " + ", ".join(unrendered))

    nodes_by_key = {node["previewKey"]: node for node in graph.get("nodes", [])}
    warning_nodes = [
        node.get("label")
        for node in graph.get("nodes", [])
        if any(node.get("warnings", {}).values())
    ]
    if warning_nodes:
        fail("dependency graph warnings: " + ", ".join(warning_nodes))
    invalid_statuses = []
    for block in blocks:
        node = nodes_by_key[block["key"]]
        if block_decls[block["authoredLabel"]]:
            valid = node.get("statementStatus") == "formalized" and node.get("proofStatus") in {
                "formalized",
                "formalizedWithAncestors",
            }
        else:
            valid = node.get("statementStatus") in {"ready", "blocked"} and node.get(
                "proofStatus"
            ) in {"ready", "none"}
        if not valid:
            invalid_statuses.append(block["authoredLabel"])
    if invalid_statuses:
        fail("invalid statement/proof status: " + ", ".join(invalid_statuses))

    print(
        f"manifest ok: {len(blocks)} statements "
        f"({len(formalized_blocks)} formalized, {len(open_blocks)} open), "
        f"{len(decls)} declarations, {len(graph.get('edges', []))} edges"
    )


if __name__ == "__main__":
    main()
