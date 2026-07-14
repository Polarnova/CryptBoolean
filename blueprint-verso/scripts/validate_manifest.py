#!/usr/bin/env python3
"""Validate the generated CryptBoolean Blueprint manifest."""
from __future__ import annotations

import json
import sys
from pathlib import Path


def fail(message: str) -> None:
    print(message, file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    manifest_path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("_out/site/html-multi/-verso-data/blueprint-manifest.json")
    if not manifest_path.exists():
        fail(f"manifest missing: {manifest_path}")
    data = json.loads(manifest_path.read_text())
    previews = data.get("previews", [])
    blocks = [p for p in previews if p.get("targetKind") == "block" and p.get("facet") == "statement"]
    lean_decls = [p for p in previews if p.get("targetKind") == "leanDecl"]
    if data.get("vbpInternalSchemaVersion") != 2:
        fail("unexpected Blueprint schema version")
    if len(blocks) != 23:
        fail(f"expected 23 statement blocks, found {len(blocks)}")
    if len(data.get("graphs", [])) != 1:
        fail("expected exactly one dependency graph")
    graph = data["graphs"][0]
    if len(graph.get("nodes", [])) != len(blocks):
        fail("graph node count does not match statement block count")
    if len(graph.get("edges", [])) != 26:
        fail(f"expected 26 statement dependency edges, found {len(graph.get('edges', []))}")
    block_keys = {p["key"] for p in blocks}
    node_keys = {n.get("previewKey") for n in graph.get("nodes", [])}
    if block_keys != node_keys:
        fail("graph nodes do not match statement preview keys")
    decls = [decl for block in blocks for decl in block.get("codeData", {}).get("external", {}).get("decls", [])]
    if len(lean_decls) != len(decls):
        fail("Lean declaration preview count does not match associated declarations")
    missing = [d.get("canonical") for d in decls if not d.get("present")]
    if missing:
        fail("missing external declarations: " + ", ".join(missing))
    unproved = [d.get("canonical") for d in decls if d.get("provedStatus") != "proved"]
    if unproved:
        fail("unproved external declarations: " + ", ".join(unproved))
    unknown_refs = [n.get("label") for n in graph.get("nodes", []) if n.get("warnings", {}).get("unknownRef")]
    if unknown_refs:
        fail("unknown graph references: " + ", ".join(unknown_refs))
    print(f"manifest ok: {len(blocks)} statements, {len(decls)} declarations, {len(graph.get('edges', []))} edges")


if __name__ == "__main__":
    main()
