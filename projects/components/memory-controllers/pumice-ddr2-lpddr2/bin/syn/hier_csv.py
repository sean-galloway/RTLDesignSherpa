#!/usr/bin/env python3
"""Turn a yosys hierarchical `stat` dump into a per-FUB CSV.

Reads a stat file produced with `read_slang --best-effort-hierarchy`, where
each module section is named ``module$full.instance.path``. Builds the
instance tree, rolls cell counts up so every node reports itself PLUS
everything under it, and converts to NAND-2 equivalents using the weight
table from bin/yosys_to_nand_equiv.py (imported, not copied, so the CSV
tracks that script).

CSV shape: hierarchy depth is encoded as leading commas, so each level
lands in its own spreadsheet column; the numeric columns stay aligned at
a fixed offset past the deepest level.
"""

import argparse
import importlib.util
import os
import re
import sys
from pathlib import Path

# Repo root: env override, else walk up from this file (…/projects/
# components/memory-controllers/<proj>/bin/syn/ -> 6 levels).
_ROOT = Path(os.environ.get("REPO_ROOT",
                            Path(__file__).resolve().parents[6]))
NAND_SCRIPT = _ROOT / "bin" / "yosys_to_nand_equiv.py"


def load_nand_module():
    spec = importlib.util.spec_from_file_location("nandeq", NAND_SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def parse_sections(path):
    """{instance_path: {cell_type: count}} plus the module name per path."""
    sections, cur = {}, None
    for line in open(path):
        m = re.match(r"=== (\S+) ===", line)
        if m:
            name = m.group(1).lstrip("\\")
            if name.startswith("design hierarchy"):
                cur = None
                continue
            if "$" in name:
                mod, inst = name.split("$", 1)
            else:
                mod, inst = name, name          # the top has no $path
            cur = inst
            sections[cur] = {"module": mod, "cells": {}}
            continue
        if cur is None:
            continue
        c = re.match(r"\s+(\d+)\s+(\$_\w+_)\s*$", line)
        if c:
            sections[cur]["cells"][c.group(2)] = int(c.group(1))
    return sections


def classify(cells):
    flops = sum(n for t, n in cells.items()
                if "DFF" in t or "LATCH" in t or "SR_" in t)
    comb = sum(n for t, n in cells.items()) - flops
    return flops, comb


def build_tree(sections, top):
    """Children keyed by parent instance path."""
    kids = {p: [] for p in sections}
    for path in sections:
        if path == top:
            continue
        parent = path.rsplit(".", 1)[0] if "." in path else top
        # Walk up until we hit a path that is actually a module section
        # (generate blocks appear in paths but have no section of their own).
        while parent not in sections and "." in parent:
            parent = parent.rsplit(".", 1)[0]
        if parent not in sections:
            parent = top
        kids.setdefault(parent, []).append(path)
    return kids


def rollup(sections, kids, node, nand_mod, memo):
    """(flops, comb, nand) for node including all descendants."""
    if node in memo:
        return memo[node]
    cells = dict(sections[node]["cells"])
    f, c = classify(cells)
    n, _, _ = nand_mod.cells_to_nand_equiv(cells)
    for k in kids.get(node, []):
        kf, kc, kn = rollup(sections, kids, k, nand_mod, memo)
        f += kf
        c += kc
        n += kn
    memo[node] = (f, c, n)
    return memo[node]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("stat")
    ap.add_argument("-o", "--output", required=True)
    ap.add_argument("--top", default="pumice_top")
    ap.add_argument("--max-depth", type=int, default=99)
    ap.add_argument("--flat-stat", help="flattened stat file; its totals are "
                    "emitted as the headline TOTAL row")
    args = ap.parse_args()

    nand_mod = load_nand_module()
    sections = parse_sections(args.stat)
    if args.top not in sections:
        sys.exit(f"top {args.top!r} not found in {args.stat}")
    kids = build_tree(sections, args.top)
    memo = {}

    depth_of = {args.top: 0}
    rows = []

    def walk(node, depth):
        f, c, n = rollup(sections, kids, node, nand_mod, memo)
        label = (sections[node]["module"] if depth == 0
                 else node.rsplit(".", 1)[-1] + " (" +
                 sections[node]["module"] + ")")
        rows.append((depth, label, f, c, n))
        if depth >= args.max_depth:
            return
        # Heaviest children first so the CSV reads as a cost ranking.
        for k in sorted(kids.get(node, []),
                        key=lambda x: -sum(rollup(sections, kids, x,
                                                  nand_mod, memo)[:2])):
            walk(k, depth + 1)

    walk(args.top, 0)
    maxd = max(r[0] for r in rows)

    # Headline total from the flattened (fully optimized) build. The
    # hierarchy-preserved numbers below are larger because keeping module
    # boundaries blocks cross-boundary optimization; use them for
    # ATTRIBUTION (which FUB owns the area), not as an absolute total.
    flat_row = None
    if args.flat_stat:
        flat_cells = {}
        for line in open(args.flat_stat):
            c = re.match(r"\s+(\d+)\s+(\$_\w+_)\s*$", line)
            if c:
                flat_cells[c.group(2)] = int(c.group(1))
        ff, fc = classify(flat_cells)
        fn, _, _ = nand_mod.cells_to_nand_equiv(flat_cells)
        flat_row = (ff, fc, fn)

    with open(args.output, "w") as fh:
        hdr = [f"L{i}" for i in range(maxd + 1)] + ["flops", "combo", "nand_eq"]
        fh.write(",".join(hdr) + "\n")
        if flat_row:
            pad = [""] * maxd
            fh.write(",".join(["TOTAL (flattened; optimized)"] + pad +
                              [str(x) for x in flat_row]) + "\n")
            fh.write(",".join(["TOTAL (hierarchy kept; = sum of rows below)"] +
                              pad + [str(x) for x in
                                     (rows[0][2], rows[0][3], rows[0][4])])
                     + "\n")
        for depth, label, f, c, n in rows:
            cells = [""] * (maxd + 1)
            cells[depth] = label
            fh.write(",".join(cells + [str(f), str(c), str(n)]) + "\n")
    print(f"{args.output}: {len(rows)} rows, max depth {maxd}, "
          f"top = {rows[0][2]:,} flops / {rows[0][3]:,} combo / "
          f"{rows[0][4]:,} NAND-eq")


if __name__ == "__main__":
    main()
