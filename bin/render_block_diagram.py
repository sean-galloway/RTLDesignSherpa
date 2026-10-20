#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Render a house-style block diagram: drawing + generated key, composited.

    render_block_diagram.py X.dot [Y.dot ...] [--dpi 150] [--no-key]

For each X.dot writes X.png: the drawing, with a key row centered beneath it.
The key is GENERATED from the drawing (vault/handbook/authoring/block-diagrams.md,
"The key"): it samples exactly the node classes and line styles the drawing
uses, so it cannot drift from the drawing or carry an absent class. dot cannot
center a multi-item row under the graphics, so the key is rendered on its own
and pasted centered (Pillow). The result is palette-encoded (PNG8, alpha
flattened first, no tIME chunk) so an unchanged source re-renders identically.

Classes come from dot's resolved attributes (`dot -Tjson`, defaults applied),
by the element key: cylinder = storage, trapezium = pick, diagonals = FSM,
rounded = interface (dashed = comb crossing), double border = registered,
plain box = logic, note = note; `dashed` on a non-interface = optional, except
a grey (#777777) dashed box, which is a sideband waypoint and is not sampled.
Edges: green = return, dashed = sideband, penwidth >= 1.8 = heavy, else flow.
A drawing with nothing to sample (a cycle grid) gets no key. A drawing in another
vocabulary (a decision tree: white questions, blue actions) carries the line
`// render: no-key` and gets none; --no-key forces that for every file.
"""
from __future__ import annotations

import argparse
import json
import re
import pathlib
import shutil
import subprocess
import sys
import tempfile

from PIL import Image

GREEN = {"#1a7a1a"}


def _is_red(color: str) -> bool:
    """A red edge marks a timing-failing path (drawn from report_timing)."""
    c = color.lower().lstrip("#")
    try:
        r, g, b = int(c[0:2], 16), int(c[2:4], 16), int(c[4:6], 16)
    except (ValueError, IndexError):
        return False
    return r >= 0xC0 and g <= 0x60 and b <= 0x60


EDGE_ORDER = ["flow", "heavy", "return", "sideband", "failing"]
FILL = {"logic": "white", "registered": "#D6E4F0", "fsm": "#FCE4D6",
        "storage": "#E8DFF5", "pick": "#FFF2CC", "interface": "#E2EFDA",
        "note": "white"}
NODE_ORDER = ["logic", "registered", "fsm", "storage", "pick", "optional",
              "interface_flopped", "interface_comb", "note"]
GAP_PX = 25


def _attrs(obj: dict) -> dict:
    return {k: str(v) for k, v in obj.items()}


def classify(dot_json: dict) -> tuple[list[str], list[str]]:
    """Node classes and edge styles the drawing uses, in key order."""
    nodes, edges = set(), set()
    for o in dot_json.get("objects", []):
        if "nodes" in o or "edges" in o or "subgraphs" in o:
            continue                                    # a subgraph / cluster
        a = _attrs(o)
        style, shape = a.get("style", ""), a.get("shape", "box")
        if "invis" in style or shape in ("point", "none", "plaintext", "plain"):
            continue
        if a.get("label", "").startswith("<") or shape in ("record", "Mrecord"):
            continue                                    # HTML table: a grid, not a block
        if "dashed" in style and a.get("color", "").lower() == "#777777":
            continue                                    # sideband waypoint box (rule)
        if shape == "note":
            nodes.add("note")
        elif shape == "cylinder":
            nodes.add("storage")
        elif shape in ("invtrapezium", "trapezium") or (
                shape == "polygon" and a.get("distortion", "0") not in ("0", "0.0")):
            nodes.add("pick")
        elif "diagonals" in style:
            nodes.add("fsm")
        elif "rounded" in style:
            nodes.add("interface_comb" if "dashed" in style else "interface_flopped")
        elif a.get("peripheries", "1") not in ("1", ""):
            nodes.add("registered")
        else:
            nodes.add("logic")
        if "dashed" in style and "rounded" not in style and shape != "note":
            nodes.add("optional")
    for e in dot_json.get("edges", []):
        a = _attrs(e)
        style = a.get("style", "")
        if "invis" in style:
            continue
        if _is_red(a.get("color", "")):
            edges.add("failing")
        elif a.get("color", "").lower() in GREEN:
            edges.add("return")
        elif "dashed" in style or "dotted" in style:
            edges.add("sideband")
        elif float(a.get("penwidth", "1") or 1) >= 1.8:
            edges.add("heavy")
        else:
            edges.add("flow")
    return ([n for n in NODE_ORDER if n in nodes],
            [e for e in EDGE_ORDER if e in edges])


def key_dot(node_classes: list[str], edge_styles: list[str],
            flopped_words: bool = False) -> str:
    """One same-rank row: Key, short sample arrows, then one sample per class."""
    out = ['digraph key {',
           '  rankdir=TB;',
           '  graph [nodesep=0.14, ranksep=0.3, fontname="Helvetica", bgcolor=none];',
           '  node [fontname="Helvetica", fontsize=8, style=filled, fillcolor="white"];',
           '  edge [fontname="Helvetica", fontsize=8, arrowsize=0.7];',
           '  k_lbl [label="Key", shape=none, style="", fontsize=11];']
    row = ["k_lbl"]
    edge_attr = {"flow": 'color="#333333"', "heavy": 'penwidth=1.8',
                 "return": 'color="#1A7A1A"',
                 "sideband": 'style=dashed, color="#777777"',
                 "failing": 'color="#D00000", penwidth=2.2'}
    for i, e in enumerate(edge_styles):
        a, b = f"k_e{i}a", f"k_e{i}b"
        out.append(f'  {a} [shape=point, width=0.01, style=invis];')
        out.append(f'  {b} [shape=point, width=0.01, style=invis];')
        row += [a, b]
    node_def = {
        "logic": 'label="logic", shape=box',
        "registered": 'label="registered", shape=box, peripheries=2, fillcolor="#D6E4F0"',
        "fsm": 'label="FSM", shape=box, style="filled,diagonals", peripheries=2, fillcolor="#FCE4D6"',
        "storage": 'label="storage", shape=cylinder, fillcolor="#E8DFF5"',
        "pick": 'label="arbiter / pick", shape=invtrapezium, fillcolor="#FFF2CC"',
        "optional": 'label="optional\\n(build-dependent)", shape=box, style="filled,dashed"',
        "interface_flopped": (('label="interface\\n(flopped)"' if flopped_words else 'label="interface"')
                              + ', shape=box, style="rounded,filled", fillcolor="#E2EFDA"'),
        "interface_comb": 'label="interface\\n(comb)", shape=box, style="rounded,filled,dashed", fillcolor="#E2EFDA"',
        "note": 'label="note", shape=note',
    }
    for n in node_classes:
        out.append(f'  k_{n} [{node_def[n]}];')
        row.append(f"k_{n}")
    out.append("  { rank=same; " + "; ".join(row) + "; }")
    # No splines=ortho: ortho swallows plain edge labels, and short
    # horizontal samples don't need it.
    for i, e in enumerate(edge_styles):
        out.append(f'  k_e{i}a -> k_e{i}b [label="{e}", {edge_attr[e]}];')
    out.append("}")
    return "\n".join(out) + "\n"


def _run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    r = subprocess.run(cmd, capture_output=True, **kw)
    if r.returncode:
        err = r.stderr.decode(errors="replace") if isinstance(r.stderr, bytes) else r.stderr
        raise RuntimeError(f"{' '.join(cmd[:3])} ...: {err.strip()[:400]}")
    return r


def render(src: pathlib.Path, dpi: int, want_key: bool) -> str:
    out = src.with_suffix(".png")
    with tempfile.TemporaryDirectory() as td:
        tmp = pathlib.Path(td)
        main_png = tmp / "main.png"
        _run(["dot", "-Tpng", f"-Gdpi={dpi}", "-o", str(main_png), str(src)])
        classes, styles = ([], [])
        if want_key and not re.search(r"//\s*render:\s*no-key", src.read_text()):
            js = _run(["dot", "-Tjson", str(src)], text=True).stdout
            classes, styles = classify(json.loads(js))
        if classes or styles:
            kdot = tmp / "key.dot"
            # "(flopped)" only when the drawing itself annotates its interfaces
            kdot.write_text(key_dot(classes, styles,
                                    "flopped" in src.read_text().lower()))
            key_png = tmp / "key.png"
            _run(["dot", "-Tpng", f"-Gdpi={dpi}", "-o", str(key_png), str(kdot)])
            drawing = Image.open(main_png).convert("RGBA")
            key = Image.open(key_png).convert("RGBA")
            canvas = Image.new("RGBA", (max(drawing.width, key.width),
                                        drawing.height + GAP_PX + key.height), "white")
            canvas.paste(drawing, ((canvas.width - drawing.width) // 2, 0), drawing)
            canvas.paste(key, ((canvas.width - key.width) // 2,
                               drawing.height + GAP_PX), key)
            canvas.convert("RGB").save(main_png)
        if shutil.which("convert"):
            _run(["convert", str(main_png), "-background", "white", "-alpha", "remove",
                  "-alpha", "off", "-colors", "64", "-define", "png:exclude-chunk=tIME",
                  f"PNG8:{out}"])
        else:
            shutil.copy(main_png, out)
    with Image.open(out) as im:
        w, h = im.size
    key_desc = ",".join(styles + classes) or "no key"
    return f"{out.name}: {w}x{h} [{key_desc}]"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("dots", nargs="+", type=pathlib.Path)
    ap.add_argument("--dpi", type=int, default=150)
    ap.add_argument("--no-key", action="store_true")
    args = ap.parse_args()
    if not shutil.which("dot"):
        print("ERROR: graphviz 'dot' not found", file=sys.stderr)
        return 1
    fail = 0
    for src in args.dots:
        try:
            print(render(src, args.dpi, not args.no_key))
        except (RuntimeError, OSError, json.JSONDecodeError) as exc:
            print(f"{src}: FAILED: {exc}", file=sys.stderr)
            fail = 1
    return fail


if __name__ == "__main__":
    sys.exit(main())
