#!/usr/bin/env python3
"""Register-transfer dataflow diagrams from a Yosys word-level JSON.

The mux-level schematics (gen_schematics.py) show every $mux/$eq/$add; for a
module like the arbiter that is 6500 cells of hairball. This instead shows the
STATE -- flops, memories, ports -- as nodes, and collapses each combinational
cone BETWEEN two state elements into ONE labeled box:

    <source regs> --> [ cone into <sink> : depth N ; 420 mux, 96 eq, 8 add ] --> <sink reg>

So you see the main register-to-register paths, and every deep combinational
cloud is a box that says how deep it is and what it computes. Deepest cones are
the timing-critical ones, so `--min-depth` filters to just those.

Input is the Yosys JSON that gen_schematics.py already emits under build/.
Output is a graphviz PNG next to the mux-level PNGs.

    python3 gen_dataflow.py --module pumice_cmd_arbiter --min-depth 3
"""
import argparse, json, collections, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BUILD = HERE / "build"

FLOP_TYPES = {"$dff","$adff","$dffe","$adffe","$sdff","$sdffe","$sdffce","$dffsr","$dlatch"}
MEM_TYPES  = {"$mem_v2","$mem","$meminit_v2"}
# word-level op -> short label for the histogram
OP = {"$mux":"mux","$pmux":"pmux","$eq":"eq","$ne":"eq","$lt":"cmp","$le":"cmp",
      "$gt":"cmp","$ge":"cmp","$add":"add","$sub":"add","$mul":"mul",
      "$logic_and":"and","$logic_or":"or","$logic_not":"not","$and":"and",
      "$or":"or","$not":"not","$xor":"xor","$shiftx":"shift","$shift":"shift",
      "$shl":"shift","$shr":"shift","$sshr":"shift","$reduce_or":"redux",
      "$reduce_and":"redux","$reduce_bool":"redux","$mux-bus":"mux"}

def load(top):
    j = json.loads((BUILD / f"{top}.json").read_text())
    mods = j["modules"]
    key = top if top in mods else next(m for m in mods if top in m)
    return mods[key]

def analyze(mod):
    cells, netnames, ports = mod["cells"], mod.get("netnames",{}), mod.get("ports",{})
    # bit -> ("cell", cellname) that DRIVES it, or ("port", portname)
    driver = {}
    for cn, c in cells.items():
        dirs = c.get("port_directions", {})
        for pn, bits in c["connections"].items():
            if dirs.get(pn) == "output":
                for b in bits:
                    if isinstance(b, int): driver[b] = ("cell", cn)
    for pn, p in ports.items():
        if p["direction"] == "input":
            for b in p["bits"]:
                if isinstance(b, int): driver[b] = ("port", pn)
    # a readable name for each bit (first netname that carries it)
    bitname = {}
    for nn, info in netnames.items():
        for b in info["bits"]:
            if isinstance(b, int): bitname.setdefault(b, nn)

    def is_state(kind, name):
        if kind == "port": return True
        return cells[name]["type"] in FLOP_TYPES | MEM_TYPES

    def state_label(kind, name):
        if kind == "port": return name
        t = cells[name]["type"]
        # name a flop by the net on its Q
        q = cells[name]["connections"].get("Q", [])
        nm = next((bitname[b] for b in q if b in bitname), name)
        return nm

    # walk the combinational fan-in of a set of bits, stop at state, return
    # (set of source state labels, max depth, op histogram)
    def cone(start_bits):
        srcs, hist, seen = set(), collections.Counter(), {}
        def depth(cellname):
            if cellname in seen: return seen[cellname]
            seen[cellname] = 0  # cycle guard
            c = cells[cellname]; dirs = c.get("port_directions", {})
            hist[OP.get(c["type"], c["type"].strip("$"))] += 1
            d = 0
            for pn, bits in c["connections"].items():
                if dirs.get(pn) == "output": continue
                for b in bits:
                    if not isinstance(b, int): continue
                    dr = driver.get(b)
                    if dr is None: continue
                    k, nm = dr
                    if is_state(k, nm):
                        srcs.add(state_label(k, nm))
                    else:
                        d = max(d, depth(nm))
            seen[cellname] = d + 1
            return seen[cellname]
        md = 0
        for b in start_bits:
            dr = driver.get(b)
            if dr is None: continue
            k, nm = dr
            if is_state(k, nm): srcs.add(state_label(k, nm))
            else: md = max(md, depth(nm))
        return srcs, md, hist

    edges = []   # (src_label, sink_label, depth, hist)
    # sinks: flop D inputs, output ports, mem write ports
    for cn, c in cells.items():
        if c["type"] in FLOP_TYPES:
            sink = state_label("cell", cn)
            dbits = c["connections"].get("D", [])
            srcs, md, hist = cone(dbits)
            for s in srcs: edges.append((s, sink, md, hist))
    for pn, p in ports.items():
        if p["direction"] == "output":
            sink = pn
            srcs, md, hist = cone(p["bits"])
            for s in srcs: edges.append((s, sink, md, hist))
    return edges

def render(top, edges, min_depth, top_n, out_png):
    # group by SINK: one collapsed cone box per register/port summarizing its
    # whole input cone (depth + op-equation + the registers that feed it).
    from collections import defaultdict
    NL = "\\l"
    by_sink = defaultdict(lambda: [0, None, set()])  # sink -> [depth, hist, srcs]
    for s, d, dep, hist in edges:
        e = by_sink[d]
        if dep >= e[0]:
            e[0] = dep; e[1] = hist
        e[2].add(s)
    sinks = [(d, dep, hist, srcs) for d, (dep, hist, srcs) in by_sink.items()
             if dep >= min_depth]
    sinks.sort(key=lambda x: -x[1])
    if top_n:
        sinks = sinks[:top_n]
    lines = ['digraph G {', '  rankdir=LR;',
             '  node [shape=box,fontname="monospace",fontsize=10];',
             '  edge [color="#333333"];',
             '  graph [nodesep=0.25,ranksep=1.0];']
    for d, dep, hist, srcs in sinks:
        ops = ", ".join(f"{n}x{c}" for c, n in hist.most_common(5)) if hist else ""
        sl = sorted(srcs)
        shown = sl[:6]
        more = f" (+{len(sl)-6})" if len(sl) > 6 else ""
        frm = ("from: " + ", ".join(shown) + more) if shown else "from: (const)"
        box = f'"cone::{d}"'
        label = f"depth {dep}: {ops}{NL}{frm}{NL}"
        lines.append(f'  {box} [shape=box,style="rounded,filled",fillcolor="#ffcf6b",'
                     f'label="{label}"];')
        lines.append(f'  "{d}" [style=filled,fillcolor="#cfe8ff"];')
        lines.append(f'  {box} -> "{d}" [penwidth=1.4];')
    if not sinks:
        return 0
    lines.append('}')
    dot = out_png.with_suffix(".dot")
    dot.write_text("\n".join(lines))
    subprocess.run(["dot","-Tpng","-o",str(out_png),str(dot)], check=True)
    dot.unlink(missing_ok=True)
    return len(sinks)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--module", required=True)
    ap.add_argument("--min-depth", type=int, default=1)
    ap.add_argument("--top", type=int, default=40, help="keep the N deepest cones (0=all)")
    a = ap.parse_args()
    mod = load(a.module)
    edges = analyze(mod)
    out = HERE / f"{a.module}.dataflow.png"
    n = render(a.module, edges, a.min_depth, a.top, out)
    if n == 0:
        print(f"[skip] {a.module}: no cones with depth>={a.min_depth}")
        return 0
    kb = out.stat().st_size/1024
    print(f"[ok] {a.module}.dataflow.png  {n} paths (depth>={a.min_depth})  {kb:.0f} KB")

if __name__ == "__main__":
    sys.exit(main())
