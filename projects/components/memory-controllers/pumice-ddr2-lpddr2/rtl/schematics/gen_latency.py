#!/usr/bin/env python3
"""Latency view: pipeline STAGES from a Yosys word-level JSON.

The other two views answer different questions. gen_schematics.py draws every
$mux/$eq/$add -- faithful, and a hairball above ~1200 cells. gen_dataflow.py
collapses each combinational cone into one box tagged with its depth -- that
answers "which cone is deep", a TIMING question.

Neither answers "how many flops from here to there", which is a LATENCY
question. This one does, and it prunes by CONSTRUCTION rather than by
filtering: the only nodes are STATE (flops, memories, ports). Combinational
logic is never drawn -- it is the edge. A module cannot produce a hairball at
this abstraction because the node count is the number of registers, not the
number of cells.

Registers are merged by the net name on their Q, so a bit-blasted r_bank[2:0]
is ONE node, not three.

Nodes are ranked into columns by flop-distance from the input ports, so
crossing one column = one clock. Count the columns and you have the latency.
Feedback loops are condensed (Tarjan SCC) so a register that feeds itself does
not make the longest path infinite; a stage containing a real loop is marked.

    python3 gen_latency.py --module pumice_cmd_arbiter
    python3 gen_latency.py --module pumice_cmd_arbiter --from s_axi --to cmd_
    python3 gen_latency.py --module pumice_rd_return_ring --table-only

Emits <module>.latency.png plus a latency TABLE on stdout (input -> output,
min/max flops). The table is the artifact that cannot be misread; the picture
is for seeing where the stages sit.
"""
import argparse, json, collections, re, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BUILD = HERE / "build"

FLOP_TYPES = {"$dff","$adff","$dffe","$adffe","$sdff","$sdffe","$sdffce","$dffsr"}
MEM_TYPES  = {"$mem_v2","$mem","$meminit_v2"}
LATCH      = {"$dlatch","$adlatch"}
# clock/reset/enable nets are control, not datapath -- they would connect
# everything to everything and destroy the staging.
CTRL_RE = re.compile(r"(^|_)(a?clk|clock|.*rst.*|.*reset.*|aresetn)($|_)", re.I)


FLAT_YS = """\
read_verilog {flat}
hierarchy -top {top} -check
proc
flatten
opt_expr
opt_clean
memory_collect
memory -nomap
wreduce
write_json {json_out}
"""


def load(top):
    """Elaborate a FLATTENED netlist for this module.

    The mux-level view deliberately does NOT flatten -- it wants the original
    instance names. The latency view MUST, and this bit me: a parameterised
    submodule instance has a Yosys cell type of `$paramod\\<name>\\<params>`,
    which starts with '$' and so slipped past every "is this a primitive"
    check. Instances were walked as if COMBINATIONAL, so every register inside
    a child module vanished and hierarchical blocks under-reported their
    latency -- pumice_bank_timers read 0 registers / depth 0, which is plainly
    impossible for a timer. Flattening removes the whole class of error rather
    than adding another type check.

    Reuses the sv2v output gen_schematics.py already produced.
    """
    flat_json = BUILD / f"{top}.flat.json"
    src_v = BUILD / f"{top}.v"
    if not src_v.exists():
        sys.exit(f"no {src_v} -- run gen_schematics.py --module {top} first "
                 f"(it runs sv2v and leaves the flattened Verilog here)")
    if not flat_json.exists() or flat_json.stat().st_mtime < src_v.stat().st_mtime:
        ys = BUILD / f"{top}.flat.ys"
        ys.write_text(FLAT_YS.format(flat=src_v, top=top, json_out=flat_json))
        r = subprocess.run(["yosys", "-q", "-s", str(ys)],
                           capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit(f"yosys (flatten) failed for {top}: "
                     f"{r.stderr.strip().splitlines()[-1:]}")
    mods = json.loads(flat_json.read_text())["modules"]
    if top not in mods:
        sys.exit(f"{top} not in the flattened JSON (got {list(mods)[:4]})")
    m = mods[top]
    leftover = sorted({c["type"] for c in m.get("cells", {}).values()
                       if c["type"].startswith("$paramod") or
                       not c["type"].startswith("$")})
    if leftover:
        print(f"[warn] {top}: unflattened instances remain, latency will be "
              f"UNDER-reported for paths through them: {leftover[:4]}")
    return m


def build_graph(mod):
    """-> (nodes, edges, kind) over STATE only.

    nodes: set of labels. kind[label] in {'in','out','flop','mem'}.
    edges: set of (src_label, dst_label) meaning src reaches dst through
           combinational logic only.
    """
    cells, netnames, ports = mod["cells"], mod.get("netnames", {}), mod.get("ports", {})

    driver = {}                       # bit -> ("cell"|"port", name)
    for cn, c in cells.items():
        dirs = c.get("port_directions", {})
        for pn, bits in c["connections"].items():
            if dirs.get(pn) == "output":
                for b in bits:
                    if isinstance(b, int):
                        driver[b] = ("cell", cn)
    for pn, p in ports.items():
        if p["direction"] in ("input", "inout"):
            for b in p["bits"]:
                if isinstance(b, int):
                    driver[b] = ("port", pn)

    bitname = {}
    for nn, info in netnames.items():
        for b in info["bits"]:
            if isinstance(b, int):
                bitname.setdefault(b, nn)

    kind = {}

    def is_state(k, name):
        return k == "port" or cells[name]["type"] in FLOP_TYPES | MEM_TYPES | LATCH

    def label(k, name):
        if k == "port":
            kind[name] = "in" if ports[name]["direction"] != "output" else "out"
            return name
        t = cells[name]["type"]
        if t in MEM_TYPES:
            nm = name.strip("$").split("$")[0] or name
            kind[nm] = "mem"
            return nm
        q = cells[name]["connections"].get("Q", [])
        nm = next((bitname[b] for b in q if b in bitname), name)
        # strip a bit-select so r_bank[2] and r_bank[0] merge
        nm = re.sub(r"\[\d+(:\d+)?\]$", "", nm)
        kind.setdefault(nm, "latch" if t in LATCH else "flop")
        return nm

    def cone_sources(start_bits):
        """State labels reachable backwards through combinational logic."""
        srcs, seen = set(), set()

        def walk(cellname):
            if cellname in seen:
                return
            seen.add(cellname)
            c = cells[cellname]
            dirs = c.get("port_directions", {})
            for pn, bits in c["connections"].items():
                if dirs.get(pn) == "output":
                    continue
                for b in bits:
                    if not isinstance(b, int):
                        continue
                    dr = driver.get(b)
                    if dr is None:
                        continue
                    k, nm = dr
                    if is_state(k, nm):
                        lb = label(k, nm)
                        if not CTRL_RE.search(lb):
                            srcs.add(lb)
                    else:
                        walk(nm)

        for b in start_bits:
            dr = driver.get(b)
            if dr is None:
                continue
            k, nm = dr
            if is_state(k, nm):
                lb = label(k, nm)
                if not CTRL_RE.search(lb):
                    srcs.add(lb)
            else:
                walk(nm)
        return srcs

    edges = set()
    for cn, c in cells.items():
        if c["type"] in FLOP_TYPES | LATCH:
            dst = label("cell", cn)
            if CTRL_RE.search(dst):
                continue
            for s in cone_sources(c["connections"].get("D", [])):
                if s != dst:
                    edges.add((s, dst))
        elif c["type"] in MEM_TYPES:
            dst = label("cell", cn)
            bits = []
            for pn, bb in c["connections"].items():
                if pn.startswith("WR_") and isinstance(bb, list):
                    bits += [b for b in bb if isinstance(b, int)]
            for s in cone_sources(bits):
                if s != dst:
                    edges.add((s, dst))
    for pn, p in ports.items():
        if p["direction"] == "output":
            dst = label("port", pn)
            if CTRL_RE.search(dst):
                continue
            for s in cone_sources(p["bits"]):
                if s != dst:
                    edges.add((s, dst))

    nodes = set(kind) | {a for a, _ in edges} | {b for _, b in edges}
    for n in nodes:
        kind.setdefault(n, "flop")
    nodes = {n for n in nodes if not CTRL_RE.search(n)}
    edges = {(a, b) for a, b in edges if a in nodes and b in nodes}
    return nodes, edges, kind


def sccs(nodes, edges):
    """Tarjan -> list of components (feedback loops condense to one node)."""
    adj = collections.defaultdict(list)
    for a, b in edges:
        adj[a].append(b)
    index, low, onstk, stk, out = {}, {}, set(), [], []
    counter = [0]
    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(adj[root]))]
        index[root] = low[root] = counter[0]; counter[0] += 1
        stk.append(root); onstk.add(root)
        while work:
            v, it = work[-1]
            adv = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]; counter[0] += 1
                    stk.append(w); onstk.add(w)
                    work.append((w, iter(adj[w])))
                    adv = True
                    break
                if w in onstk:
                    low[v] = min(low[v], index[w])
            if adv:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stk.pop(); onstk.discard(w); comp.append(w)
                    if w == v:
                        break
                out.append(comp)
    return out


def stage_ranks(nodes, edges, kind):
    """Longest flop-distance from any input, over the SCC condensation."""
    comps = sccs(nodes, edges)
    cid = {n: i for i, c in enumerate(comps) for n in c}
    looped = {i for i, c in enumerate(comps) if len(c) > 1}
    cadj = collections.defaultdict(set)
    indeg = collections.Counter()
    for a, b in edges:
        if cid[a] != cid[b]:
            if cid[b] not in cadj[cid[a]]:
                cadj[cid[a]].add(cid[b]); indeg[cid[b]] += 1
    order, q = [], [i for i in range(len(comps)) if indeg[i] == 0]
    while q:
        i = q.pop()
        order.append(i)
        for j in cadj[i]:
            indeg[j] -= 1
            if indeg[j] == 0:
                q.append(j)
    rank = {i: 0 for i in range(len(comps))}
    for i in order:
        for j in cadj[i]:
            # crossing INTO a flop/mem costs a clock; into an output port does not
            cost = 1 if any(kind.get(n) in ("flop", "mem", "latch") for n in comps[j]) else 0
            rank[j] = max(rank[j], rank[i] + cost)
    return {n: rank[cid[n]] for n in nodes}, cid, looped, comps


def latency_table(nodes, edges, kind, cid, comps, looped):
    """(src, dst, min_flops, max_flops, loop) per input->output pair.

    min is a shortest-path on flop cost. max is a longest path over the SCC
    CONDENSATION -- a register inside a feedback loop would make a plain
    longest path infinite, so a path through a non-trivial SCC is reported as
    a lower bound and flagged.
    """
    adj = collections.defaultdict(list)
    for a, b in edges:
        adj[a].append(b)
    cadj = collections.defaultdict(set)
    for a, b in edges:
        if cid[a] != cid[b]:
            cadj[cid[a]].add(cid[b])
    ccost = {i: (1 if any(kind.get(n) in ("flop", "mem", "latch") for n in c) else 0)
             for i, c in enumerate(comps)}

    ins = sorted(n for n in nodes if kind.get(n) == "in")
    outs = {n for n in nodes if kind.get(n) == "out"}
    rows = []
    for src in ins:
        best = {src: 0}
        dq = collections.deque([src])
        while dq:
            v = dq.popleft()
            for w in adj[v]:
                c = best[v] + (1 if kind.get(w) in ("flop", "mem", "latch") else 0)
                if w not in best or c < best[w]:
                    best[w] = c
                    dq.append(w)
        # longest path on the condensation, memoised, from src's component
        memo, onloop = {}, {}

        def lp(i):
            if i in memo:
                return memo[i], onloop[i]
            memo[i], onloop[i] = 0, False
            bestv, bl = 0, False
            for j in cadj[i]:
                d, l = lp(j)
                d += ccost[j]
                if d > bestv:
                    bestv, bl = d, l or (j in looped)
            memo[i], onloop[i] = bestv, bl or (i in looped)
            return memo[i], onloop[i]

        for o in sorted(outs & set(best)):
            # longest path is measured on the condensation from src to o's comp
            mx, lp_flag = lp(cid[src])
            rows.append((src, o, best[o], max(mx, best[o]), lp_flag))
    return rows


def render(top, nodes, edges, kind, rank, looped, cid, comps, out_png, max_nodes,
           no_feedback=False):
    if len(nodes) > max_nodes:
        print(f"[warn] {top}: {len(nodes)} state nodes > --max-nodes {max_nodes}; "
              f"picture skipped (table still printed). Narrow with --from/--to/--only.")
        return 0
    by_stage = collections.defaultdict(list)
    for n in nodes:
        by_stage[rank[n]].append(n)
    NL = "\\l"
    L = ['digraph G {', '  rankdir=LR;', '  splines=ortho;',
         '  node [shape=box,fontname="monospace",fontsize=9,margin="0.06,0.03"];',
         '  edge [color="#555555",arrowsize=0.6];',
         '  graph [nodesep=0.18,ranksep=1.1,fontname="monospace",'
         f'label="{top} -- one column = one clock; count columns for latency",'
         '  labelloc=t,fontsize=13];']
    COLOR = {"in": "#d7f0d7", "out": "#f0d7d7", "flop": "#cfe8ff",
             "mem": "#ffe2b0", "latch": "#ffd0f0"}
    for st in sorted(by_stage):
        L.append(f'  subgraph cluster_s{st} {{ label="stage {st}"; '
                 f'style=dashed; color="#999999"; fontsize=11;')
        for n in sorted(by_stage[st]):
            k = kind.get(n, "flop")
            loop = " *" if cid[n] in looped else ""
            L.append(f'    "{n}" [style=filled,fillcolor="{COLOR.get(k,"#eeeeee")}",'
                     f'label="{n}{loop}{NL}"];')
        L.append('  }')
    for a, b in sorted(edges):
        back = rank[a] >= rank[b]
        if back and no_feedback:
            continue
        same = " [constraint=false,color=\"#cccccc\",style=dashed]" if back else ""
        L.append(f'  "{a}" -> "{b}"{same};')
    L.append('}')
    dot = out_png.with_suffix(".dot")
    dot.write_text("\n".join(L))
    subprocess.run(["dot", "-Tpng", "-o", str(out_png), str(dot)], check=True)
    dot.unlink(missing_ok=True)
    return len(nodes)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--module", required=True)
    ap.add_argument("--from", dest="src", help="regex: keep only these input ports")
    ap.add_argument("--to", dest="dst", help="regex: keep only these output ports")
    ap.add_argument("--only", help="regex: keep only nodes matching")
    ap.add_argument("--hide", help="regex: drop nodes matching")
    ap.add_argument("--max-nodes", type=int, default=120)
    ap.add_argument("--table-only", action="store_true")
    ap.add_argument("--no-feedback", action="store_true",
                    help="drop backward edges from the PICTURE (they are the "
                         "loops; latency is unaffected and it declutters a lot)")
    ap.add_argument("--min-flops", type=int, default=0,
                    help="hide paths with fewer flops (1 = drop the "
                         "combinational feedthroughs)")
    a = ap.parse_args()

    mod = load(a.module)
    nodes, edges, kind = build_graph(mod)

    def keep(n):
        if a.only and not re.search(a.only, n):
            return False
        if a.hide and re.search(a.hide, n):
            return False
        if a.src and kind.get(n) == "in" and not re.search(a.src, n):
            return False
        if a.dst and kind.get(n) == "out" and not re.search(a.dst, n):
            return False
        return True

    nodes = {n for n in nodes if keep(n)}
    edges = {(x, y) for x, y in edges if x in nodes and y in nodes}

    rank, cid, looped, comps = stage_ranks(nodes, edges, kind)
    rows = latency_table(nodes, edges, kind, cid, comps, looped)

    nflop = sum(1 for n in nodes if kind.get(n) in ("flop", "mem", "latch"))
    depth = max(rank.values()) if rank else 0
    print(f"\n=== {a.module}: {len(nodes)} state nodes ({nflop} registers/mems), "
          f"pipeline depth {depth} clocks ===")
    reg = [r for r in rows if r[2] >= max(1, a.min_flops)]
    comb = [r for r in rows if r[2] == 0 and a.min_flops == 0]
    if reg:
        w1 = max(len(r[0]) for r in reg); w2 = max(len(r[1]) for r in reg)
        print(f"\nREGISTERED paths -- flops from input to output:")
        print(f"{'input':<{w1}}  {'output':<{w2}}   min   max")
        print(f"{'-'*w1}  {'-'*w2}  ----  ----")
        for s, o, mn, mx, fl in sorted(reg, key=lambda r: (-r[2], r[0], r[1])):
            note = "  >= (feedback loop on the longest path)" if fl else ""
            mxs = f"{mx:>4}" if mx != mn else "   ="
            print(f"{s:<{w1}}  {o:<{w2}}  {mn:>4}  {mxs}{note}")
    if comb:
        byo = collections.defaultdict(list)
        for s, o, _, _, _ in comb:
            byo[o].append(s)
        print(f"\nCOMBINATIONAL feedthroughs (0 flops) -- {len(comb)} pairs, "
              f"{len(byo)} outputs. These are the timing paths, not latency:")
        for o in sorted(byo):
            srcs = sorted(byo[o])
            shown = ", ".join(srcs[:5]) + (f" (+{len(srcs)-5})" if len(srcs) > 5 else "")
            print(f"  {o} <- {shown}")
    if not reg and not comb:
        print("(no input-port -> output-port path survived the filters)")
    if looped:
        names = sorted(n for n in nodes if cid[n] in looped)
        print(f"\nfeedback loops (marked * in the picture): {', '.join(names[:12])}"
              + (f" (+{len(names)-12})" if len(names) > 12 else ""))

    if a.table_only:
        return 0
    out = HERE / f"{a.module}.latency.png"
    n = render(a.module, nodes, edges, kind, rank, looped, cid, comps, out, a.max_nodes,
               no_feedback=a.no_feedback)
    if n:
        print(f"\n[ok] {out.name}  {n} nodes, {depth} stages, "
              f"{out.stat().st_size/1024:.0f} KB")
    return 0


if __name__ == "__main__":
    sys.exit(main())
