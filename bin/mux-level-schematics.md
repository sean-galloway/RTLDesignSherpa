# Mux-Level Schematic Generation

Automatic generation of readable, word-level schematics from SystemVerilog RTL.
Target abstraction: **muxes, flops, adders, comparators, and memories as boxes** —
above raw gates, below opaque block diagrams. You can trace a datapath; you are not
staring at 4000 NAND2s.

Pipeline:

```
SystemVerilog  ->  Yosys (stop after `proc`)  ->  JSON netlist
                                                      |
                                                      v
                                        netlistsvg + custom skin
                                                      |
                                                      v
                                                    SVG / PDF
```

Layout and routing are done by **ELK** (Eclipse Layout Kernel), which netlistsvg
wraps via `elkjs`. ELK's layered algorithm does orthogonal edge routing with
port-side constraints, which is what makes the output look like a schematic rather
than a graph.

---

## 1. Prerequisites

```bash
# Yosys — 0.40+ recommended for SV coverage
sudo apt install yosys        # or build from source / oss-cad-suite

# netlistsvg (Node)
sudo apt install nodejs npm
npm install -g netlistsvg

# optional: SV fallback when Yosys chokes (you already have this for the SBY flow)
#   sv2v

# optional: SVG -> PDF for docs
sudo apt install librsvg2-bin    # provides rsvg-convert

# graphviz -- the dataflow and latency views lay out with `dot`, not ELK
sudo apt install graphviz
```

Verify:

```bash
yosys -V
netlistsvg --help
```

No Python packages are required. The driver script in §6 is stdlib-only.

---

## 2. Directory layout

IMPLEMENTED (2026-09-09) under the component rather than the repo root, since
the parameters and filelists are per-component:
`projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/schematics/`.
The layout below is the shape; substitute that path. Port it to a second
component by copying the four scripts and pointing them at its filelists.

```
<component>/rtl/schematics/
├── skin/
│   ├── rds-skin.svg          # custom skin (see §5)
│   └── default.svg           # pristine copy from netlistsvg, for diffing
├── params.json               # per-module elaboration parameters (see §4)
├── gen_schematics.py         # driver (see §6)
├── build/                    # intermediate .ys and .json — gitignored
└── out/                      # generated .svg — committed
```

`.gitignore`:

```
docs/schematics/build/
```

Commit `out/`. The whole point is that the diagrams are derived artifacts that
cannot drift from the RTL; having them in-tree makes drift visible in review as a
diff on the SVG.

---

## 3. The Yosys script

This is the core of the flow. Per module:

```tcl
# --- read ---
read_verilog -sv -I rtl/common rtl/common/*.sv

# --- elaborate one module with concrete parameters ---
hierarchy -top ${TOP} -check ${CHPARAM}

# --- lower behavioural code to word-level cells ---
proc                # always blocks -> $mux / $pmux / $dff / $adff
opt_expr            # constant folding only; structurally harmless
opt_clean           # remove dangling wires and unused cells

# --- keep memories as boxes, not exploded flop arrays ---
memory_collect
memory -nomap

# --- optional: trim provably-dead upper bits, tightens bus labels ---
wreduce

# --- emit ---
write_json ${BUILD}/${TOP}.json
```

### Why it stops there

`proc` is the pass that converts decision trees into multiplexers. Before it, the
logic is still trapped inside Yosys `process` objects and won't render as anything
useful. After it, you have exactly the cell types you want to see.

Everything downstream of `proc` trades readability for implementation detail.

### Passes to never run in this flow

| Pass | What it costs you |
|---|---|
| `flatten` | Submodule boundaries vanish; one giant unreadable page |
| `techmap`, `simplemap` | A 32-bit `$mux` shatters into 32 bit-level `$_MUX_` cells |
| `abc`, `abc9` | Full gate mapping; datapath structure is gone entirely |
| `aigmap` | Everything becomes AND/NOT |
| `splitnets` | Buses split into individual wires — you lose the fat datapath lines |
| `opt` (full) | Runs `opt_muxtree` + `opt_merge`, which collapse and dedup exactly the mux trees you are trying to look at |
| `fsm` | Re-encodes state machines; diagram no longer matches your source encoding |
| `memory_map` | RAMs explode into flop arrays |

`opt_expr` and `opt_clean` are the only safe optimizations. Use them individually,
never the `opt` umbrella.

### Hierarchy control

By default `hierarchy` leaves submodules as instance boxes — no action needed.

To force a submodule to stay a box even under aggressive settings, mark it in
source:

```systemverilog
(* keep_hierarchy *)
module counter_bin #(parameter int WIDTH = 8) (...);
```

Or from the script, without touching RTL:

```tcl
setattr -mod -set keep_hierarchy 1 counter_bin
```

To go the other way — inline one specific submodule because it's the thing you're
documenting:

```tcl
flatten counter_bin
```

---

## 4. Parameter manifest

Yosys cannot elaborate a parameterized module without concrete values. Since
essentially everything in `rtl/common` is parameterized, the flow needs a manifest.

`docs/schematics/params.json`:

```json
{
  "_default": {},

  "gaxi_fifo_sync": {
    "DATA_WIDTH": 32,
    "DEPTH": 8
  },

  "gaxi_fifo_async": {
    "DATA_WIDTH": 32,
    "DEPTH": 8,
    "N_FLOP_CROSS": 2
  },

  "arbiter_round_robin": {
    "CLIENTS": 4
  },

  "counter_johnson": {
    "WIDTH": 4
  },

  "_skip": [
    "some_module_that_wont_elaborate"
  ]
}
```

Choose the **smallest parameter set that still shows the structure**. A depth-8
FIFO diagram and a depth-1024 FIFO diagram have identical topology; the first fits
on a page. This is a documentation artifact, not a synthesis run.

Parameters become `-chparam` arguments:

```tcl
hierarchy -top gaxi_fifo_sync -check -chparam DATA_WIDTH 32 -chparam DEPTH 8
```

---

## 5. The skin

The skin is an SVG file containing one `<g>` per cell symbol. netlistsvg matches
Yosys cell types against `<s:alias>` entries inside each group and stamps the
symbol into the layout at the coordinates ELK computed.

**Start by copying the shipped default**, then edit — the file documents its own
schema and the layout-engine properties block at the top is fiddly to reproduce
from scratch:

```bash
SKINDIR=$(dirname $(readlink -f $(which netlistsvg)))/../lib/netlistsvg/lib
cp "$SKINDIR/default.svg" docs/schematics/skin/default.svg
cp "$SKINDIR/default.svg" docs/schematics/skin/rds-skin.svg
```

(If that path doesn't resolve, `npm root -g` then look under
`netlistsvg/lib/`. The skins shipped are `default.svg`, `analog.svg`, and
usually a couple of variants.)

### Bus vs. single-bit muxes

netlistsvg appends `-bus` to the cell type when a cell has a `WIDTH` parameter
greater than 1, and this currently applies to `$mux` and its variants. So the skin
can carry two distinct mux symbols:

- `$mux` — thin stroke, 1-bit control path
- `$mux-bus` — heavy stroke, datapath

This single distinction does most of the visual work at this abstraction level.
Make the weight difference obvious (1px vs 2.5px) — at a glance you want control
and data to separate.

### `$pmux` — the one you must fix

`$pmux` is what `case` statements become.

**Correction (2026-09-09, from implementing this).** An earlier draft of this
section said `$pmux` is *not in the default skin* and renders as a generic
labelled rectangle. That is wrong, and the truth is worse. The shipped skin
carries `<s:alias val="$pmux"/>` **inside the 2:1 mux symbol group**, so every
`case` statement is drawn as a two-input mux with `A`/`B`/`S`. It does not look
unstyled, it looks *plausible and wrong* — an N-way one-hot select rendered as
a 2:1. In the pumice FUBs that is 669 cells silently misdrawn.

So the first edit is a **deletion**: remove the `$pmux` alias from the `mux`
group before adding the symbol below. A missing symbol is a visible TODO; a
wrong alias is a misread schematic.

A `$pmux` has:
- `A` — the default/fallthrough input (width W)
- `B` — all case inputs concatenated (width W × N)
- `S` — one-hot select (width N)
- `Y` — output (width W)

Sketch of the symbol group to add. Sizes and port coordinates need tuning against
your other symbols; treat the port `s:x`/`s:y` values as the thing you'll iterate
on:

```xml
<g s:type="pmux" s:width="30" s:height="70" transform="translate(200,50)">
  <s:alias val="$pmux"/>
  <s:alias val="$pmux-bus"/>

  <!-- tall trapezoid, wide edge on the input side -->
  <path d="M0,0 L30,12 L30,58 L0,70 Z"
        style="fill:none;stroke:#000;stroke-width:2.5"/>

  <text x="15" y="40" text-anchor="middle"
        style="font-size:9px;font-family:monospace">1-hot</text>

  <g s:x="0"  s:y="10" s:pid="A"/>
  <g s:x="0"  s:y="35" s:pid="B"/>
  <g s:x="15" s:y="66" s:pid="S"/>
  <g s:x="30" s:y="35" s:pid="Y"/>
</g>
```

### Which symbols to add — measure, don't guess

Histogram the cells the design actually contains before drawing anything.
Across the pumice FUBs (34508 cells) the default skin has **no symbol for
about 13%**, so they render as anonymous rectangles:

| Cell | Share | Default skin |
|---|---|---|
| `$mux` | 32.6% | present, but tiny; add a heavy-stroke `$mux-bus` for datapath |
| `$eqx` | 4.8% | **missing** |
| `$reduce_and` / `$reduce_or` / `$reduce_bool` | 3.1% | **missing** (only the `nor`/`xnor`/`xor` reductions ship) |
| `$adff` / `$adffe` / `$dffsr` | 2.3% | **missing** — and this is the async-reset flop, the thing a CDC review most needs to see |
| `$shiftx` / `$shift` | 2.6% | **missing** — how a variable index into a packed vector lands |
| `$pmux` | 1.9% | present but **aliased onto the 2:1 mux** (see above) |
| `$mul`, `$neg`, `$mem_v2` | <1% | **missing**; give memories a distinct fill |

Make the generic fallback slightly ugly on purpose — garish pink works. It is
your TODO list: anything still pink needs a symbol.

### Generate the skin, don't hand-maintain it

The default skin carries a style block and a layout-properties block that are
fiddly and that upstream changes. Copy the installed default and apply a
documented set of edits in a script (`make_skin.py`), so that:

* `diff skin/default.svg skin/rds-skin.svg` shows exactly what you changed;
* an upstream netlistsvg bump is a re-run, not a merge;
* the reason for each symbol is in the script next to the edit.

### Layout tuning

The skin's `<s:layoutEngine>` element passes options straight through to ELK. The
ones that matter most:

```
org.eclipse.elk.layered.spacing.nodeNodeBetweenLayers   # horizontal breathing room
org.eclipse.elk.spacing.nodeNode                        # vertical
org.eclipse.elk.direction                               # RIGHT for datapath L->R
org.eclipse.elk.layered.mergeEdges                      # bundles fanout, big win
```

Increase the layer spacing before you do anything else — the default is tight and
routed buses need room to be legible.

---

## 6. Driver script

`docs/schematics/gen_schematics.py` — stdlib only, no venv needed.

```python
#!/usr/bin/env python3
"""Generate mux-level schematics for RTL modules via Yosys + netlistsvg."""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
BUILD = HERE / "build"
OUT = HERE / "out"
SKIN = HERE / "skin" / "rds-skin.svg"

YOSYS_TEMPLATE = """\
read_verilog -sv {incdirs} {sources}
hierarchy -top {top} -check {chparam}
proc
opt_expr
opt_clean
memory_collect
memory -nomap
wreduce
write_json {json_out}
"""

MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z_]\w*)", re.MULTILINE)


def discover_modules(rtl_dir):
    """Map module name -> defining file."""
    found = {}
    for sv in sorted(rtl_dir.rglob("*.sv")):
        text = sv.read_text(errors="replace")
        for name in MODULE_RE.findall(text):
            found.setdefault(name, sv)
    return found


def build_one(top, sources, incdirs, params, keep_going):
    BUILD.mkdir(parents=True, exist_ok=True)
    OUT.mkdir(parents=True, exist_ok=True)

    chparam = " ".join(f"-chparam {k} {v}" for k, v in params.items())
    json_out = BUILD / f"{top}.json"
    svg_out = OUT / f"{top}.svg"

    script = YOSYS_TEMPLATE.format(
        incdirs=" ".join(f"-I {d}" for d in incdirs),
        sources=" ".join(str(s) for s in sources),
        top=top,
        chparam=chparam,
        json_out=json_out,
    )
    script_path = BUILD / f"{top}.ys"
    script_path.write_text(script)

    r = subprocess.run(
        ["yosys", "-q", "-s", str(script_path)],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        msg = f"[yosys FAIL] {top}\n{r.stderr.strip()}"
        if keep_going:
            print(msg, file=sys.stderr)
            return False
        raise SystemExit(msg)

    cmd = ["netlistsvg", str(json_out), "-o", str(svg_out)]
    if SKIN.exists():
        cmd += ["--skin", str(SKIN)]

    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        msg = f"[netlistsvg FAIL] {top}\n{r.stderr.strip()}"
        if keep_going:
            print(msg, file=sys.stderr)
            return False
        raise SystemExit(msg)

    size_kb = svg_out.stat().st_size / 1024
    flag = "  <-- LARGE, consider decomposing" if size_kb > 250 else ""
    print(f"[ok] {top:<40} {size_kb:7.1f} KB{flag}")
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rtl", default="rtl/common",
                    help="RTL directory, relative to repo root")
    ap.add_argument("--module", action="append",
                    help="specific module(s); default is all discovered")
    ap.add_argument("--params", default=str(HERE / "params.json"))
    ap.add_argument("--keep-going", action="store_true")
    args = ap.parse_args()

    rtl_dir = (REPO / args.rtl).resolve()
    if not rtl_dir.is_dir():
        raise SystemExit(f"no such directory: {rtl_dir}")

    manifest = json.loads(Path(args.params).read_text()) \
        if Path(args.params).exists() else {}
    skip = set(manifest.get("_skip", []))
    default_params = manifest.get("_default", {})

    sources = sorted(rtl_dir.rglob("*.sv"))
    incdirs = sorted({p.parent for p in sources})

    modules = args.module or sorted(discover_modules(rtl_dir))

    ok = fail = 0
    for top in modules:
        if top in skip:
            print(f"[skip] {top}")
            continue
        params = manifest.get(top, default_params)
        if build_one(top, sources, incdirs, params, args.keep_going):
            ok += 1
        else:
            fail += 1

    print(f"\n{ok} generated, {fail} failed")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
```

Usage:

```bash
# everything in rtl/common, don't stop on the first failure
python3 docs/schematics/gen_schematics.py --keep-going

# one module while you iterate on its skin symbols
python3 docs/schematics/gen_schematics.py --module gaxi_fifo_async
```

---

## 7. Makefile integration

```makefile
SCHEM_DIR := docs/schematics

.PHONY: schematics schematics-clean schematics-pdf

schematics:
	python3 $(SCHEM_DIR)/gen_schematics.py --keep-going

schematics-pdf: schematics
	@for f in $(SCHEM_DIR)/out/*.svg; do \
		rsvg-convert -f pdf -o "$${f%.svg}.pdf" "$$f"; \
	done

schematics-clean:
	rm -rf $(SCHEM_DIR)/build $(SCHEM_DIR)/out
```

### CI drift check

Regenerate and fail if anything changed — this is what keeps the diagrams honest:

```yaml
- name: Schematics up to date
  run: |
    make schematics
    git diff --exit-code docs/schematics/out/
```

---

## 8. Reading the output

A few things to expect the first time:

- **`$pmux` with a very wide `B` port.** Normal. `B` carries all case arms
  concatenated, so a 4-way 32-bit case gives `B` a width of 128. The bus label
  will look alarming; it isn't.
- **`$eq` cells feeding `$pmux.S`.** These are the case-item comparisons. They are
  your decision points, and worth styling distinctly.
- **`$adff` vs `$dff`.** If you expected async reset and see `$dff`, your reset
  isn't in the sensitivity list the way you think it is. This flow is a decent
  passive lint for that.
- **Dangling rhombus shapes.** Unconnected or `public`-named wires. Often a
  genuine unused signal.
- **A `$mem_v2` box with many ports.** Correct for multi-port structures; if the
  port count surprises you, that's worth a look.

---

## 9. The latency view — counting flops

The mux-level view is faithful and the dataflow view tags each combinational
cone with its depth, which is a **timing** question. Neither answers "how many
flops from here to there", which is a **latency** question, and neither can be
filtered into answering it — the thing you want to count is not in the picture.

The fix is not a better filter, it is a different node set. Draw **only state**
— flops, memories, ports. Combinational logic is never drawn; it *is* the edge.
This prunes **by construction**: a hairball is impossible because the node count
is the number of registers, not the number of cells. The pumice arbiter goes
from 6500 cells to 173 state nodes.

Three details make it readable:

* **Merge bit-blasted registers** by the net name on `Q`, so `r_bank[2:0]` is
  one node and not three.
* **Rank into columns** by flop-distance from the input ports. One column is one
  clock, so you count columns. Emit each column as a Graphviz cluster with
  `rank=same`.
* **Condense feedback** with Tarjan SCC before ranking. Without it a register
  that feeds itself makes the longest path infinite. Mark nodes inside a loop.

Drop clock and reset nets by name before building the graph — they connect
everything to everything and destroy the staging.

Emit a **table as well as a picture**. The table is the artifact that cannot be
misread, and it is what you actually cite:

```
=== pumice_rd_return_ring: 36 state nodes (18 registers), pipeline depth 4 clocks ===
input            output          min   max
dfi_ret_data_i   drain_data_o      3     =
```

Report **combinational feedthroughs separately**. A 0-flop input-to-output path
is not latency, it is a timing path (typically the ready/valid handshake), and
mixing the two buries the real latencies under dozens of rows.

**Validate against structure you already know** before trusting it. The pumice
arbiter reports depth 4, which is its snapshot -> arg-select -> pre-pick ->
output-register pipeline; the return ring reports read data at 3 flops, which is
slot write -> BRAM -> skid. A latency tool that cannot reproduce a pipeline you
can count by hand is not yet a tool.

---

## 10. Page-size discipline

If a module's schematic doesn't fit a page at legible zoom, that is a decomposition
signal, not a rendering problem — or a signal that you want the latency view of
section 9, which does not have this failure mode at all. The generator flags anything over ~250 KB of SVG,
which correlates reasonably with "too much on one page."

When you want a page-sized slice out of a large module rather than splitting the
RTL, Yosys `select` walks logic cones and `submod` extracts them into standalone
modules you can render individually:

```tcl
# everything feeding output `y`, stopping at flop boundaries
select -set outstage y %ci2:+$dff[Q,D] %ci*:-$mux[S]:-$dff
submod -name outstage @outstage
write_json build/outstage.json
```

`%ci` walks backward through input cones; `%ci2` limits depth; `:-$dff` stops the
walk at flop boundaries. This is the manual escape hatch — useful for documenting
one pipeline stage of a large datapath.

---

## 11. Troubleshooting

**Yosys rejects SystemVerilog constructs.**
Interfaces, some package usage, and advanced `always_comb` patterns can fail. Fall
back to the same `sv2v` step already used in the formal flow:

```bash
sv2v -I rtl/common rtl/common/*.sv > build/flat.v
# then read_verilog build/flat.v  (no -sv)
```

Note that `sv2v` output loses some original signal names, so diagrams get uglier.
Prefer fixing the Yosys read where practical.

**`ERROR: Module ... referenced but not found`.**
A missing source file, or a module intended as a black box. For genuine black
boxes, declare them:

```tcl
read_verilog -lib rtl/common/stubs.v
```

**Everything renders as generic boxes.**
The skin isn't being found. Check the `--skin` path resolves; netlistsvg fails soft
here rather than erroring.

**Diagram is a hairball despite being a small module.**
Usually `opt_clean` didn't run, or `splitnets` snuck in via a copied script. Also
check you aren't reading a `flatten`ed intermediate.

**Is my skin at fault, or the tool?** Re-run the same JSON with no `--skin`.
If it fails identically on the stock skin the skin is innocent. Worth doing
before debugging your own SVG: `pumice_row_pred_table` throws
`RangeError: Maximum call stack size exceeded` inside netlistsvg on both.

**Three real front-end failures, each in a different tool** (pumice, 2026-09-09,
all pre-existing and none fixable in the skin):

| Module | Tool | Error |
|---|---|---|
| `init_sequencer` | sv2v | `error, called at src/Convert/Scoper.hs` |
| `pumice_cmd_history_checker` | yosys | `Non-constant function call in constant expression` — it is a DV checker, not synthesizable; don't render checkers |
| `pumice_row_pred_table` | netlistsvg | `RangeError: Maximum call stack size exceeded` |

The lesson is to report which stage failed per module rather than one count:
"5 failed" hides three unrelated causes.

**Ports appear on the wrong sides.**
ELK decides port sides from edge direction unless constrained. Set
`org.eclipse.elk.portConstraints=FIXED_SIDE` on the relevant symbols in the skin.

---

## 12. Suggested first run

```bash
mkdir -p docs/schematics/{skin,build,out}
# copy the driver and params.json into docs/schematics/
# copy the default skin per §5

# start with one known-good module before running the whole directory
python3 docs/schematics/gen_schematics.py --module counter_bin

# then the sweep
python3 docs/schematics/gen_schematics.py --keep-going
```

Expect the first sweep to have failures — mostly missing parameter entries. Fill in
`params.json` from the error output and re-run. Once it's clean, add the `$pmux`
symbol and iterate on the skin against your two or three most structurally
interesting modules.
