# pumice schematics

Two views of the same Yosys word-level netlist. Both read the RTL through the
project filelists and stop after `proc` (no techmap/abc), so what you see maps
back to the SystemVerilog, not to LUTs.

## 1. Mux-level schematics -- `gen_schematics.py`

Every `$mux`/`$eq`/`$add`/... cell drawn with netlistsvg. Faithful but dense:
for a big block (the arbiter is ~6500 cells) it is an unreadable hairball. Use
it to trace one specific signal, not to read the whole module.

    python3 gen_schematics.py --module pumice_page_policy

Emits `<module>.png` here and the Yosys JSON under `build/<module>.json`.

## 2. Register-transfer dataflow -- `gen_dataflow.py`

The readable view. Nodes are STATE (flops, memories, ports). Every deep
combinational cone feeding a register is collapsed into ONE box that says how
many logic levels it is and what it computes (op histogram) plus the registers
that feed it:

    [ depth 81: 437 mux, 302 and, 290 eq | from: cmd_bank_o, r_bank_act_ready, ... ] --> rd_act_s

`--min-depth N` keeps only cones at least N levels deep (the timing-critical
ones); `--top K` keeps the K deepest. Consumes the `build/<module>.json` that
`gen_schematics.py` already produced.

    python3 gen_dataflow.py --module pumice_cmd_arbiter --min-depth 3 --top 40

Emits `<module>.dataflow.png`. Modules with no cone deeper than `--min-depth`
emit nothing (they have no interesting paths).

## 3. Latency / pipeline stages -- `gen_latency.py`

The view for "how many flops from here to there". The other two answer
different questions: gen_schematics draws every cell (faithful, hairball above
~1200), gen_dataflow tags each combinational cone with its DEPTH (a TIMING
question). Neither counts clocks.

This one prunes BY CONSTRUCTION rather than by filtering -- the only nodes are
STATE (flops, memories, ports), and combinational logic is never drawn, it IS
the edge. A hairball is impossible: the arbiter goes from 6500 cells to 173
state nodes. Registers merge by the net name on Q, so a bit-blasted
`r_bank[2:0]` is one node.

Nodes are ranked into columns by flop-distance from the inputs, so **one column
= one clock; count the columns**. Feedback loops are condensed (Tarjan SCC) so a
self-feeding register does not make the longest path infinite; nodes inside a
loop are marked `*`.

    python3 gen_latency.py --module pumice_cmd_arbiter --min-flops 1
    python3 gen_latency.py --module pumice_rd_return_ring --no-feedback

Prints a latency TABLE (input -> output, min/max flops) and emits
`<module>.latency.png`. The table is the artifact that cannot be misread; the
picture shows where the stages sit. Pruning knobs: `--from`/`--to` (port
regexes), `--only`/`--hide` (node regex), `--no-feedback` (drop backward edges
from the picture), `--min-flops 1` (drop the combinational feedthroughs),
`--max-nodes` (picture is skipped above it; the table still prints).

Combinational feedthroughs are reported separately and named -- those are the
timing paths, not latency.

Whole-design profile (2026-09-09): page_policy 7 clocks, rbl_table 6,
cmd_arbiter 4, rd_return_ring 4, wr_data_cam 4, bank_timers 3, refresh_ctrl 3,
rd_cmd_cam 2, dfi_cdc 1; addr_mapper / dfi_cmd_formatter / wr_intake are purely
combinational (0).

## The skin -- `make_skin.py`

netlistsvg's shipped skin is missing symbols for ~13% of the cells this design
actually contains, and worse, it ALIASES `$pmux` ONTO THE 2:1 MUX SYMBOL -- so
every `case` statement was drawn as a two-input mux, which misrepresents the
netlist rather than merely looking plain.

`make_skin.py` copies the installed default and applies a documented set of
edits, so `diff skin/default.svg skin/rds-skin.svg` shows exactly what RDS
changed and an upstream netlistsvg bump is a re-run, not a merge. Chosen from a
cell histogram of the FUBs (34508 cells), not from taste:

| cell | share | what the default did |
|---|---|---|
| `$pmux` | 1.9% | drawn as a 2:1 mux -- now a tall `1-hot case` symbol |
| `$mux` | 32.6% | tiny -- enlarged, plus a heavy-stroke `$mux-bus` for datapath |
| `$adff` | 2.3% | generic box -- now marked `aRST` with a doubled edge |
| `$eqx` | 4.8% | generic box |
| `$reduce_and/or/bool` | 3.1% | generic box |
| `$shiftx/$shift` | 2.6% | generic box |
| `$mul`, `$neg`, `$mem_v2` | <1% | generic box; mem now filled distinctly |

The generic fallback is deliberately garish pink: anything still pink needs a
symbol.

    python3 make_skin.py          # -> skin/rds-skin.svg + skin/default.svg

`gen_schematics.py` picks the skin up automatically and warns if it is missing.

## Regenerating everything

    python3 make_skin.py
    for m in build/*.json; do m=$(basename $m .json)
      python3 gen_schematics.py --module $m
      python3 gen_dataflow.py  --module $m --min-depth 3 --top 40
      python3 gen_latency.py   --module $m --no-feedback
    done

`build/` is git-ignored; the committed PNGs are the artifacts.
