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

## Regenerating everything

    for m in build/*.json; do m=$(basename $m .json)
      python3 gen_schematics.py --module $m
      python3 gen_dataflow.py  --module $m --min-depth 3 --top 40
    done

`build/` is git-ignored; the committed PNGs are the artifacts.
