<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Pipeline Latency and Mux-Level Schematics

Every figure on this page is **derived from the elaborated netlist**, not
written by hand, so it cannot drift from the RTL without the generator
disagreeing. Regenerate with the commands in the last section; if a number here
disagrees with a fresh run, the page is stale and the run is right.

## How the numbers are obtained

Yosys elaborates each block and stops after `proc`, so the netlist is still
word-level (`$mux`, `$eq`, `$add`, `$dff`) and maps back to the SystemVerilog
rather than to LUTs. `gen_latency.py` then reduces that netlist to **state
only** — flops, memories and ports. Combinational logic is never a node; it is
the edge between two pieces of state. Nodes are ranked into columns by
flop-distance from the input ports, so **one column is one clock**.

Two properties matter for trusting the result:

* The netlist is **flattened** for this view. A parameterised submodule
  instance carries a Yosys type of `$paramod\<name>\<params>`, and treating
  that as a primitive makes its internal registers invisible — `mc_bank_timers`
  reported 0 registers and 0 clocks before flattening, which is impossible for
  a timer block. Flattening removes the class of error rather than adding
  another special case.
* **Feedback is condensed** (Tarjan SCC) before ranking. Without it any
  register that feeds itself makes the longest path infinite. A path whose
  longest route runs through a real loop is reported as a lower bound.

Clock and reset nets are excluded before the graph is built; they connect
everything to everything and would destroy the staging.

## Per-block pipeline depth

Depth is the longest flop-distance from an input port. Registers counts the
merged registers (a bit-blasted `r_bank[2:0]` is one), not raw flop cells.

> **Stale until regenerated (2026-10-13).** These numbers come from the last
> generator run, made against the pumice-local copies of these blocks before
> they moved into `common-ip` on 2026-10-10/11. The rows are labelled with the
> common-ip module each block became. `gen_schematics.py` / `gen_latency.py`
> resolve only pumice's own `rtl/filelists/{fub,macro}`, which no longer hold
> these blocks, so the table cannot be rerun until the generator learns the
> common-ip filelists. One row is already known to disagree with the RTL:
> `mc_xddr2_cmd_formatter` has strict-flop outputs, so it is not 0 clocks.

| Block | Depth (clocks) | Registers | State nodes |
|---|---|---|---|
| `mc_addr_mapper` | 0 | 0 | 8 |
| `mc_xddr2_cmd_formatter` | 0 | 0 | 17 |
| `mc_global_timers` | 1 | 5 | 24 |
| `mc_xddr2_mode_register` | 1 | 1 | 16 |
| `mc_dfi_cdc` | 2 | 53 | 78 |
| `mc_dfi_rd_aligner` | 2 | 3 | 14 |
| `mc_dfi_wr_serializer` | 2 | 2 | 12 |
| `mc_wr_splitter` | 2 | 13 | 51 |
| `mc_bank_timers` | 3 | 48 | 72 |
| `mc_cmd_arbiter` | 3 | 57 | 128 |
| `mc_rd_cmd_cam` | 3 | 11 | 49 |
| `mc_rd_intake` | 3 | 24 | 75 |
| `mc_xddr2_refresh_ctrl` | 3 | 6 | 26 |
| `mc_rd_return_ring` | 5 | 23 | 41 |
| `mc_wr_data_cam` | 5 | 60 | 120 |
| `mc_page_policy` | 7 | 39 | 70 |
| `mc_wr_intake` | 7 | 31 | 79 |

`mc_addr_mapper` is purely combinational: it transforms a request in place and
adds no clock. (The table also reports `mc_xddr2_cmd_formatter` as 0 clocks; see
the note above.) The two deepest live blocks are `mc_page_policy` and
`mc_wr_intake`.

### Retired blocks

Two history-based paging predictors were removed from the RTL in 2026-09 (TASK-011,
TASK-014) after measuring inert or harmful on silicon, and two more blocks were
removed on 2026-10-11 (`dfi_signal_pack`, whose register stage was dropped, and
`powerdown_ctrl`, which was never wired into the core). They are kept here as a
latency record for the pre-removal netlist only.

| Block | Depth (clocks) | Registers | State nodes | Status |
|---|---|---|---|---|
| `pumice_row_pred_table` | 4 | 8 | 18 | **RETIRED** — removed 2026-09-27 (TASK-014) |
| `pumice_rbl_table` | 6 | — | — | **RETIRED** — removed 2026-09-26 (TASK-011) |
| `dfi_signal_pack` | 0 | 0 | 24 | **RETIRED** — removed 2026-10-11 |
| `powerdown_ctrl` | 3 | 5 | 18 | **RETIRED** — removed 2026-10-11 |

## Datapath latencies worth knowing

Read return, the path that sets read bandwidth:

| Path | Flops |
|---|---|
| `dfi_ret_data_i` -> `drain_data_o` (return ring) | 3 |

That is slot write, then the block RAM, then the skid — the three register
boundaries the ring is built from.

Scheduling, from a CAM entry becoming schedulable to the command issuing:

| Path | Flops |
|---|---|
| `*_sch_*` / `bank_*_ready_i` -> `rd_issue_slot_o` | 3 |
| `*_sch_*` / `bank_*_ready_i` -> `wr_commit_slot_o` | 3 |

This is the arbiter's pick pipeline, and it is the reason strict in-order
scheduling costs bandwidth under the auto-precharge paging modes: those modes
need two dependent commands per access (activate, then column-with-
auto-precharge), so each access pays the pick-pipeline traversal twice. See the
scheduler chapter and pumice ISSUE-006 (was PUMICE-021).

## Combinational feedthroughs

A zero-flop input-to-output path is **not latency, it is a timing path** —
typically a ready/valid handshake. The generator reports these separately for
exactly that reason. In the return ring, for example, `alloc_ready_o`,
`issue_ready_o` and `dfi_ret_ready_o` are all combinational from their
respective valids. They belong in timing review, not in a latency budget.

## The schematics

Three views live in `rtl/schematics/`, each answering a different question:

| View | File | Question |
|---|---|---|
| Mux-level | `<block>.png` | what does this cell-for-cell look like |
| Dataflow | `<block>.dataflow.png` | which combinational cone is deep (timing) |
| Latency | `<block>.latency.png` | how many flops from here to there |

The mux-level view is faithful but becomes unreadable above roughly 1200 cells,
so the largest blocks are deliberately black-boxed rather than rendered into a
hairball. The latency view has no such limit, because its node count is the
number of registers rather than the number of cells.

Symbols come from a custom netlistsvg skin. The shipped default aliases the
one-hot case primitive onto the two-input mux symbol, so every `case` statement
rendered as a 2:1 mux, and it has no symbol at all for the async-reset flop —
the element a clock-domain review most needs to see. Both are fixed in
`skin/rds-skin.svg`.

## Regenerating

```bash
cd rtl/schematics
python3 make_skin.py                                   # once, or after an npm bump
python3 gen_schematics.py --module <block>             # mux-level + the Yosys JSON
python3 gen_dataflow.py   --module <block> --min-depth 3
python3 gen_latency.py    --module <block> --min-flops 1
```

`gen_latency.py` prunes with `--from` / `--to` (port regexes), `--only` /
`--hide` (node regex), `--no-feedback` (drop backward edges from the picture)
and `--max-nodes`. Above `--max-nodes` the picture is skipped and the table
still prints, which is the right behaviour for the largest blocks.
