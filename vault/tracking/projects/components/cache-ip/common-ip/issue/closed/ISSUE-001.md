# ISSUE-001: the Vivado flow defines no `XILINX` macro, so every `ifdef XILINX (* ram_style *)` is dead on the board

**Priority:** P3
**Status:** CLOSED 2026-11-10 -- owner decision: make the attributes unconditional; done in all 25 files repo-wide.
**Filed:** 2026-11-08, from the FPGA microarchitecture review (TASK-001).

## Observation

The Genesys2 filelists carry no `+define+XILINX`, and
`fpga/tcl/create_project.tcl` sets `verilog_define` only from the filelist.
So the `ifdef XILINX` guards around `(* ram_style = "..." *)` in the cache-ip
RTL (`l1_control`, `l1_data_array`, `l1_repl`, `l1_tag_array`, `jet_control`
x4, `jet_rsp_seq`, `jet_wb_buffer`) never compile on the board. Every RAM
mapping the review measured came from array shape alone, and the
`reset_sync` `max_fanout` attribute was made unconditional for that reason.

24 files repo-wide use the same guard, so this is not a cache-ip-only fix.

## Options

- Define `XILINX` in the shared Vivado flow (`create_project.tcl` or every
  board filelist). Wakes all 24 files' attributes at once; each needs a
  rebuild check because some may have been written against a different
  inference outcome.
- Make the synthesis attributes unconditional (Verilator and yosys ignore
  attributes they do not know). Per-file, reviewable, no global flip.
- Leave it. The arrays infer correctly by shape today; the guards are then
  documentation only and should say so.

## Resolution (2026-11-10)

Owner picked the second option. The 24 guard sites in 25 files are gone;
the Xilinx `(* ram_style *)` attribute and the Quartus `/* synthesis
ramstyle */` comment pragma now sit on the array unconditionally. Verilator,
yosys and Quartus ignore an attribute they do not know. Beyond the cache-ip
list above: the five shared FIFOs (`fifo_sync`, `fifo_async`,
`gaxi_fifo_sync`, `gaxi_fifo_async`, `gaxi_drop_fifo_sync`), the kestrel and
gatling register files and memories, `alu_infer_pwl`, `rapids_seq_g`,
`axi4_dwidth_converter_rd`, `rom`, `hpet_core`, `uart_16550_core`, and three
board-harness files (`alu_harness`, both `axi_response_delay`). Left alone:
`rtc_clk_mux` (its guard selects a vendor primitive, not an attribute -- the
one legitimate `ifdef`, and just as dead until a flow defines the macro) and
the deprecated `bridge_cam`.

Inert to simulation: Verilator's generated C++ for all 22 affected modules
is byte-identical before and after, except for source line numbers inside
assertion messages. All three cache-ip FULL regressions pass on the change
(common-ip 255/255, amber 121/121, jet 149/149). The 26 current formal
flats that carry one of these arrays (six on the edited modules, twenty on
modules that instantiate one of the FIFOs) were regenerated, each differing
only by the attribute on the same declaration, and re-proved.

Where the attributes now reach Vivado, measured same-tree before/after:

| Rig | Flow | Before | After |
|---|---|---|---|
| jet pair rig (Genesys2) | routed, bin 14 -> 15 | 21,730 LUT / 2,244 LUTRAM / 160 BRAM / 24,444 FF, WNS +0.347 | 21,508 / 2,254 / 160 / 24,268, WNS +0.128 |
| amber pair rig (Genesys2) | routed, bin 9 -> 10 | 17,165 / 1,648 / 160 / 19,699, WNS +0.722 | 16,984 / 1,658 / 160 / 19,521, WNS +0.424 |
| gatling build-bram (NexysA7) | synth | 2,070 / 0 / 17 / 1,736 | identical |
| kestrel build-bram (NexysA7) | synth | 1,747 / 48 / 4 / 1,051 | identical |
| alu-infer build-infer (NexysA7) | synth | 25,755 / 1,506 / 0 / 3,455 | 25,402 / 1,506 / 0 / 3,449 |
| STREAM build-perf (Genesys2) | synth | 62,639 / 6,574 / 26 / 55,434 | 62,632 / 6,566 / 26.5 / 55,429 |

On both cache-ip rigs the same thing happens: about 176 flops of one small
common-ip array become ten LUTRAMs, and the LUT count drops about 1% from
re-optimisation around it. STREAM is the one place a block-RAM count changes: its `sram_controller_unit`
is the only `FIFO_BRAM` user in the tree, and its `ram_style = "block"`
now reaches Vivado, so one small distributed array becomes a RAMB18 (+0.5
BRAM tile, -8 LUTRAM). Everything else the reviews measured was already
inferred by shape, which is what the observation said. WNS moves inside the 0.2 ns clock-uncertainty budget on
both rigs (placement noise, per the budget rule). alu-infer's LUT delta is
spread across modules that have no array in them, so it is Vivado
re-optimising a perturbed netlist, not an inference change; its LUTRAM count
is unchanged. Both boards: smoke PASS, from-reset disjoint CRCs identical to
the previous bin, all eleven sweep configurations identical to the previous
bin, unexpected 0.

The rule and this failure are in
`vault/handbook/design/sram-and-memories.md`.
