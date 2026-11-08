# ISSUE-001: the Vivado flow defines no `XILINX` macro, so every `ifdef XILINX (* ram_style *)` is dead on the board

**Priority:** P3
**Status:** OPEN
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

## Resolves into

A tooling task if the flow defines the macro, or a cache-ip task if the
attributes go unconditional. Owner's call.
