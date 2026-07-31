---
title: Build flows
summary: Vivado non-project batch flow, board switches, bitstream naming.
---

# Build flows

## The global make infra

Flow logic lives in ONE place and every FPGA project reuses it -- the
`make/tests.mk` pattern (see [[test-runner]]) applied to board builds. Two files:

| File | Include when | Gives you |
|---|---|---|
| `make/fpga_flow.mk` | a build wants the whole flow | `project synth bitstream bitstream-ila lint program ports board-info boards sim run seq-list utilization timing clean clean-all help` |
| `make/fpga_board.mk` | a flow already owns its build recipes | the board half only: `program ports board-info boards` |

A build's Makefile is variables, not recipes:

```make
FLOW      := ddr2_char
TOP       := ddr2_char_top
FILELIST  := $(SELF_DIR)/rtl/filelists/ddr2_char_harness.f
SIM_TESTS := $(SELF_DIR)/dv/tests
SEQ_DIR   := $(SELF_DIR)/../bin
include $(RDS_ROOT)/make/fpga_flow.mk
```

Paths are derived (`fpga/tcl`, `fpga/bitstream`, `fpga/reports`, falling back to
the older flat layout so existing flows can adopt it without moving anything).
A build needing a different recipe overrides the VARIABLE (`BUILD_TCL := ...`),
not the rule. `make help` is generated from the `##` comments, so it cannot
drift from the real target set.

Reference: `projects/fpga-systems/NexysA7/pumice/` -- a per-build Makefile of
five variables, plus an area dispatcher (`make bitstream BUILD=litedram`,
`make ab` to run both builds back to back).

## Flow notes

- Non-project batch Tcl driven by the Makefiles above
  (`fpga/tcl/{create_project,build_all,synth_only,build_ila}.tcl`). There is no
  per-flow `program_fpga.tcl` any more -- programming is the board registry, see
  [[boards]].
- A cocotb sim gate runs BEFORE Vivado (verify-sim): UART ping -> CSR
  round-trip. A build that skips it wastes hours on dead-on-arrival RTL.
- Long runs: background + log polling; place/route on a K325T takes tens
  of minutes - do not kill on a hunch. Monitor the log for the phase
  markers and Post Placement/Routing Timing Summary lines.
- Filelists resolve standalone (source env_python first); flow Makefiles
  may add flow-scoped vars but the .f files must not require them.
- Verilator sim of board tops: deep monitor tables need --unroll-count
  (default 64) - see [[timing-closure]] sibling gotchas.
