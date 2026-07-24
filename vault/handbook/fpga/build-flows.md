---
title: Build flows
summary: Vivado non-project batch flow, board switches, bitstream naming.
---

# Build flows

- Non-project batch Tcl driven by per-flow Makefiles
  (flows-*/tcl/{create_project,build_all,program_fpga}.tcl). Pattern
  reference: stream flows-stream-bridge with BOARD=nexys|genesys2 - one
  flow, board-suffixed bitstreams, board serial baked into programming.
- A cocotb sim gate runs BEFORE Vivado (verify-sim): UART ping -> CSR
  round-trip. A build that skips it wastes hours on dead-on-arrival RTL.
- Long runs: background + log polling; place/route on a K325T takes tens
  of minutes - do not kill on a hunch. Monitor the log for the phase
  markers and Post Placement/Routing Timing Summary lines.
- Filelists resolve standalone (source env_python first); flow Makefiles
  may add flow-scoped vars but the .f files must not require them.
- Verilator sim of board tops: deep monitor tables need --unroll-count
  (default 64) - see [[timing-closure]] sibling gotchas.
