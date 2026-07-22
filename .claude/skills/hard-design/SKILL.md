---
name: hard-design
description: HARD RTL design guidelines - reset macros, CDC, valid/ready contracts, streaming no-FSM pattern, SRAM rules, sizing invariants, signal-naming audit. Use when writing or reviewing any RTL.
---

# HARD design guidelines

Authority: /GLOBAL_REQUIREMENTS.md (P0 items are enforced). This skill is the
working checklist; that file wins on conflict.

- Reset: `ALWAYS_FF_RST` / `RST_ASSERTED` macros (reset_defs.svh); aresetn
  active-low async. Never bare always_ff with manual reset in projects/.
- CDC: bin2gray/gray2bin + sync flops for pointers; cdc_* handshakes for
  events; NEVER sample a foreign-domain signal raw.
- valid/ready: valid may not retract once asserted until ready (AXI
  stability); a monitor/observer may gate COMMANDS only, never responses.
- Streaming datapaths: no FSM; skid-buffered pipelines with backpressure.
- SRAM modules: NO reset port; FPGA ram_style attributes; controllers own
  pointers/reset. Array syntax [DEPTH], never [0:DEPTH-1].
- Sizing invariants live in ONE place (localparam/package function), never
  duplicated in a comment ("keep in sync" comments are how the monitor
  wedge shipped). Shared-resource sizing = per-client limit x clients.
- Deep priority scans serialize: an N^2 loop with a found-flag synthesizes
  to a priority chain (242 levels at N=36, real case). Write parallel
  min-select instead; check logic depth for anything looped over MAX_*.
- Before TB work: bin/audit_signal_naming_conflicts.py (factory prefix
  collisions).
- FIFO depths power of 2. No emojis in RTL comments/headers.
