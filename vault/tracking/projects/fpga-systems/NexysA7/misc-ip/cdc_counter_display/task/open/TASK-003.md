# TASK-003: measured comparison of the five CDC modes -- area, latency, throughput

**Priority:** P3
**Status:** open (filed 2026-11-07; was "cross-variant deliverables: docs/COMPARISON.md" in CDC_DEMO_TODO)
**Owner:** TBD

## Why

The books and episode 5 state the trade-offs in words ("two-phase if throughput
matters, four-phase if your reviewer demands the classic waveform";
`docs/cdc_fpga_system/ch02_harness/01_harness.md`: "their differences are
throughput, latency and whether every event or only the latest value survives"). No
number backs them.

## Done when

A table, one row per mode, with:
- **Area**: LUT / FF / BRAM per mode's primitive instance, from a hierarchical
  utilization report of the routed `build-demo` (all modes are built in
  parallel per counter, so one build gives every row).
- **Latency**: source event to sys_clk VALUE update, in sys_clk cycles, at a
  stated ctr_clk. Needs a measurement path (a timestamp or cycle counter);
  there is none in the RTL today.
- **Throughput / what crosses**: every event (FIFO) vs latest snapshot
  (handshakes, `HANDSHAKE_INTERVAL`=256) vs held pulse (STRETCH).

Where the table lives is a doc-placement decision: the `cdc_fpga_system` book
is the likely home, not a new beside-code file.
