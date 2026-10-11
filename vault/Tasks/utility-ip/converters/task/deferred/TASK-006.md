# TASK-006: Quartus synthesis-compatibility check for queue-based converter FSMs

**Priority:** P2
**Status:** DEFERRED
**Owner:** TBD

## What

Verify that the queue-based SystemVerilog FSMs in the AXI3 converters (`axi4_to_axi3_rd`, `axi4_to_axi3_wr`, and related segmenter logic) synthesize cleanly under Quartus Prime 24.1 before the DE10 leg-bridge integration.

## Why

The current RTL uses simulation-idiomatic SV queues inside `always_ff` blocks (for example, descriptor FIFOs implemented as unpacked queue arrays). Quartus Prime historically supports a subset of SV queue semantics; if the chosen patterns are rejected, the queues must be refactored to static arrays with head/tail pointers before the FPGA leg-bridge is built.

## Un-defer condition

A Quartus 24.1 synthesis run is attempted on the converter filelist and either passes, or fails with a clear, actionable error that determines the refactor scope.
