# TASK-003: Tag-based chopped-burst overlap in axi4_to_axi3_rd

**Priority:** P3
**Status:** DEFERRED
**Owner:** TBD

## What

Add tag-based overlap of chopped AXI3 read chunks in `axi4_to_axi3_rd` so that sequential chunk-issue no longer limits the DE10 leg-bridge `f2h` throughput.

## Why

The current read path issues one AXI3 chunk at a time per ID and waits for its R data before issuing the next chunk. This is correct and simple, but it leaves idle cycles on the AXI3 slave. Tag-based overlap would issue chunk *n+1* under a different temporary ID while chunk *n* is outstanding, then merge responses back to the original ARID at the AXI4 slave.

## Un-defer condition

Measured `f2h` throughput is shown to be bounded by sequential chunk issue rather than by the hard-subsystem memory latency or fabric bandwidth.
