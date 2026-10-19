# TASK-005: Write-data interleaving support in axi3_to_axi4_wr

**Priority:** P3
**Status:** DEFERRED
**Owner:** TBD

## What

Add AXI3 write-data interleaving support to `axi3_to_axi4_wr` by demuxing incoming W beats by `WID` before presenting a single, in-order AXI4 write transaction to the slave.

## Why

The current `axi3_to_axi4_wr` enforces a single-active-write contract: only one outstanding write ID is accepted and `WID` must remain stable. This is a deliberate simplification because the upstream DE10 HPS is not expected to interleave. If that assumption changes, the converter must buffer interleaved beats, route them to the correct AXI4 AW context, and preserve write ordering rules.

## Un-defer condition

An upstream AXI3 master is confirmed to exercise interleaved `WID` sequences on the target seam.
