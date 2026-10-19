# TASK-002: APB3 to AXI4 wrapper over apb4_to_axi4

**Priority:** P3
**Status:** DEFERRED
**Owner:** TBD

## What

Provide an `apb3_to_axi4` wrapper around the existing `apb4_to_axi4` converter for retro-legacy customers still carrying APB3 interfaces.

## Why

APB3 differs from APB4 mainly in the absence of the `PSTRB` and `PPROT` signals. A thin shim can tie off or derive these from APB3 controls (`PWRITE` → `PSTRB`, static `PPROT`) and then reuse the verified APB4→AXI4 path, rather than maintain a separate converter.

## Un-defer condition

A named consumer (board leg, soft-core peripheral bus, or customer IP) requests APB3 connectivity and confirms the signal-set subset they need.
