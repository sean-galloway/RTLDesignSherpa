# Reset — Class Overview

**Category:** Reset infrastructure
**Scope:** `rtl/common/reset_sync.sv` (1 module)
**Status:** Production-ready

---

## What this is

A parameterized reset synchronizer providing asynchronous assertion and synchronous deassertion. The shift-chain depth is configurable to trade metastability margin against deassertion latency.

## Why use this class

Reset must assert immediately (asynchronous) but deassert in sync with the clock to avoid metastability and timing-arc violations on the receiving flops. Every clock domain in a design needs a synchronizer on its reset; `reset_sync` is the one-stop module for that.

## Members

| Module | One-line role | When to pick |
|---|---|---|
| [`reset_sync.sv`](../../../rtl/common/reset_sync.sv) | Async-assert / sync-deassert reset synchronizer | One per clock domain that receives an external/system reset |

## Picking guide

Instantiate one `reset_sync` per receiving clock domain. Set the depth to your standard CDC stages (typically 2 or 3). Do not stretch or condition the reset upstream of this module — let `reset_sync` handle the clean handoff.

## Tests

[`val/common/`](../../../val/common/) — pytest + CocoTB suite. Naming: `test_reset_sync.py`.

## Full per-module specs

[`docs/markdown/RTLCommon/reset_sync.md`](../../markdown/RTLCommon/reset_sync.md) — parameters, ports, and synchronizer-depth guidance.

## Source

[`rtl/common/reset_sync.sv`](../../../rtl/common/reset_sync.sv)
