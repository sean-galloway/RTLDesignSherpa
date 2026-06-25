# FIFOs — Class Overview

**Category:** Storage / queues
**Scope:** `rtl/common/fifo_*.sv` (4 modules)
**Status:** Production-ready

---

## What this is

The base synchronous and asynchronous FIFO library. `fifo_sync` is a single-clock FIFO; `fifo_async` is a Gray-pointer CDC FIFO restricted to power-of-2 depths; `fifo_async_div2` is a Johnson-pointer CDC FIFO that works at any even depth; `fifo_control` is the shared full/empty pointer-arithmetic block used inside the three FIFO wrappers.

## Why use this class

Every interface in the repo eventually buffers — pipelines need elasticity, CDC paths need handoff, monitors need packet staging. These modules give you correct full/empty logic, safe Gray-coded CDC pointers, and configurable depth/width without re-deriving the pointer math. For AXI/AXIS-style ready-valid FIFOs with skid behavior see `rtl/amba/gaxi/`; this directory holds the protocol-agnostic primitives those wrappers build on.

## Members

| Module | One-line role | When to pick |
|---|---|---|
| [`fifo_control.sv`](../../../rtl/common/fifo_control.sv) | Shared full/empty generator used by all FIFO variants | Building a custom FIFO — reuse this for status |
| [`fifo_sync.sv`](../../../rtl/common/fifo_sync.sv) | Single-clock synchronous FIFO | Same-clock buffering, pipeline elasticity |
| [`fifo_async.sv`](../../../rtl/common/fifo_async.sv) | Async CDC FIFO with Gray-coded pointers, power-of-2 depths | CDC FIFO, standard case |
| [`fifo_async_div2.sv`](../../../rtl/common/fifo_async_div2.sv) | Async CDC FIFO using Johnson counters, any even depth | CDC FIFO when depth must not be power-of-2 |

## Picking guide

Same clock domain: `fifo_sync`. Crossing clock domains with a depth like 8/16/32/64: `fifo_async`. Crossing clock domains but you need depth 6 or 10 (e.g., to match a beat count or area target): `fifo_async_div2`. `fifo_control` is a leaf — only instantiate it directly if you are building a new FIFO flavor and want to reuse the proven status generator.

## Tests

[`val/common/`](../../../val/common/) — pytest + CocoTB suite. Naming: `test_fifo_*.py`. WaveDrom waveform generators exist for each variant.

## Full per-module specs

[`docs/markdown/RTLCommon/`](../../markdown/RTLCommon/) — one `.md` per module. Use those for parameter descriptions, port lists, and timing diagrams.

## Source

[`rtl/common/`](../../../rtl/common/) (`fifo_*.sv`)

> For AXI/AXIS ready-valid FIFOs (`gaxi_fifo_sync`, skid buffers, etc.), see [`rtl/amba/gaxi/`](../../../rtl/amba/gaxi/).
