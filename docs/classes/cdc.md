<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Clock Domain Crossing (CDC) — Class Overview

**Category:** Cross-cutting (cuts across `rtl/common/`, `rtl/amba/shared/`, `rtl/amba/gaxi/`, `rtl/amba/apb/`, `rtl/amba/apb5/`)
**Status:** Production-ready

---

## What this is

A set of primitives that move data and control signals safely across asynchronous clock domains. The repo's CDC modules cover the three things you ever actually do in CDC: synchronize single bits, hand off multi-bit data with a handshake, and bridge word-stream traffic through an async FIFO. There's also a counter-pointer Gray-coding pair (the building block inside every async FIFO) and a reset bridge for the asymmetric reset path.

## Why use this class

Any time two parts of your design tick on different clocks (or the same clock fed from independent sources that drift), you cannot just wire a signal across — metastability and bus skew will eventually corrupt it. The fix is one of a small number of well-understood patterns:

- **Single-bit control signal** → multi-flop synchronizer
- **Multi-bit data, low rate** → request/acknowledge handshake
- **Word stream, high rate** → async FIFO with Gray-coded read/write pointers
- **Async-assert reset** → reset bridge

Pick the right one for the traffic shape. This page lists every CDC primitive in the repo and tells you when each one is the right choice. Implementations are all here so you don't have to roll your own (which is where CDC bugs usually come from).

## Members

### Single-bit / pulse synchronization

| Module | One-line role | When to pick |
|---|---|---|
| [`cdc_synchronizer.sv`](../../rtl/amba/shared/cdc_synchronizer.sv) | N-flop synchronizer for a stable level | Any single-bit level signal crossing domains. Default choice. |
| [`cdc_open_loop.sv`](../../rtl/amba/shared/cdc_open_loop.sv) | Pulse stretcher + synchronizer (no handshake back) | One-shot pulses where the source can guarantee width > 2 destination clocks. Cheapest pulse CDC. |

### Multi-bit data with handshake

| Module | One-line role | When to pick |
|---|---|---|
| [`cdc_2_phase_handshake.sv`](../../rtl/amba/shared/cdc_2_phase_handshake.sv) | 2-phase req/ack (toggle protocol) | Default for low-rate multi-bit transfers. Lower latency than 4-phase. |
| [`cdc_4_phase_handshake.sv`](../../rtl/amba/shared/cdc_4_phase_handshake.sv) | 4-phase req/ack (return-to-zero) | When you need explicit ack-deasserted state for downstream sequencing, or you're interfacing to an existing 4-phase protocol. |

### Reset CDC

| Module | One-line role | When to pick |
|---|---|---|
| [`reset_sync.sv`](../../rtl/common/reset_sync.sv) | Async-assert / sync-deassert reset bridge | Every reset that crosses into a new clock domain. Asserts immediately on async input; releases synchronously to local clock. |

### Pointer Gray-coding (FIFO building blocks)

| Module | One-line role | When to pick |
|---|---|---|
| [`bin2gray.sv`](../../rtl/common/bin2gray.sv) | Binary → Gray code | Building your own async FIFO pointer; converting a counter to a CDC-safe representation. |
| [`gray2bin.sv`](../../rtl/common/gray2bin.sv) | Gray → binary | Receiving side of the above. |
| [`counter_bingray.sv`](../../rtl/common/counter_bingray.sv) | Dual binary + Gray counter in one module | FIFO pointer in production code — gives you both the local-domain binary value (for math) and the CDC-safe Gray value (to ship across) in one register. |

### Async FIFOs (word-stream CDC)

| Module | One-line role | When to pick |
|---|---|---|
| [`fifo_async.sv`](../../rtl/common/fifo_async.sv) | Generic async FIFO | High-rate word stream between two domains. Default. |
| [`fifo_async_div2.sv`](../../rtl/common/fifo_async_div2.sv) | Async FIFO assuming write-clock = 2× read-clock (or vice versa) | When the clock ratio is exactly 2:1 and you want the smaller area / better timing of the simpler pointer logic. |
| [`gaxi_fifo_async.sv`](../../rtl/amba/gaxi/gaxi_fifo_async.sv) · [`gaxi_fifo_async_multi.sv`](../../rtl/amba/gaxi/gaxi_fifo_async_multi.sv) | AXI-style async FIFO with valid/ready handshake | Building an AXI/AXIS bridge across clock domains. Same payload, AMBA-shaped ports. |
| [`gaxi_skid_buffer_async.sv`](../../rtl/amba/gaxi/gaxi_skid_buffer_async.sv) · [`gaxi_skid_buffer_async_multi.sv`](../../rtl/amba/gaxi/gaxi_skid_buffer_async_multi.sv) | Async skid buffer (depth-2 async FIFO) | Lowest-area / lowest-latency AMBA crossing when only one or two beats of slack are needed. |

### Protocol-aware CDC slaves

| Module | One-line role | When to pick |
|---|---|---|
| [`apb_slave_cdc.sv`](../../rtl/amba/apb/apb_slave_cdc.sv) | APB slave with CDC built in | Putting an APB peripheral on a different clock from its master. Saves rolling your own. |
| [`apb5_slave_cdc.sv`](../../rtl/amba/apb5/apb5_slave_cdc.sv) | Same, APB5 version | APB5 variant. |

## Picking guide

- **One-bit level signal** → `cdc_synchronizer`. Always. Don't overthink.
- **One-bit pulse** → `cdc_open_loop` if the source can hold the pulse wide enough; otherwise pulse-stretch in source domain first, then `cdc_synchronizer`, then edge-detect on the destination side.
- **Multi-bit data, sporadic** (config registers, occasional commands) → `cdc_2_phase_handshake`. Use 4-phase only if you need return-to-zero semantics.
- **Multi-bit stream, sustained throughput** → async FIFO. Pick `fifo_async` for plain data, `gaxi_fifo_async` for AMBA-shaped ports, `gaxi_skid_buffer_async` when you only need depth 2 (lowest area + latency).
- **Reset crossing domains** → `reset_sync`. Every time.
- **Building a new async FIFO from scratch** → don't. Use `gaxi_fifo_async`. If you really must, use `counter_bingray` for the pointers.

## What to **not** do

- Don't synchronize the bits of a multi-bit bus independently with `cdc_synchronizer` — they will arrive on different destination cycles. Use a handshake or an async FIFO instead.
- Don't use a 2-flop synchronizer when MTBF matters (long-running silicon, high-rate transitions). Use 3 or more flops; `cdc_synchronizer` is parameterized for this.
- Don't run a synthesis tool's CDC report without then *reading the violations* — the tool will report safe Gray-code crossings as suspect; that's expected.

## On-board demo

[`projects/NexysA7/cdc_counter_display/`](../../projects/NexysA7/cdc_counter_display/) — multi-clock counter CDC running on a Digilent Nexys A7-100T. Useful for sanity-checking what a working CDC actually looks like on real silicon vs. on the simulator.

## Tests

- [`val/common/`](../../val/common/) — tests for the `rtl/common/` CDC primitives (`test_fifo_async*`, `test_bin2gray`, `test_gray2bin`, `test_counter_bingray`, `test_reset_sync`)
- [`val/amba/`](../../val/amba/) — tests for the `rtl/amba/shared/` CDC primitives (cdc handshakes, synchronizer) and AMBA-shaped async FIFOs/skids
- Project-level CDC validation lives in each project's `dv/` tree (e.g., `projects/components/stream/dv/`)

## Further reading

- Vendor's own RTL: [`rtl/amba/shared/`](../../rtl/amba/shared/) (cdc_* files), [`rtl/common/`](../../rtl/common/) (bin2gray, gray2bin, counter_bingray, fifo_async*, reset_sync), [`rtl/amba/gaxi/`](../../rtl/amba/gaxi/) (AMBA-shaped async FIFOs and skids)
- AMBA-shared inventory grouped by role: [`rtl/amba/README.md`](../../rtl/amba/README.md)
- Per-module specs: [`docs/markdown/RTLCommon/`](../markdown/RTLCommon/) (common-library modules), [`docs/markdown/RTLAmba/shared/`](../markdown/RTLAmba/shared/) (shared infrastructure)

---

## Navigation

- **[← Back to RTL Design Sherpa README](../../README.md)**
- **[← Browse by Class index](../../README.md#browse-by-class)**
- **[Main Documentation Index](../DOCUMENTATION_INDEX.md)**
