# Counters — Class Overview

**Category:** Sequential primitives
**Scope:** `rtl/common/counter_*.sv` (8 modules)
**Status:** Production-ready

---

## What this is

Parameterized counter primitives covering plain up-counters, FIFO-pointer counters with MSB-wrap semantics, loadable terminal-count counters, frequency-invariant prescaled counters, and the shift-register counters (ring, Johnson, bin/gray) used for sequencing and CDC pointers.

## Why use this class

Every state machine, timeout, throttle, FIFO, prescaler, and one-hot sequencer eventually needs a counter. Picking the right variant matters: a FIFO pointer needs the MSB-toggle wrap for full/empty detection, a periodic tick needs a max-compare counter, a CDC pointer needs Gray or Johnson encoding, and a frequency-portable timer needs a prescaler. Reusing these instead of rolling your own avoids subtle wrap and reset bugs.

## Members

| Module | One-line role | When to pick |
|---|---|---|
| [`counter.sv`](../../../rtl/common/counter.sv) | Simple up-counter with `tick` output at `MAX` | Periodic tick / heartbeat |
| [`counter_load_clear.sv`](../../../rtl/common/counter_load_clear.sv) | Loadable terminal-count with clear | Configurable delays, protocol timers |
| [`counter_bin.sv`](../../../rtl/common/counter_bin.sv) | FIFO-style binary counter (MSB toggles on wrap) | FIFO read/write pointer |
| [`counter_bin_load.sv`](../../../rtl/common/counter_bin_load.sv) | FIFO binary counter with variable-increment and direct load | FIFO pointer with drop/flush/skip |
| [`counter_freq_invariant.sv`](../../../rtl/common/counter_freq_invariant.sv) | Prescaled counter — time-portable across clock rates | Timers that must hold real-time meaning |
| [`counter_ring.sv`](../../../rtl/common/counter_ring.sv) | Ring counter (rotating one-hot) | One-hot phase sequencer |
| [`counter_johnson.sv`](../../../rtl/common/counter_johnson.sv) | Johnson (twisted-ring) counter | 2N-state sequencer, non-pow2 async FIFO pointer |
| [`counter_bingray.sv`](../../../rtl/common/counter_bingray.sv) | Combined binary + Gray output counter | Async FIFO pointer needing both forms |

## Picking guide

For a plain periodic tick, use `counter`. For a configurable timeout or delay generator, use `counter_load_clear`. For FIFO pointers use the `counter_bin*` family — `counter_bin` for plain push/pop, `counter_bin_load` when the pointer must jump (drops, flushes). For CDC, use `counter_bingray` (power-of-2 depth) or `counter_johnson` (any even depth). Use `counter_freq_invariant` when the same RTL must run at different clock rates with stable real-time behavior.

## Tests

[`val/common/`](../../../val/common/) — pytest + CocoTB suite. Naming: `test_counter_*.py`.

## Full per-module specs

[`docs/markdown/RTLCommon/`](../../markdown/RTLCommon/) — one `.md` per module. Use those for parameter descriptions, port lists, and wrap-behavior diagrams.

## Source

[`rtl/common/`](../../../rtl/common/) (`counter_*.sv`)
