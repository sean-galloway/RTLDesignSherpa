# Claude Code Guide: CDC Library

**Purpose:** AI-specific guidance for `rtl/cdc/`

---

## Quick Context

**What:** Everything whose job is getting data across a clock boundary — synchronizer, handshakes, asynchronous FIFOs, and the Gray/Johnson coders that make those crossings safe.
**Where the docs are:** [`docs/markdown/rtl-cdc/overview.md`](../../docs/markdown/rtl-cdc/overview.md) — start there for the decision guide; the catalogue is [`index.md`](../../docs/markdown/rtl-cdc/index.md).
**Tests:** `val/cdc/` · **Filelists:** `rtl/cdc/filelists/` (lint the area with `cdc_all.f`) · **Formal:** `formal/cdc/`

This area was pulled out of `rtl/common` and `rtl/amba` (AMBA-CDC-REORG). If you find a reference to `rtl/common/bin2gray.sv`, `rtl/amba/gaxi/gaxi_fifo_async.sv` or `rtl/amba/cdc/`, it's stale — fix it rather than working around it.

---

## The One Rule That Matters Here

**Never cross a clock domain with a bare flop chain unless the signal can tolerate it.** A multi-flop synchronizer is only safe for a signal whose bits may be sampled independently: a single-bit flag, or a quasi-static value that holds still across the crossing. A multi-bit value that changes as a unit will land with its bits split across cycles, and the receiver sees a value that never existed.

For those, pick by what the receiver needs:

| Need | Use |
|---|---|
| single flag / quasi-static value | `cdc_synchronizer` |
| multi-bit counter | `counter_bingray` (Gray), or `counter_johnson` for non-power-of-2 |
| one transfer, acknowledged | `cdc_2_phase_handshake` / `cdc_4_phase_handshake` |
| one transfer, no acknowledge | `cdc_open_loop` |
| a stream | `fifo_async`, or `gaxi_fifo_async` / `gaxi_skid_buffer_async` on GAXI |

**Read the reset section before choosing a handshake.** If the two domains can reset independently — a soft reset, a per-block reset, separate power domains — `cdc_2_phase_handshake` will fabricate a transfer out of an idle link. This is documented with waveforms in [`rtl-cdc/cdc.md`](../../docs/markdown/rtl-cdc/cdc.md#reset-considerations).

---

## What Stays in rtl/common

`fifo_control`, `counter_bin`, `find_first_set`, `find_last_set` and `leading_one_trailing_one` are dependencies of modules here, but they are NOT cdc modules — they serve FIFOs and bit-search generally. They stay in `rtl/common` and are reached with `-f` includes. Do not move them here, and do not hand-list their sources in a cdc filelist; see [[filelists]] in the handbook.

---

## Pointer Encoding: Gray vs Johnson

`fifo_async` and `gaxi_fifo_async` support both through the `USE_JOHNSON` parameter — one module, not two:

- **Gray (`USE_JOHNSON=0`, default)** requires a power-of-2 depth. The elaboration check only fires in this mode.
- **Johnson (`USE_JOHNSON=1`)** takes **any** depth, odd included. It costs more decode logic (roughly 2x `gray2bin`) because it needs priority encoders.

`USE_JOHNSON=1` replaced the retired standalone `fifo_async_div2`.

---

## Before Adding a Module Here

1. Search first: `ls rtl/cdc/*.sv`. Fourteen modules already cover most crossings.
2. A new module lands with its `.f` in `rtl/cdc/filelists/` **in the same commit**, and `cdc_all.f` gets a line. Then `python3 bin/filelist_registry.py --check` and `--audit` must both pass.
3. A test goes in `val/cdc/`, taking its sources from the filelist — never a hand-listed array. Hand-listing is what broke `test_fifo_async_wavedrom` when this area was created.
