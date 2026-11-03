# ISSUE-026: two back-to-back reads of one burst trip the rd aligner's lost-beat assertion at DFI_RD_FIFO_DEPTH 4 (granite core TB)

> Source: granite TASK-006 (2026-10-29), the directed store-combining test
> `test_granite_core.py::test_granite_core_merge[0]` (STORE_MERGE_EN=0:
> the same-burst read pair takes two DRAM reads). With the core's default
> `DFI_RD_FIFO_DEPTH = 4` the second read's return hits
> `mc_dfi_rd_aligner.sv:311`: "read beat LOST (return FIFO full; rcnt=0
> outst=1) -- return-path sizing contract broken". With
> `DFI_RD_FIFO_DEPTH = 0` (the whole window) the same test passes and the
> two reads return the two bursts in order.
> Related: granite_core's comment on the parameter ("4 holds the return in
> the same-clock form where the ring is always ready"), mc_rd_return_ring,
> the granite core TB's `_dfi_model` (serves a read window 3 cycles after
> rddata_en, one burst per window), pumice BUG-010's return-path history.

**Priority:** P2
**Status:** closed 2026-11-02 -- an RTL sizing defect on CDC builds, not the TB model; fixed in `granite_core` (see Resolution)
**Owner:** TBD

## What is seen

Two reads of the same address, same id, issued back-to-back through the
BFM's engine runner, on `granite_core` with the TB's loopback DFI model.
The first read's beats return; the second read's first beat arrives with
the aligner's return FIFO full and the ring not ready, and the assertion
fires. The main `cocotb_test_granite_core` never issues two reads at once,
so it has not seen this. The board runs back-to-back reads at full rate
with zero mismatches on every profile, and the perf proxies (the RDS-DV
DFI slave, not this loopback) run concurrent reads daily -- so either the
TB model returns the second burst earlier than a PHY can (its 3-cycle
service is well under any real read latency, and `rddata_en` for two
adjacent reads is one continuous window to its edge detector) or the ring
has a not-ready case the comment does not cover.

## To resolve

Reproduce with the directed test at depth 4, read the ring's ready during
the second return, and either fix the TB model's service timing (likely)
or size / document the FIFO against the real not-ready case. Until then
the combining test pins the whole-window depth for both of its states.

## Resolution (2026-11-02)

**Neither guess was right: it is the CROSSING.** The TB runs `granite_core`
with `DFI_CDC_EN = 1` and `dfi_clk = 2 x aclk` (`board_clock_periods`), which
is also `granite_top_geared`'s default. The ring is always ready
(`dfi_ret_ready_o` is its issue queue's valid, and a ticket is pushed at issue,
long before its data) -- but across the CDC the DFI side writes the return
FIFO one word per dfi_clk while the ring drains it one per aclk, behind a
pointer synchroniser. `mc_dfi_rd_aligner` has no back-pressure, so a read
stream outruns any FIFO shallower than the reads in flight; its own header
states the contract (FIFO >= reads in flight x BL_WORDS). Depth 4
(84cbb3f86, 2026-10-24) was measured on the board, where `DFI_CDC_EN = 0`
and one clock makes "always ready" true. The comment's "2 loses beats where
dfi_clk runs at 2x aclk" was this same failure one depth lower.

Depth sweep, `test_granite_core_merge[0]` (two back-to-back reads of one
burst), at the TB's crossing:

| `DFI_RD_FIFO_DEPTH` | result |
|---|---|
| 4 | FAIL: `read beat LOST (return FIFO full; rcnt=0 outst=1)` |
| 6, 12 | not legal: `gaxi_fifo_async` Gray pointers need a power of two |
| 8, 16 | pass (two reads; a longer stream needs more) |
| 0 (whole window) | pass |

**Fix.** `granite_core` sizes the read-return FIFO through
`DFI_RD_FIFO_EFF`: `DFI_RD_FIFO_DEPTH` (4) only when `DFI_CDC_EN = 0`; with
the crossing on, or 0, `RD_RET_DEPTH x BURST_WORDS`, the bound the aligner
needs. Same-clock builds -- every board bitstream (`granite_char_macro`
ties `DFI_CDC_EN = 0`) -- are unchanged. The parameter comments in
`granite_core` and `granite_top_geared` say so. Pumice always used the whole
window and was never exposed.

The TB pins come out: the two merge tests and the page-mode test no longer
force `DFI_RD_FIFO_DEPTH = 0`; at the product default they now take the
whole-window path, which is what failed before.

**Gates** (from a snapshot of HEAD plus the fix): granite top
`make clean-all && run-all-func` 22 passed / 1 xfail (the standing one);
`test_granite_char_uart.py` 2 / 2 (the same-clock board configuration);
pumice `run-all-func-both` 222 / 222 at both geometries.

