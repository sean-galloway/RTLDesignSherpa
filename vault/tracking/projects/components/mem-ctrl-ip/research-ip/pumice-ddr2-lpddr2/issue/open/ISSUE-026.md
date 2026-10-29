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
**Status:** open (filed 2026-10-29)
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
