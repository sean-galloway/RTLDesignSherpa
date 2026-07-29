---
title: Coverage record-ingest gap (open)
summary: On silicon the DMA runs but zero monbus records reach either tally.
---

# Coverage record-ingest gap (OPEN)

On the 4-channel Genesys 2 monitor-coverage bitstream, the primitive routines
all pass on silicon (see `host/poc.py`: link, desc_ram, and the cfg AXIL slave --
profile-CAM load + dense-bin read). But the end-to-end coverage routine
(`host/poc_coverage.py`, R6) shows **zero records reach either tally**, so no
agent-resolved coverage is observed yet.

## What is confirmed
- The DMA runs and completes: harness timer reports done+pass (status 0x05) for a
  256 B / 16-beat transfer, so real AXI traffic occurred.
- The host config replicates the cosim `run_dma_test` recipe exactly, by name:
  SOFT_RESET first, then per-monitor PKT_MASK=0xFEF0 / MASK3=0 / ENABLE=0x0F /
  ERR_CFG=0 (BULK_TRACE), match-all DEBUG range0 on rd+wr (ctrl=0x31), FREEZE
  after. Profile CAM load over the cfg slave works (bins readable).
- Routing addresses are consistent: harness `cfg_mon_base_addr=0x0004_0000` ==
  the `stream_tally` record-ingest slave window (0x40000, bridge TOML);
  `slave_tally` @ 0xC0000; cfg slaves @ 0x100000 / 0x140000.
- **Both** tallies are empty -- STREAM (fed by the in-core group -> `mon_awvalid`)
  and SLAVE (fed by the dma-slave group -> `slmon_awvalid`). They are independent
  paths, so the empty result is not specific to one group.

## Why the sim never caught it
The profile cosim (`test_stream_mon_profile`) is monitors-on and UART-bound
(~26 s per transaction); it overran the 34-min TB wall BEFORE its dense-bin
assertion executed. The DMA + cfg-load portions passed, but
`assert rd_hits>0 and wr_hits>0` never actually ran. The author had already
tagged the STREAM tally "the empty one" (test_stream_mon.py comment) and added
edge-trigger probes on `mon_awvalid` / `slmon_awvalid` to chase exactly this.

## Next step (needs instrumentation, not a config tweak)
Since both independent groups deliver nothing, the question is whether the
monitor groups EMIT records at all under this traffic. Decisive checks:
1. On-silicon ILA on `mon_awvalid` / `slmon_awvalid` (and the monitor
   packet-valid upstream) during a DMA -- do the m_axil write masters ever fire?
2. Or a BOUNDED cosim run reading the existing `_watch()` edge counts, without
   waiting for the full dense sweep.

If the valids never assert, the monitors aren't emitting (addr-range checker /
group enable / arbiter upstream); if they assert but bins stay 0, the tally
record reassembler/flush is the culprit. The fub-level `test_monbus_pkt_tally.py`
(4/4) proves the counting logic in isolation, so suspicion is on the emit/route
integration, not the counter.

Tooling: `host/poc.py` (primitives), `host/poc_dma.py` (DMA + raw sweep),
`host/poc_coverage.py` (full recipe + both-tally isolation sweep).
