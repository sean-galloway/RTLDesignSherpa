# DMA Observer Integration — Plan & Tracker

**Status:** Mostly done. The instrumentation is built and proven on STREAM;
remaining work is wiring the standalone observer into a generic
external-DMA characterization harness.

**Goal:** Drop `axi4_dma_observer` between an arbitrary AXI4-master DMA's
read/write ports and the fabric, and have it produce **all the
performance information the existing Python infrastructure consumes** —
the same data we already gather for STREAM — for our DMA or anyone else's.

> **Why this is "mostly done":** the observation + metering logic that
> produces the STREAM numbers (`datapath_E2E_pct = 94.1%`, etc.) has been
> pulled into one standalone, DMA-agnostic module (`axi4_dma_observer`)
> and unit-tested. STREAM itself is fully characterized through the
> equivalent in-harness instrumentation today. What's left is the
> integration glue (a harness "flavor") to point the observer at a
> non-STREAM DMA and land its outputs on the CSR surface the host
> already reads.

---

## Status legend

- `[x]` done / verified
- `[~]` partially done — exists but not yet wired/verified in this flow
- `[ ]` not started

---

## 1. Components (the reusable parts)

| Component | Path | Status | Notes |
|---|---|---|---|
| `axi4_dma_observer` (taps + arbiter + group + meters, pass-through) | `rtl/amba/shared/axi4_dma_observer.sv` | `[x]` | Built, cocotb block-test `val/amba/test_axi4_dma_observer.py`; in `rtl/amba/filelists/monbus_group.f` |
| `axi_bus_meter` (prod/bp/starv/idle buckets) | `rtl/amba/shared/axi_bus_meter.sv` | `[x]` | Per rd/wr port inside the observer; pure CSR counters, no SRAM, unbounded run length |
| `axi4_master_rd_mon` / `axi4_master_wr_mon` (passive taps) | `rtl/amba/axi4/` | `[x]` | Per-txn completion/latency, errors, timeouts; `TRANS_CAM_PIPELINE` available |
| `monbus_arbiter` + `monbus_compressor` + `monbus_halfbeat_packer` | `rtl/amba/shared/` | `[x]` | Aggregation + optional compression chain |
| `monbus_axil_axi4_group` (AXIL drain + AXI4 bulk-dump + IRQ) | `rtl/amba/shared/monbus_axil_axi4_group.sv` | `[x]` | Observer's output stage; test `val/amba/test_monbus_axil_axi4_group.py` |
| `axi4_dma_slaves` (LFSR read source + CRC write sink) | stream char harness | `[x]` | The endpoint for endpoint-mode characterization |
| `harness_csr` meter input ports @ 0x100/0x180, timer, CRC regs | `stream_char_framework/rtl/harness_csr.sv` | `[x]` | Already shaped for the observer's meter outputs |
| Host readers (`read_bus_meters.py`, timer/CRC/trace, JSON emit) | `flows-stream-bridge/host/` | `[x]` | CSR-based; reusable unchanged |
| PDF/CSV report tooling (`generate_reports_pdf.sh`, `perf_json_to_csv.py`) | `reports/` | `[x]` | House-style reports already wired |

**STREAM end-to-end characterization:** `[x]` proven — perf matrix
(`reports/perf/matrix_2026-06-15.*`) and compression report
(`reports/compression/`) were gathered on the all-fixes bitstream.

---

## 2. The contract: every Python/JSON field → its hardware source

What the host already reads, and where it comes from in an observer-based harness:

| Field(s) | Source | Status |
|---|---|---|
| `r/w_aggregate{prod,bp,starv,idle}`, `*_buckets_pct`, `datapath_utilization_r/w`, per-channel, overflow | observer `*_meter_*` ports | `[~]` ports exist; needs wiring to `harness_csr` 0x100/0x180 |
| `cycles_total`, `end_to_end_utilization`, `r/w_first/last/firstlast_cycles` | harness timer + first/last-beat latches | `[~]` reuse harness timer; add/verify first/last latches (meter doesn't emit them) |
| CRC `rd_expected/wr_expected/wr_computed/match`; beat counts → `mb_moved`/throughput | `axi4_dma_slaves` (endpoint) | `[x]` reuse as-is on fabric side |
| `completion{completed,timer_pass,overflow,...}` | harness timer/status | `[x]` reuse |
| `trace{wr_ptr,overflow}` + compressed monbus records | observer `m_axi` bulk-dump **or** `s_axil` drain | `[ ]` land dump into `debug_sram` @ 0x40000 (or new host drain) |

---

## 3. Remaining integration work

### Phase 1 — generic harness (`dma_char_harness.sv`, sibling of `stream_char_harness.sv`)
- [ ] Instantiate the external DMA as the DUT; bring its rd/wr master ports to the observer `dma_*` side
- [ ] Instantiate `axi4_dma_observer`; `fab_*` side → `axi4_dma_slaves` (LFSR source + CRC sink)
- [ ] Wire observer `{rd,wr}_meter_agg_*` / per-channel → `harness_csr` meter inputs (0x100/0x180)
- [ ] Land observer `m_axi` bulk-dump into a `debug_sram` exposed at 0x40000 with `wr_ptr`/`overflow`
- [ ] Reuse harness timer + first/last latches + freeze/clear → observer `i_meter_freeze`/`i_meter_clear`
- [ ] Bridge/UART + `harness_csr` as today

### Phase 2 — per-DMA kick adapter (the one inherently DMA-specific piece = the "flavor")
- [ ] Define a thin `dma_kick_adapter` interface: harness `csr_start_pulse` + transfer descriptor → DMA-native start; DMA "done"/expected-beats → harness timer
- [x] STREAM flavor: the existing harness already does this (STREAM descriptor kick) — reference implementation
- [ ] First external-DMA flavor (TBD which DMA — see Open Decisions)

### Phase 3 — host
- [x] CSR readers (`read_bus_meters.py`, timer/CRC/trace) reusable
- [ ] Replace `run_characterization.py` STREAM-descriptor `build_test()` with a DMA-specific workload setup (drives the kick adapter); keep JSON emit + report tooling identical

### Phase 4 — build flow + verify
- [ ] Clone `flows-stream-bridge` flow (filelists from `monbus_group.f` + new harness, XDC, tcl)
- [~] Extend `test_axi4_dma_observer.py` to an endpoint-mode cosim (observer + `axi4_dma_slaves` + stub AXI DMA) asserting meter buckets + CRC against a known pattern, before FPGA

---

## 4. Flavors (per-DMA variants)

The observer, `axi4_dma_slaves`, timer, CSR, and host are **shared**.
Only two things vary per DMA-under-test:

1. **Kick adapter** (Phase 2) — how the DMA is started and how "done" /
   expected-beats are signalled.
2. **Channel attribution config** — `NUM_CHANNELS` + `cfg_rd_rid_per_channel`
   (reads) and `dma_wr_active_ch_id` sideband or an AW→W order tracker
   (writes). `NUM_CHANNELS=1` (aggregate-only) works for any DMA with no
   extra wiring.

| Flavor | Kick mechanism | Channels | Status |
|---|---|---|---|
| STREAM | descriptor kick (existing harness) | 8 (rid + wr sideband) | `[x]` works today |
| *(next external DMA)* | TBD | TBD | `[ ]` |

---

## 5. Open decisions

1. **Channel attribution granularity** — `NUM_CHANNELS=1` (aggregate, simplest, any DMA) vs. bucket by AXI ID (fill `cfg_rd_rid_per_channel`; writes need a sideband or an AW→W order tracker).
2. **Trace readout** — land `m_axi` dump into `debug_sram` @ 0x40000 (zero host change, SRAM-depth-limited) vs. `s_axil` IRQ-drain (unbounded, new host reader). Bus-meter utilization (the headline) is unaffected either way — pure CSR counters.
3. **First target DMA + its kick mechanism** — defines the first Phase-2 flavor (descriptor in memory? a "go" register? something else?).

---

## 6. Key file references

- Observer: `rtl/amba/shared/axi4_dma_observer.sv`
- Observer test: `val/amba/test_axi4_dma_observer.py`
- Output stage: `rtl/amba/shared/monbus_axil_axi4_group.sv` (test `val/amba/test_monbus_axil_axi4_group.py`)
- Meter: `rtl/amba/shared/axi_bus_meter.sv`
- Filelist: `rtl/amba/filelists/monbus_group.f`
- STREAM harness (reference flavor): `projects/NexysA7/stream_characterization/flows-stream-bridge/rtl/stream_char_harness.sv`
- CSR (meter inputs at 0x100/0x180): `projects/NexysA7/stream_characterization/stream_char_framework/rtl/harness_csr.sv`
- Host readers: `projects/NexysA7/stream_characterization/flows-stream-bridge/host/read_bus_meters.py`
- Methodology: `projects/NexysA7/stream_characterization/DMA_UTILIZATION_MEASUREMENT.md`
- Perf/compression reports: `projects/NexysA7/stream_characterization/reports/`
