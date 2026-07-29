<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# STREAM tasks — active (in progress)

### TASK-056: RFC Stage-E — in-core R/W datapath perf monitors (retire `axi_bus_meter`)

**Priority:** Medium
**Status:** [~] In progress (2026-07-28) — **RTL + COSIM COMPLETE (E.1–E.4)**;
board bring-up pending. (Migrated from the loose
`projects/components/dmas/stream/TODO_RFC_StageE_datapath_perfmon.md`, formerly
"task #56".)

**Goal:** Replace the harness-side `axi_bus_meter` with in-core R/W datapath
performance monitors so utilisation is measured inside `stream_top_ch8` (and is
available on silicon), not only in the char harness.

**Done (this side, RTL + cosim):**
- **E.1** in-core datapath R/W monitors → `RDMON_PERF_*` @ 0x300 / `WRMON_PERF_*`
  @ 0x330. The two datapath skid buffers were upgraded to
  `axi4_master_rd_mon` / `axi4_master_wr_mon`; aggregate buckets + beat/byte/burst,
  RUN-bit window.
- **E.2** per-channel buckets via in-core `axi_bus_meter` (`PERF_CH_SEL` @ 0x35C +
  packed `RD/WRMON_PERF_CH_*` @ 0x360–0x374); cosim matched the legacy harness
  meter exactly (all four buckets, every channel) before it was retired.
- **E.3** latency histograms via new `rtl/amba/shared/axi_perf_latency_hist.sv`
  (`HIST_SEL/HIST_DATA/HIST_TOTAL` @ 0x378–0x380); totals == burst counts.
- **E.4** retired the harness-side `axi_bus_meter` (instances + harness_csr
  0x100/0x180 readback + `instrumentation.f`); repointed `read_bus_meters.py`
  (now an in-core shim) + `run_characterization.py` (opens/closes the RUN windows
  around the workload).

**Deliberately NOT retired:** the legacy `PktTypePerf` / `axi_monitor_reporter_perf`
path — it is shared `rtl/amba` IP enabled across many generated bridge adapters
and covered by the `val/amba` suite.

**Validation done:** lint clean both `USE_AXI_MONITORS` variants (pristine
baseline warning profile); cosim `TEST_TYPE=rw_perf` + `csr_read` pass.

**Remaining (board — owner drives):**
- [ ] `make bitstream` / `make timing` / `make utilization` / `make program`
- [ ] run a known workload, sanity-check the in-core perf CSRs
- [ ] the `run_characterization.py` sweep repoint is board-only-testable (not cosim)
