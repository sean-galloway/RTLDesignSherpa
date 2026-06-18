# TODO — RFC Stage E (option 2): in-core R/W datapath perf monitors, retire `axi_bus_meter`

**Status:** NOT STARTED. Tracked as task #56.
**Prerequisite (DONE):** RFC Stage E **option 1** landed in commit `a4a7442b`
("feat(stream): surface descriptor-monitor perf window via CSR"). Read that
commit first — it is the **proven template** for everything below.

> **Work this in a SIDE REPO / separate worktree.** This is a large, multi-file
> RTL change that regenerates the regblock and rebuilds the bitstream. Do it on
> a clone or `git worktree` so the primary checkout stays buildable during
> development. Rebase/PR back only once cosim + board numbers match.

---

## 1. Why this exists (the topology reality)

Despite the natural assumption that "the monitor block already brings the perf
signals out," **there is no `axi_monitor` watching the STREAM datapath R or W
bus anywhere inside the core.** Confirmed topology:

- The **only** in-core AXI monitor is the **descriptor-fetch monitor**
  (`axi4_master_rd_mon` at `projects/components/stream/rtl/macro/scheduler_group_array.sv:499`).
  Option 1 already surfaced *its* perf window to CSR. It measures the
  **descriptor-fetch R bus only** — not the datapath.
- **Datapath R/W utilization** (every bucket number in the perf report and the
  whole `DMA_UTILIZATION_MEASUREMENT.md` methodology) is measured **only** by two
  external `axi_bus_meter` instances in the FPGA characterization harness:
  - `projects/NexysA7/stream_characterization/flows-stream-bridge/rtl/stream_char_harness.sv:1667` `u_rd_bus_meter` — snoops read engine R channel (`rd_rvalid/rd_rready`, channel id `rd_rid`).
  - `…stream_char_harness.sv:1699` `u_wr_bus_meter` — snoops write engine W channel (`wr_wvalid/wr_wready`); channel attribution via the write-engine sideband `wr_active_channel_id/_valid` (`stream_char_harness.sv:1632`).
- The per-channel "channel monitors" (`mon_valid_ch[ch]` in `scheduler_group_array.sv`)
  are **scheduler/descriptor-engine event reporters**, NOT bus monitors. They have
  **no perf counters** (`cfg_sched_perf_enable` is "not implemented").
- RFC **Stage C** (per-channel buckets) and **Stage D** (latency histograms) are
  **not implemented in any RTL** — genuinely absent, not just tied off.

So "retire `axi_bus_meter`, read the monitor's CSRs instead" is **not a wiring
job** — it requires *new* monitor instances on the datapath plus new RTL features.

---

## 2. Goal & scope (user-selected: "buckets + counts + latency histograms")

Source the datapath perf metrics from the monitor framework (CSR route, no
MonBus packets) and **retire `axi_bus_meter`**, delivering:

1. **Four cycle buckets** (productive / backpressure / starvation / idle),
   aggregate + **per-channel** (RFC Stage C), for **both** the read R bus and
   write W bus.
2. **Counts**: beat / byte / burst, per bus (+ per-channel where cheap).
3. **Latency histograms** (RFC Stage D) — the only *genuinely new* data vs.
   today's bus_meter: per-transaction latency (AR→first-R and AR→RLAST for reads,
   AW→B for writes) binned into a histogram. This is CSR-address-heavy — see §6.

The numbers this produces for the four buckets **must match** the current
`axi_bus_meter` values for the same workload (that's the acceptance test).

---

## 3. The proven pattern to copy (from option 1, commit `a4a7442b`)

Option 1 established the exact end-to-end route. Mirror it:

1. **RTL port plumbing** up three hierarchy levels:
   `axi_monitor_base` (ports already exist) → wrapper → `scheduler_group_array.sv`
   → `stream_core.sv` → `stream_top_ch8.sv` (note: **two** `USE_AXI_MONITORS`
   generate variants in the top — wire both; variant-0 ties outputs to 0).
2. **Window control via a `RUN` CSR bit**, trigger mode:
   `cfg_start_event_sel=3'b000`, `cfg_end_event_sel=3'b000`,
   `cfg_start_trigger = run`, `cfg_end_trigger = ~run`, `cfg_window_force_close=0`.
   Decoupled from `cfg_perf_enable` so the window accumulates without emitting
   `PktTypePerf` packets.
3. **CSRs** added to `projects/components/stream/rtl/macro/stream_regs.rdl`
   (status regs `sw=r hw=w`, control reg `sw=rw hw=r`), regblock regenerated,
   `stream_regmap.py` mirrored, `stream_top_ch8.sv` drives `hwif_in.*.next` from
   the monitor outputs (see the `always_comb` block that drives `OBS_*`/`DAXMON_PERF_*`).
4. **Host reader** modeled on
   `projects/NexysA7/stream_characterization/flows-stream-bridge/host/read_desc_perf.py`.
5. **Cosim** functional test modeled on the `desc_perf` TEST_TYPE in
   `…/dv/tests/test_stream_char.py` + the `measure_desc_perf` hook in
   `…/dv/tbclasses/stream_char_tb.py`.

### Critical semantics gotcha (already discovered in option 1)
`window_cycles` is a **live** counter that `axi_monitor_base` **zeroes when the
window closes** (`WIN_CLOSING_S` in `rtl/amba/shared/axi_monitor_base.sv:562`).
It is meant to be sampled at close for the legacy WIN_END packet, **not** polled
after. The **four bucket counters HOLD** after close (`axi_monitor_base.sv:655`),
so **`bucket_total = prod+bp+starv+idle` is the authoritative closed-window
length** for the CSR route. Do NOT modify `axi_monitor_base` to make
`window_cycles` persist — it is shared by the bridge/val-amba monitors and that
would be a broad-impact, high-risk change. Document the live-only semantics
instead (option 1 did this in the RDL field desc, host reader, and TB).

---

## 4. `axi_monitor_base` perf surface (already available, per bus)

These output ports exist on `rtl/amba/shared/axi_monitor_base.sv` (and pass
through the `axi4_master_rd_mon` / `axi4_master_wr_mon` wrappers):

```
window_active        logic           perf_idle_cycles    [31:0]
window_cycles  [31:0] (live-only)    perf_beat_count     [31:0] (= prod_cycles)
perf_prod_cycles  [31:0]             perf_byte_count     [63:0]  (beats<<axsize)
perf_bp_cycles    [31:0]             perf_burst_count    [31:0]  (AR/AW handshakes)
perf_starv_cycles [31:0]
```

Window control inputs: `cfg_start_event_sel[2:0]`, `cfg_end_event_sel[2:0]`,
`cfg_start_trigger`, `cfg_end_trigger`, `cfg_window_force_close`.
Build with `ENABLE_PERF_LOGIC=1` (default in the STREAM hierarchy). The window
FSM + bucket counters are **ungated** by `cfg_perf_enable` — they always run.

**Not yet present (must be added):** per-channel buckets (Stage C) and latency
histograms (Stage D). See §5/§6.

---

## 5. Staged implementation plan

Do these in order; validate (lint → cosim) at each stage before the next.
Bitstream only at the very end.

### Stage E.1 — Instantiate datapath R/W monitors (aggregate buckets+counts)
- Add an `axi4_master_rd_mon` (or the lighter perf-only monitor, if you create
  one) on the **read engine R bus** and an `axi4_master_wr_mon` on the **write
  engine W bus**, inside `stream_core.sv` (alongside the read/write engines in
  `projects/components/stream/rtl/fub/axi_read_engine.sv` /
  `axi_write_engine.sv`). NOTE: `stream_core.sv` already has *dead* config hooks
  `cfg_rdeng_mon_*` / `cfg_wreng_mon_*` (assigned but never consumed) — wire the
  new monitors to those instead of inventing new config.
- Surface `perf_*`/`window_*` from each new monitor up the same 3-level chain to
  new CSR blocks `RDMON_PERF_*` and `WRMON_PERF_*` (mirror `DAXMON_PERF_*`).
- One shared `RUN` bit (or per-bus) drives all three windows in lockstep.
- **Acceptance:** cosim `dma_Nch` workload → `RDMON_PERF`/`WRMON_PERF` aggregate
  buckets match the `axi_bus_meter` aggregate buckets for the same run (within
  the close-window off-by-few-cycles caused by CSR readout latency).

### Stage E.2 — RFC Stage C: per-channel buckets
- Add per-channel (`NUM_CHANNELS`-deep) bucket counters in `axi_monitor_base`
  (or a dedicated perf sub-block), keyed by `rid` on the read R bus and by the
  write-engine channel sideband on the W bus (the same `wr_active_channel_id`
  mechanism `axi_bus_meter` uses — see `stream_char_harness.sv:587`).
- Add per-channel overflow stickies (bus_meter uses 16-bit per-channel counters
  + a 4-bit/channel overflow mask — replicate that resolution choice or go 32-bit).
- Surface as CSR-indexed readout (a `PERF_CH_SEL` index reg + readback regs) to
  avoid `NUM_CHANNELS × 4 × 2 buses` flat registers. See the existing OBS mux
  (`OBS_CTRL`/`OBS_DATA*` @ 0x2C0) for the indexed-readout pattern.
- **Acceptance:** per-channel buckets match `read_bus_meters.py` per-channel
  output for the same workload.

### Stage E.3 — RFC Stage D: latency histograms (the new data)
- Add per-transaction latency capture in `axi_monitor_base`: AR→first-R and
  AR→RLAST (reads), AW→B (writes). The transaction-tracking CAM already times
  transactions for timeout detection — reuse its timestamps.
- Bin into a histogram (e.g. 16 log2 bins). Per the RFC this is the one thing
  worth keeping as sparse packets *because* it is CSR-address-heavy — but the
  user chose the CSR route, so expose via **CSR-indexed window readout**:
  a `HIST_SEL` index (which bus, which metric, which bin) + a single `HIST_DATA`
  readback reg. Do NOT allocate 3×16×2 flat registers.
- **Acceptance:** histogram totals equal the corresponding burst/transaction
  counts; spot-check bin placement against known fixed-latency cosim transactions.

### Stage E.4 — Retire `axi_bus_meter` + legacy perf-packet path
- Delete `rtl/amba/shared/axi_bus_meter.sv` and its two instances +
  CSR readback in `stream_char_harness.sv` / `harness_csr.sv`
  (R-meter `+0x100`, W-meter `+0x180`; map documented at top of `harness_csr.sv`).
- Repoint `read_bus_meters.py` at the new monitor CSRs (or replace it with a
  generalized version of `read_desc_perf.py`). Update `run_characterization.py`
  to open/close the perf window and read the monitor CSRs instead of the meters.
- Retire the legacy `PktTypePerf` emission path
  (`rtl/amba/shared/axi_monitor_reporter_perf.sv`, gated by `cfg_*_mon_perf_enable`)
  only if it is no longer needed — confirm no other consumer relies on it first.
- **Acceptance:** the full sweep (`run_characterization.py`) produces the same
  four-bucket numbers it produces today, sourced from monitor CSRs.

---

## 6. Gotchas / decisions

- **Histogram CSR bulk.** 3 metrics × 16 bins × 2 buses × (aggregate + per-channel)
  is far too many flat registers. Use **indexed readout** (select reg + data reg),
  like the OBS mux. This is the main design decision in Stage E.3.
- **`window_cycles` live-only** — see §3. Use `bucket_total` after close.
- **Two `USE_AXI_MONITORS` variants** in `stream_top_ch8.sv` — wire perf outputs
  in both (variant 0 ties to 0). Forgetting variant 0 = lint/elab error.
- **W-channel has no `id`** — per-channel write attribution needs the engine
  sideband (`wr_active_channel_id/_valid`), already produced by `axi_write_engine.sv`
  and surfaced through `stream_core.sv`/`stream_top_ch8.sv` for the bus_meter.
- **CRITICAL RULE #0**: the regblock under
  `projects/components/stream/regs/generated/rtl/` is generated. After editing
  `stream_regs.rdl`, regenerate fully:
  ```
  cd projects/components/stream/rtl/macro
  peakrdl regblock stream_regs.rdl --cpuif passthrough -o ../../regs/generated/rtl/
  ```
  and mirror offsets in `projects/components/stream/rtl/stream_regmap.py`.
- **Area/timing**: two more full AXI monitors + per-channel arrays + histograms
  on the FPGA (xc7a100t) may stress utilization/timing. Check
  `make utilization` / `make timing` after the build; the baseline closed with
  WNS ≈ +0.007 ns, so there is little slack.

---

## 7. Validation checklist (acceptance gates)

1. `source env_python` before any pytest/verilator/Vivado.
2. Lint clean, **both** `USE_AXI_MONITORS` variants:
   ```
   verilator --lint-only --top-module stream_char_harness -f \
     projects/NexysA7/stream_characterization/flows-stream-bridge/rtl/filelists/stream_char_harness.f
   ```
   (set `REPO_ROOT STREAM_ROOT FRAMEWORK_ROOT FLOW_ROOT STREAM_CHAR_ROOT BRIDGE_ROOT`).
3. Cosim from `…/flows-stream-bridge/dv/tests`:
   - `TEST_TYPE=csr_read pytest test_stream_char.py` (no regression)
   - new `TEST_TYPE=rw_perf` (model on `desc_perf`) — buckets match bus_meter.
4. `make bitstream` (runs `regen-bridges` + `verify-sim` gate + Vivado build);
   confirm timing met (`make timing`) and utilization acceptable (`make utilization`).
5. `make program` → board `210292B7D46F` (UART `/dev/serial/by-id/usb-Digilent_Digilent_USB_Device_210292B7D46F-if01-port0`, typically `/dev/ttyUSB2`).
6. Run a known workload; confirm monitor-CSR buckets == legacy `axi_bus_meter`
   buckets (run both before deleting the meter, diff, *then* delete).

---

## 8. Key files (with anchors)

| Purpose | File |
|---|---|
| Perf primitives (ports, window FSM, buckets) | `rtl/amba/shared/axi_monitor_base.sv` (window FSM `:542`, buckets `:617`, `WIN_CLOSING` zero `:562`) |
| Read/write monitor wrappers | `rtl/amba/axi4/axi4_master_rd_mon.sv`, `axi4_master_wr_mon.sv` |
| Desc monitor instance (option-1 template) | `projects/components/stream/rtl/macro/scheduler_group_array.sv:499` |
| Datapath engines (where new monitors go) | `projects/components/stream/rtl/fub/axi_read_engine.sv`, `axi_write_engine.sv` |
| Core (dead `cfg_rdeng_mon_*`/`cfg_wreng_mon_*` hooks to reuse) | `projects/components/stream/rtl/macro/stream_core.sv` |
| Top (two `USE_AXI_MONITORS` variants) | `projects/components/stream/rtl/top/stream_top_ch8.sv` |
| CSR source (regenerate after edits) | `projects/components/stream/rtl/macro/stream_regs.rdl` |
| Generated regblock (RULE #0) | `projects/components/stream/regs/generated/rtl/stream_regs{,_pkg}.sv` |
| Python regmap mirror | `projects/components/stream/rtl/stream_regmap.py` |
| `axi_bus_meter` (to retire) | `rtl/amba/shared/axi_bus_meter.sv` |
| Bus-meter instances + harness CSR | `projects/NexysA7/stream_characterization/flows-stream-bridge/rtl/stream_char_harness.sv:1667,1699`; `…/stream_char_framework/rtl/harness_csr.sv` (R `+0x100`, W `+0x180`) |
| Host meter reader (to repoint) | `…/flows-stream-bridge/host/read_bus_meters.py` |
| Host desc-perf reader (template) | `…/flows-stream-bridge/host/read_desc_perf.py` |
| Characterization driver | `…/flows-stream-bridge/host/run_characterization.py` |
| Cosim TB + test (templates) | `…/flows-stream-bridge/dv/tbclasses/stream_char_tb.py`, `…/dv/tests/test_stream_char.py` |
| RFC | `rtl/amba/PRD/RFCs/RFC-perfmon-window-buckets.md` |
| Methodology | `DMA_UTILIZATION_MEASUREMENT.md` (Section 3 = four-bucket model) |

---

## 9. Conventions (this repo)

- `source env_python` before pytest/verilator/Vivado (sets `SIM=verilator`, PATH, PYTHONPATH).
- Reset macros: `\`include "reset_defs.svh"`, `\`ALWAYS_FF_RST(...)`, `\`RST_ASSERTED(...)`.
- Commit directly to `main`, **no** `Co-Authored-By` trailer; conventional-commit subjects.
- `projects/components/` tests use Pattern B (`cocotb_test_*` prefixed cocotb fns + pytest wrappers).
- No emojis in technical docs.
