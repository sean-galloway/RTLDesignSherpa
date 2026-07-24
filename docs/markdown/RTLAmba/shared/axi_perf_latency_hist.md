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

# AXI Performance Latency Histogram

**Module:** `axi_perf_latency_hist.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The AXI Performance Latency Histogram captures per-transaction latency on an AXI master bus and bins it into a log2 histogram surfaced through a CSR-indexed readout (no MonBus packets). It is a self-contained snoop block — it does not gate or otherwise touch the AXI datapath — and is instantiated alongside the datapath monitors, deliberately leaving the shared `axi_monitor_base` untouched. For reads it measures both AR→first-R and AR→RLAST latency; for writes it measures AW→B latency.

### Key Features

- Per-channel log2 latency histogram (default 16 bins: bin `b` counts latencies in `[2^b, 2^(b+1))`)
- Read mode (`IS_READ=1`): two metrics — AR→first-R beat and AR→RLAST
- Write mode (`IS_READ=0`): one metric — AW→B response
- Per-channel command-timestamp FIFO matches completions to oldest outstanding command (same-ID in-order)
- Four-stage histogram update pipeline for FPGA timing closure
- Free-running (non-frozen) timestamp so latencies straddling the window boundary stay correct
- CSR-indexed readout of any bin count plus each metric's transaction total
- Window control (`i_clear` / `i_freeze`) mirroring `axi_bus_meter`

---

## Module Purpose

Average latency hides the distribution that actually matters for QoS analysis — a bus can have a fine mean while a tail of slow transactions strangles a real workload. This block bins each transaction's measured latency into a log2 histogram, so the shape of the distribution (and its tail) is visible from a handful of CSR reads. It snoops the command and completion channels, timestamps each command as it is accepted, and on completion subtracts to get latency and increments the matching log2 bin. It is purely observational and adds no load to the AXI path, so it can be dropped in for characterization without perturbing the design under measurement.

**Use Cases:**
- Read/write latency distribution characterization on AXI master ports (perfmon Stage D)
- Tail-latency analysis for QoS and arbitration tuning
- Parity latency metrics alongside `axi4_dma_observer` per-port histograms
- Host-driven on-silicon performance runs (CSR readout, no MonBus traffic)

**Key Benefit:** Exposes the full latency distribution (including the tail) per channel through cheap CSR reads, without touching the shared monitor base or adding any MonBus packet traffic.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ID_WIDTH | int | 8 | AXI id width on the snooped bus |
| NUM_CHANNELS | int | 8 | Number of per-channel bins (channel = `id[CW-1:0]`) |
| MAX_OUTSTANDING | int | 8 | Per-channel command-timestamp FIFO depth |
| NUM_BINS | int | 16 | Number of log2 histogram bins; bin `b` counts `[2^b, 2^(b+1))` |
| IS_READ | bit | 1'b1 | 1 = read build (2 metrics), 0 = write build (1 metric) |
| CNT_W | int | 32 | Histogram bin and total counter width |
| CW | int | derived | `$clog2(NUM_CHANNELS)` — channel index width |
| PW | int | derived | `$clog2(MAX_OUTSTANDING)` — FIFO pointer width |
| PW1 | int | derived | `PW + 1` — occupancy width (extra bit for full) |
| BINW | int | derived | `$clog2(NUM_BINS)` — bin index width |

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | Clock |
| aresetn | input | 1 | Active-low asynchronous reset |

### Window Control

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_clear | input | 1 | One-cycle pulse (perf RUN rising edge): resets histogram + FIFOs |
| i_freeze | input | 1 | Hold high to freeze the histogram (counters stop; readback stable) |

### Command Channel (AR for reads, AW for writes)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cmd_valid | input | 1 | Command-channel valid |
| cmd_ready | input | 1 | Command-channel ready (handshake timestamps the command) |
| cmd_id | input | ID_WIDTH | Command id; low CW bits select the channel |

### Read Data Channel (R) — used when IS_READ=1

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| data_valid | input | 1 | R-channel valid |
| data_ready | input | 1 | R-channel ready |
| data_last | input | 1 | R-channel `rlast` (marks the RLAST metric / FIFO pop) |
| data_id | input | ID_WIDTH | R-channel id; low CW bits select the channel |

### Write Response Channel (B) — used when IS_READ=0

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| resp_valid | input | 1 | B-channel valid |
| resp_ready | input | 1 | B-channel ready |
| resp_id | input | ID_WIDTH | B-channel id; low CW bits select the channel |

### CSR-Indexed Readout

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_hist_metric | input | 1 | Metric select: 0 = first-R/B, 1 = RLAST (reads only) |
| i_hist_bin | input | BINW | Bin index to read |
| o_hist_count | output | CNT_W | Selected bin's count for the selected metric |
| o_hist_total | output | CNT_W | Selected metric's total transaction count |

---

## Functional Description

### Metrics

- **`IS_READ=1` (read build), `NUM_METRICS=2`:** metric 0 = AR handshake → first R beat; metric 1 = AR handshake → RLAST beat.
- **`IS_READ=0` (write build), `NUM_METRICS=1`:** metric 0 = AW handshake → B response.

The histogram storage is always sized for two metrics for uniform indexing; the write build uses only metric 0.

### Transaction Matching

AXI requires same-ID responses to return in order, so completions can be matched to commands with a simple per-channel FIFO of command-phase timestamps rather than a CAM. On a command handshake (`cmd_valid && cmd_ready`) the current free-running time is pushed into the channel's FIFO (bounded by `MAX_OUTSTANDING`). On completion the oldest timestamp for that channel (`r_ts[ch][head]`) is the start time, and the FIFO is popped when the completing beat is `last` (RLAST for reads; B is always "last" for writes). A single AXI data/response bus carries at most one beat per cycle, so at most one push and one pop occur per cycle — there is no multi-writer hazard on the shared histogram.

For reads, a per-channel `r_burst_active` flag distinguishes the first R beat (metric 0, AR→first-R) from subsequent beats of the same burst; it is set on the first beat and cleared when the burst pops on RLAST.

### Log2 Binning

`latency_bin()` returns `floor(log2(lat))` clamped to `NUM_BINS-1`; latencies of 0 or 1 map to bin 0. Bin `b` therefore counts latencies in `[2^b, 2^(b+1))`.

### Free-Running Timestamp

`r_time` is a 32-bit counter that increments every cycle and is **not** frozen by `i_freeze`. Keeping it running means a latency measurement that straddles the window-close boundary still subtracts two consistent absolute timestamps and yields the correct value. Only the histogram accumulation is frozen.

### Four-Stage Update Pipeline

The chain FIFO-read → latency subtract → log2 bin → indexed histogram increment is far too deep for a single 100 MHz cycle (it was the routed critical path), so it is split into four register stages:

- **Stage 0:** capture the event — `{start_ts, time, metric flags m0/m1, valid}`. Gated by `i_freeze` (a frozen window captures no new events).
- **Stage 1:** latency = completion time − start time.
- **Stage 2:** log2 bin from the latency.
- **Stage 3:** increment the selected histogram bin(s) and the per-metric total(s).

The increment is delayed a few cycles, but the host reads the window long after RUN drops to 0, by which time the pipeline has drained — `i_freeze` gates stage 0 while stages 1–3 keep advancing to flush. Because a single AXI bus completes at most one transaction per cycle and metrics m0/m1 target different histograms, consecutive same-bin increments are hazard-free (the cross-cycle NBA read-after-write is correct).

### Window Control

`i_clear` (a one-cycle pulse on the perf RUN rising edge) resets the histograms, totals, and all per-channel FIFOs and state. `i_freeze` (`~RUN`) holds the histogram so a closed window can be read back, while the free-running timestamp keeps counting.

### Readout

Readout is a combinational mux: `o_hist_count` returns `r_hist[metric][bin]` for the CSR-selected metric and bin, and `o_hist_total` returns that metric's running transaction total (useful for normalizing bin counts into a distribution).

---

## Usage Example

```systemverilog
// Read-latency histogram on an AXI master read port (2 metrics: first-R, RLAST).
axi_perf_latency_hist #(
    .ID_WIDTH        (8),
    .NUM_CHANNELS    (8),
    .MAX_OUTSTANDING (8),
    .NUM_BINS        (16),
    .IS_READ         (1'b1)
) u_rd_lat_hist (
    .aclk           (aclk),
    .aresetn        (aresetn),

    // Window control (share with axi_bus_meter)
    .i_clear        (perf_run_rising),
    .i_freeze       (~perf_run),

    // AR command channel
    .cmd_valid      (m_axi_arvalid),
    .cmd_ready      (m_axi_arready),
    .cmd_id         (m_axi_arid),

    // R data channel
    .data_valid     (m_axi_rvalid),
    .data_ready     (m_axi_rready),
    .data_last      (m_axi_rlast),
    .data_id        (m_axi_rid),

    // B channel unused for reads
    .resp_valid     (1'b0),
    .resp_ready     (1'b0),
    .resp_id        ('0),

    // CSR readout
    .i_hist_metric  (csr_metric),   // 0 = AR->first-R, 1 = AR->RLAST
    .i_hist_bin     (csr_bin),
    .o_hist_count   (csr_bin_count),
    .o_hist_total   (csr_metric_total)
);

// Write build: set IS_READ=0, wire AW to cmd_* and B to resp_*, leave data_* tied off.
```

---

## Design Notes

### Snoop-Only, Base Untouched

The block is instantiated next to the datapath monitors but does not modify `axi_monitor_base`; it snoops the AXI channels read-only and emits no MonBus packets. Results leave exclusively through the CSR-indexed readout.

### Timestamp Not Frozen

Only histogram accumulation freezes on `i_freeze`; `r_time` keeps counting so a transaction whose command was accepted before the window closed and whose completion arrives just after still yields a correct latency.

### FIFO Depth vs Outstanding

`MAX_OUTSTANDING` bounds the per-channel timestamp FIFO. A command handshake only pushes when the channel FIFO is not full, and a completion only pops when the FIFO is non-empty, so an over-run on one channel cannot corrupt another. Size `MAX_OUTSTANDING` to the real per-channel outstanding depth of the bus.

### Pipeline Drain Before Readback

Because increments land up to three cycles after the completing beat, always read the histogram after the window has been closed (`i_freeze` high) long enough for the pipeline to drain — the host reads long after RUN falls, so this is automatic in the intended usage.

---

## Related Modules

### Used By
- Perfmon Stage D characterization (see RFC below)
- Datapath-monitor instantiations needing latency distributions alongside `axi_bus_meter`

### Uses
- **reset_defs.svh** - `ALWAYS_FF_RST` / `RST_ASSERTED` reset macros

### See Also
- **axi_bus_meter.sv** - Four-bucket utilization meter, shares the window-control convention
- **axi4_dma_observer.sv** - DMA observability wrapper with per-port latency histograms
- **axi_monitor_base.sv** - The shared monitor scaffold this block deliberately does not touch

---

## References

### Source Code
- RTL: `rtl/amba/shared/axi_perf_latency_hist.sv`

### Documentation
- RFC: `docs/markdown/RTLAmba/index.md`
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- Design Guide: `docs/markdown/RTLAmba/index.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
