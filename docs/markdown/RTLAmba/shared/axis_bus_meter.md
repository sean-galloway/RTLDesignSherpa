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

# AXIS Bus Meter

**Module:** `axis_bus_meter.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The AXIS Bus Meter is the AXI-Stream analogue of `axi_bus_meter`. It performs the same four-bucket per-cycle valid/ready classification (productive / backpressure / starvation / idle), and adds AXIS-native throughput counters that are **window-independent**: a payload-byte count derived from `tstrb` popcount and a packet count derived from `tlast`. Because bytes and packets are counted only on productive beats, they measure exactly how much data moved regardless of how long the measurement window stays open — so throughput computed as bytes / busy-time is robust to backpressure and idle padding that would distort a pure cycle-utilization figure. Like its AXI cousin, it is a pure observer and drives nothing back onto the bus.

### Key Features

- Four-bucket per-cycle classification identical to `axi_bus_meter`
- Window-independent AXIS throughput counters: 64-bit bytes (via `tstrb` popcount), 32-bit beats, 32-bit packets (via `tlast`)
- Aggregate 32-bit cycle-bucket counters (~42.9 s at 100 MHz before wrap)
- Per-channel 16-bit cycle buckets binned by `tid`, with per-channel 4-bit sticky overflow
- Synchronous one-cycle `i_clear` and `i_freeze` window control
- Passive snoop of `tvalid`/`tready`/`tlast`/`tstrb`/`tid` — no bus interaction

---

## Module Purpose

Cycle-utilization alone is a fragile throughput proxy on a stream bus: if a window is held open for host polling after the last beat, idle cycles inflate and the utilization ratio drops even though the same number of bytes moved. The AXIS Bus Meter fixes this by counting the actual payload transferred. Every productive beat contributes `popcount(tstrb)` bytes to a 64-bit accumulator and, when `tlast` is set, one packet to a 32-bit accumulator. These are byte-exact and independent of window length, so the honest throughput figure is `bytes / busy_time`. The four cycle buckets are retained alongside for root-causing where non-productive time went.

The block is instantiated one per AXIS bus to be measured, snooping the stream signals as a passive observer.

**Use Cases:**
- Metering AXIS datapath throughput in the `rapids_char` characterization harness
- Byte-exact throughput measurement immune to window-hold artifacts
- Per-stream (per-`tid`) cycle-utilization breakdown on multi-stream buses
- Packet-rate measurement via `tlast` on framed streams

**Key Benefit:** Window-independent byte and packet counts give a throughput number that cannot be distorted by how long the host holds the measurement window open.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| DATA_WIDTH | int | 512 | Stream data width in bits (sets `tstrb`/byte-lane width) |
| NUM_CHANNELS | int | 8 | Number of per-channel (`tid`) bins |
| TID_WIDTH | int | `(NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1` | `tid` bus width; derived, do not override |
| SW | int | `DATA_WIDTH / 8` | `tstrb` width (byte lanes); derived |
| CW | int | `(NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1` | Channel-bin index width; derived |

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
| i_clear | input | 1 | Synchronous one-cycle clear pulse; zeroes every counter and sticky |
| i_freeze | input | 1 | Hold high to close the measurement window (no counter moves) |

### AXIS Bus Snoop

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_tvalid | input | 1 | Stream `tvalid` |
| i_tready | input | 1 | Stream `tready` |
| i_tlast | input | 1 | Stream `tlast` (increments packet count on a productive beat) |
| i_tstrb | input | SW | Byte-lane strobes; popcount gives this beat's payload byte count |
| i_tid | input | TID_WIDTH | Stream id; its low CW bits select the per-channel bin |

### Aggregate Cycle Buckets

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| o_agg_productive | output | 32 | Cycles with `tvalid && tready` (beat transferred) |
| o_agg_backpressure | output | 32 | Cycles with `tvalid && !tready` |
| o_agg_starvation | output | 32 | Cycles with `!tvalid && tready` |
| o_agg_idle | output | 32 | Cycles with `!tvalid && !tready` |

### Aggregate AXIS-Native Throughput (productive beats only)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| o_agg_bytes | output | 64 | Sum of `popcount(tstrb)` over productive beats — exact payload bytes moved |
| o_agg_beats | output | 32 | Productive beat count (equals `o_agg_productive`; provided for convenience) |
| o_agg_packets | output | 32 | Productive beats with `tlast` asserted (stream packets) |

### Per-Channel Cycle Buckets (binned by tid)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| o_ch_productive | output | 16 × NUM_CHANNELS | Per-channel productive-cycle counts |
| o_ch_backpressure | output | 16 × NUM_CHANNELS | Per-channel backpressure-cycle counts |
| o_ch_starvation | output | 16 × NUM_CHANNELS | Per-channel starvation-cycle counts |
| o_ch_idle | output | 16 × NUM_CHANNELS | Per-channel idle-cycle counts (always zero — see Design Notes) |
| o_ch_overflow | output | NUM_CHANNELS*4 | Sticky overflow mask, packed `{prod, bp, starv, idle}` per channel |

---

## Functional Description

### Bucket Classification

Identical to `axi_bus_meter`: the handshake pair decodes combinationally into four mutually-exclusive buckets.

```
w_prod  =  i_tvalid &&  i_tready   // productive   — beat transferred
w_bp    =  i_tvalid && !i_tready   // backpressure — master wants to send, slave stalls
w_starv = !i_tvalid &&  i_tready   // starvation   — slave ready, master not producing
w_idle  = !i_tvalid && !i_tready   // idle         — both sides quiet
```

See `DMA_UTILIZATION_MEASUREMENT.md` §3 for the reference methodology.

### Payload-Byte Popcount

Each beat's byte count is the number of asserted `tstrb` lanes, computed combinationally by summing the strobe bits into `w_beat_bytes`. If the stream has no meaningful `tstrb`, tie it all-ones so bytes accumulate as `beats × (DATA_WIDTH/8)`.

### AXIS-Native Throughput Counters

On every productive beat (`tvalid && tready`, window open):

- `o_agg_bytes` += this beat's `popcount(tstrb)` — a 64-bit accumulator that will not wrap in any realistic run.
- `o_agg_beats` += 1 — a convenience mirror of `o_agg_productive`.
- `o_agg_packets` += 1 when `i_tlast` is set — counts framed stream packets.

Because these advance only on productive beats, they are window-length independent: holding `i_freeze` low longer only accumulates more idle cycles in the aggregate buckets, never more bytes or packets.

### Per-Channel Cycle Buckets

Per-channel buckets are 16-bit, `NUM_CHANNELS` deep, binned by the low `CW` bits of `tid` (`w_ch`). AXIS carries `tid` on every valid cycle, so the productive, backpressure, and starvation buckets are attributed to `w_ch` whenever the bus is active. Each per-channel counter has a companion sticky overflow bit (`{prod, bp, starv, idle}` packed into `o_ch_overflow`) that latches when the counter would advance past `16'hFFFF`, exactly as in `axi_bus_meter`. Software discards the per-channel numbers for any channel whose overflow mask is nonzero.

### Clear and Freeze Semantics

`i_clear` is a synchronous one-cycle pulse that zeroes every counter and sticky. `i_freeze` holds all counters frozen while high and is driven from the characterization window controller so the window closes the moment the workload finishes.

---

## Usage Example

```systemverilog
// Meter an AXIS bus: cycle buckets + byte/packet throughput, per-tid bins.
axis_bus_meter #(
    .DATA_WIDTH     (512),
    .NUM_CHANNELS   (8)
) u_axis_meter (
    .aclk               (aclk),
    .aresetn            (aresetn),

    .i_clear            (perf_run_rising),
    .i_freeze           (~perf_run),

    // Stream snoop (all inputs — passive)
    .i_tvalid           (s_axis_tvalid),
    .i_tready           (s_axis_tready),
    .i_tlast            (s_axis_tlast),
    .i_tstrb            (s_axis_tstrb),      // tie all-ones if the stream has no tstrb
    .i_tid              (s_axis_tid),

    // Aggregate cycle buckets
    .o_agg_productive   (agg_prod),
    .o_agg_backpressure (agg_bp),
    .o_agg_starvation   (agg_starv),
    .o_agg_idle         (agg_idle),

    // Window-independent throughput
    .o_agg_bytes        (agg_bytes),
    .o_agg_beats        (agg_beats),
    .o_agg_packets      (agg_packets),

    // Per-channel (by tid)
    .o_ch_productive    (ch_prod),
    .o_ch_backpressure  (ch_bp),
    .o_ch_starvation    (ch_starv),
    .o_ch_idle          (ch_idle),
    .o_ch_overflow      (ch_overflow)
);

// Honest throughput = o_agg_bytes / busy_time  (immune to window-hold padding)
```

---

## Design Notes

### Why Byte/Packet Counters Are Window-Independent

A pure cycle-utilization ratio drops if the window is held open past the last beat (host polling adds idle cycles). Byte and packet counters advance only on productive beats, so they capture the true transferred payload no matter how long the window is held. Reporting `bytes / busy_time` sidesteps the padding-sensitivity of `productive / total_cycles`.

### Per-Channel Idle Is Not Attributed

Idle cycles (`!tvalid && !tready`) cannot be assigned to any stream — no `tid` is meaningful when nothing is on the bus — so `r_ch_idle` is never incremented and `o_ch_idle` stays zero. Idle cycles land only in the aggregate `o_agg_idle`. The per-channel idle output and its overflow bit are kept for structural symmetry with `axi_bus_meter`.

### tstrb Handling

If the source does not drive a meaningful `tstrb`, tie it all-ones so `o_agg_bytes` equals `beats × (DATA_WIDTH/8)`. Otherwise `o_agg_bytes` reflects sparse/partial beats exactly.

### Counter Widths

Cycle buckets are 32-bit (aggregate) / 16-bit (per-channel) matching `axi_bus_meter`. Bytes are 64-bit to guarantee no wrap; beats and packets are 32-bit.

---

## Related Modules

### Used By
- `rapids_char` AXIS datapath meters (characterization harness)
- Host-driven AXIS throughput characterization runs

### Uses
- **reset_defs.svh** - `ALWAYS_FF_RST` / `RST_ASSERTED` reset macros

### See Also
- **axi_bus_meter.sv** - AXI channel four-bucket meter (this module's origin)
- **axi_perf_latency_hist.sv** - Latency histogram sharing the same window-control convention

---

## References

### Source Code
- RTL: `rtl/amba/shared/axis_bus_meter.sv`

### Documentation
- Methodology: `docs/.../DMA_UTILIZATION_MEASUREMENT.md` (four-bucket definition, window semantics)
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- Design Guide: `docs/markdown/RTLAmba/index.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
