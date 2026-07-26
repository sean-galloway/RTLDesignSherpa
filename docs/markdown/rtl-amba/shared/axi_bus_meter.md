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

# AXI Bus Meter

**Module:** `axi_bus_meter.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The AXI Bus Meter is a per-cycle valid/ready classifier for a single AXI data channel. Every clock cycle it inspects the `valid` and `ready` handshake pair and attributes that cycle to one of four buckets — productive, backpressure, starvation, or idle — accumulating both aggregate (32-bit) and per-channel (16-bit) counts. It is a pure passive observer that drives nothing back onto the bus, making it safe to drop onto any live AXI R or W channel to characterize datapath utilization.

### Key Features

- Four-bucket per-cycle cycle classification (productive / backpressure / starvation / idle)
- Aggregate 32-bit counters (~42.9 s at 100 MHz before wrap) — always attributed based on bus state
- Per-channel 16-bit counters, `NUM_CHANNELS` deep, binned by a caller-supplied channel id
- Per-channel 4-bit sticky overflow mask flags counters that wrapped
- Synchronous one-cycle `i_clear` for atomic reset with the surrounding measurement substrate
- `i_freeze` window control to close the measurement window the instant the workload finishes
- Passive snoop — no protocol interaction, zero backpressure onto the metered bus

---

## Module Purpose

AXI datapath performance is dominated by how often data actually moves versus how often a handshake stalls. A raw throughput number cannot distinguish a slow producer (master not offering data) from a congested consumer (slave withholding `ready`). The AXI Bus Meter separates these root causes by classifying every cycle into one of four mutually-exclusive buckets, so a post-run analysis can compute utilization and, more importantly, attribute lost cycles to the correct side of the interface.

The block is instantiated one per bus to be measured. On a read engine it drops onto the R channel (aggregate plus per-channel via `rid`); on a write engine it drops onto the W channel (aggregate plus per-channel via an engine-side sideband, since AXI4 W beats carry no id).

**Use Cases:**
- Metering read R-bus and write W-bus utilization on the stream/rapids characterization engines
- Root-causing throughput shortfalls (backpressure-bound vs starvation-bound datapaths)
- Per-channel utilization breakdown in multi-channel DMA engines
- On-silicon performance characterization runs driven from a host CSR interface

**Key Benefit:** Turns a single throughput figure into an attributable four-way cycle budget, so lost bandwidth can be pinned to producer starvation or consumer backpressure per channel.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| NUM_CHANNELS | int | 8 | Number of per-channel bins (depth of the per-channel counter arrays) |
| CW | int | `(NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1` | Derived channel-id width; do not override |

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
| i_clear | input | 1 | Synchronous one-cycle clear pulse; zeroes all counters and overflow stickies |
| i_freeze | input | 1 | When high, every counter and overflow sticky holds its value (window closed) |

### AXI Bus Snoop

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_valid | input | 1 | Snooped channel `valid` (e.g. `m_axi_rvalid` / `m_axi_wvalid`) |
| i_ready | input | 1 | Snooped channel `ready` (e.g. `m_axi_rready` / `m_axi_wready`) |
| i_channel_id | input | CW | Channel index selecting the per-channel bin to increment this cycle |
| i_channel_valid | input | 1 | Gates per-channel accumulation; high when a channel is on the hook this cycle |

### Aggregate Counters

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| o_agg_productive | output | 32 | Cycles with `valid && ready` (data delivered) |
| o_agg_backpressure | output | 32 | Cycles with `valid && !ready` (master offering, slave stalling) |
| o_agg_starvation | output | 32 | Cycles with `!valid && ready` (slave ready, master not producing) |
| o_agg_idle | output | 32 | Cycles with `!valid && !ready` (both sides quiet) |

### Per-Channel Counters

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| o_ch_productive | output | 16 × NUM_CHANNELS | Per-channel productive-cycle counts |
| o_ch_backpressure | output | 16 × NUM_CHANNELS | Per-channel backpressure-cycle counts |
| o_ch_starvation | output | 16 × NUM_CHANNELS | Per-channel starvation-cycle counts |
| o_ch_idle | output | 16 × NUM_CHANNELS | Per-channel idle-cycle counts |
| o_ch_overflow | output | NUM_CHANNELS*4 | Sticky overflow mask, packed `{prod, bp, starv, idle}` per channel |

---

## Functional Description

### Bucket Classification

The four buckets are decoded combinationally from the handshake pair and are mutually exclusive — exactly one is asserted every cycle:

```
w_prod  =  i_valid &&  i_ready   // productive   — data delivered
w_bp    =  i_valid && !i_ready   // backpressure — master wants to send, slave stalls
w_starv = !i_valid &&  i_ready   // starvation   — slave ready, master not producing
w_idle  = !i_valid && !i_ready   // idle         — both sides quiet
```

This is the reference methodology documented in `DMA_UTILIZATION_MEASUREMENT.md` §3.

### Aggregate Counters

The four 32-bit aggregate counters always increment based on the raw bus state (subject only to `i_clear` and `i_freeze`). At 100 MHz a 32-bit counter lasts ~42.9 s before overflow — ample for a single characterization run. These provide the whole-bus utilization figure regardless of which channel was active.

### Per-Channel Counters and Overflow Stickies

The per-channel arrays are 16 bits wide and `NUM_CHANNELS` deep. Only the bin selected by `i_channel_id` is incremented, and only when `i_channel_valid` is high. The caller asserts `i_channel_valid` whenever some channel is on the hook for the current cycle (for example mid-burst); for cycles where the engine has no work on any channel, `i_channel_valid` is left low and only the aggregate idle/starvation counts are attributed.

Because 16 bits wraps after 65 536 cycles (~655 µs at 100 MHz), each per-channel counter has a companion sticky overflow bit. When a counter is at `16'hFFFF` and would increment again, its overflow bit latches high. The four bits per channel are packed `{prod, bp, starv, idle}` into `o_ch_overflow`. Software checks this mask after stopping the meter; any set bit means the burst outran 16-bit per-channel resolution and the per-channel numbers for that channel should be discarded (the aggregate 32-bit figures remain valid).

### Recommended Wiring

- **Read engine:** `i_valid = m_axi_rvalid`, `i_ready = m_axi_rready`, `i_channel_id = m_axi_rid[CW-1:0]`, `i_channel_valid = m_axi_rvalid` (rid is only meaningful when rvalid is high).
- **Write engine:** `i_valid = m_axi_wvalid`, `i_ready = m_axi_wready`, `i_channel_id =` the engine's internal write-channel-id sideband, `i_channel_valid =` a "W beats in flight on this channel" indicator (W beats carry no id in AXI4).

### Clear and Freeze Semantics

`i_clear` is a synchronous one-cycle pulse: on the cycle it is high, all counters and all overflow stickies reset to zero. It is intended to be wired to the same control bit that clears the surrounding measurement state (debug SRAM, harness CRC) so a single CSR write atomically resets the entire measurement substrate.

`i_freeze` holds every counter and sticky frozen while high — no bucket increments, no overflow flips. It is driven from the characterization timer's `done` so the window closes the moment the workload finishes. Without it, the lifetime starvation count would drift upward at one bit per cycle during post-burst host polling, contaminating the in-window utilization math. Hold `i_freeze` low for unbounded free-running measurement.

---

## Usage Example

```systemverilog
// Meter the read engine's R channel: aggregate + per-channel by rid.
axi_bus_meter #(
    .NUM_CHANNELS   (8)
) u_r_meter (
    .aclk               (aclk),
    .aresetn            (aresetn),

    // Window control (share with the char timer + CRC clear)
    .i_clear            (perf_run_rising),   // one-cycle pulse on RUN rising edge
    .i_freeze           (~perf_run),         // freeze when the window is closed

    // R channel snoop
    .i_valid            (m_axi_rvalid),
    .i_ready            (m_axi_rready),
    .i_channel_id       (m_axi_rid[2:0]),
    .i_channel_valid    (m_axi_rvalid),      // rid valid only when rvalid

    // Aggregate readback (to CSR / host)
    .o_agg_productive   (r_agg_prod),
    .o_agg_backpressure (r_agg_bp),
    .o_agg_starvation   (r_agg_starv),
    .o_agg_idle         (r_agg_idle),

    // Per-channel readback
    .o_ch_productive    (r_ch_prod),
    .o_ch_backpressure  (r_ch_bp),
    .o_ch_starvation    (r_ch_starv),
    .o_ch_idle          (r_ch_idle),
    .o_ch_overflow      (r_ch_overflow)
);

// Utilization = productive / (productive + backpressure + starvation + idle)
// Backpressure-heavy => consumer bound; starvation-heavy => producer bound.
```

---

## Design Notes

### Passive Observer

The meter drives nothing back onto the AXI bus — it only reads `valid`/`ready`. It can be added to or removed from a design without any protocol impact, and multiple meters can snoop different channels independently.

### Counter Width Rationale

Aggregate counters are 32-bit because they must survive a full-length run (~42.9 s at 100 MHz). Per-channel counters are deliberately kept at 16 bits to bound area across `NUM_CHANNELS` bins; the sticky overflow mask makes the resulting ~655 µs resolution limit self-diagnosing rather than silently wrong.

### Verilator Output Drivers

The per-channel register arrays are copied to the unpacked output arrays through explicit `always_comb` loops, and the overflow stickies are packed into `o_ch_overflow` with a `c*4 +: 4` slice, because Verilator cannot infer unpacked-array output assignments directly from a register array.

### Window Alignment

For correct in-window math, drive `i_clear` and `i_freeze` from the same window controller used by the companion `axi_perf_latency_hist` block so all meters open and close on the same cycle boundaries.

---

## Related Modules

### Used By
- `stream_char` datapath utilization metering (read R bus, write W bus)
- `rapids_char` AXI datapath meters (see `projects/NexysA7/.../rapids_char_harness.sv`)
- Host-driven on-silicon performance characterization harnesses

### Uses
- **reset_defs.svh** - `ALWAYS_FF_RST` / `RST_ASSERTED` reset macros

### See Also
- **axis_bus_meter.sv** - AXIS analogue with byte/packet throughput counters
- **axi_perf_latency_hist.sv** - Per-channel latency histogram, same window-control convention

---

## References

### Source Code
- RTL: `rtl/amba/shared/axi_bus_meter.sv`

### Documentation
- Methodology: `docs/.../DMA_UTILIZATION_MEASUREMENT.md` (window semantics, four-bucket definition)
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- Design Guide: `docs/markdown/rtl-amba/index.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to rtl-amba Index](../index.md)
