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

# AXI Monitor Reporter — Threshold Packets

**Module:** `axi_monitor_reporter_threshold.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The `axi_monitor_reporter_threshold` module is the threshold-crossing packet emitter for the AXI/AXIL monitor family. It is one of the per-packet-type sub-blocks dispatched by the top-level `axi_monitor_reporter`. It watches two conditions — the number of currently active transactions crossing a configured limit, and any transaction's measured latency exceeding a configured limit — and emits `PktTypeThreshold` packets when either crossing occurs.

The block was split out of the original monolithic reporter so integrators can drop it (`ENABLE_THRESHOLD_LOGIC=0`) and recover real area, because it owns the per-slot latency pipeline (16 × 32-bit latency flops plus 16 threshold flags).

### Key Features

- Active-transaction-count threshold detection (instantaneous condition)
- Per-slot latency threshold detection with a registered latency pipeline
- Edge-sticky flags to fire once per crossing rather than every cycle
- Read/write latency measurement selectable via `IS_READ`
- Internal arbitration: active-count wins over latency events
- One packet at a time via `pkt_valid` / `pkt_taken` handshake
- Emits `AXI_THRESH_ACTIVE_COUNT` and `AXI_THRESH_LATENCY` event codes

---

## Module Purpose

Monitoring a bus for congestion and latency outliers requires two distinct checks: how many transactions are in flight right now, and whether any individual transaction took too long. This block performs both. The active count is computed combinationally by scanning the transaction table; latency is computed per slot in a registered pipeline (splitting the wide subtract-and-compare across a cycle to close timing) and compared against the configured latency threshold.

**Use Cases:**
- Detecting bus congestion when outstanding-transaction count exceeds a budget
- Flagging latency-outlier transactions that exceed a service-level target
- Feeding threshold-crossing telemetry to a host for QoS monitoring
- Regression checks that latency stays within expected bounds

**Key Benefit:** Real area savings when disabled (the 16-deep latency pipeline is removed), plus a timing-friendly split of the latency compare so the wide carry chain does not sit on the packet-generation critical path.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `MAX_TRANSACTIONS` | int | 16 | Number of transaction slots scanned for active count and latency |
| `IS_READ` | bit | 1'b1 | 1 = measure read latency (data − addr timestamp); 0 = measure write latency (resp − addr timestamp) |
| `IDX_W` | int | `$clog2(MAX_TRANSACTIONS)` | Derived width of the selected-slot index |

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `aclk` | input | 1 | Monitor clock |
| `aresetn` | input | 1 | Active-low asynchronous reset |

### Transaction Table and Configuration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `trans_table` | input | `bus_transaction_t [MAX_TRANSACTIONS]` | Live outstanding-transaction table (valid, state, timestamps, channel) |
| `cfg_threshold_enable` | input | 1 | Enable threshold detection |
| `active_trans_threshold` | input | 16 | Active-transaction-count limit; crossing above it fires a packet |
| `latency_threshold` | input | 32 | Per-transaction latency limit (in timestamp ticks) |

### Handshake / Backpressure

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `output_busy` | input | 1 | Output bus busy (FIFO read or `monbus_valid`); threshold packets inject directly, so this prevents overwriting an in-flight one |
| `pkt_taken` | input | 1 | Pulsed by the top reporter when this block's packet was accepted; clears the edge flag and arms the next detection |

### Packet Output

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `pkt_valid` | output | 1 | A threshold packet is available this cycle |
| `pkt_type` | output | 4 | Packet type — constant `PktTypeThreshold` (4'h2) |
| `pkt_event_code` | output | 8 | Event code: `AXI_THRESH_ACTIVE_COUNT` (8'h0) or `AXI_THRESH_LATENCY` (8'h1) |
| `pkt_channel` | output | 9 | Channel of the selected transaction (0 for active-count events) |
| `pkt_data` | output | 64 | Zero-extended active count, or the zero-extended latency value |

---

## Functional Description

### Active-Count Detection

A combinational loop scans `trans_table` and counts slots that are `valid` and in a state other than `TRANS_COMPLETE` or `TRANS_ERROR` — that is, transactions genuinely in flight. `w_active_detect` asserts when threshold detection is enabled, the count strictly exceeds `active_trans_threshold`, the edge flag `r_active_crossed` is not already set, and the output is not busy. Because this reflects an instantaneous condition, it takes priority in the output mux.

### Per-Slot Latency Pipeline

For each slot, a registered pipeline computes latency from the live transaction table: `data_timestamp − addr_timestamp` for reads (`IS_READ=1`) or `resp_timestamp − addr_timestamp` for writes. The result is stored in `r_latency[idx]`, and a companion flag `r_latency_over_thresh[idx]` is set when the slot is valid, in `TRANS_COMPLETE` state, its latency exceeds `latency_threshold`, and the latency edge flag is not already set. Registering the subtract and compare splits what would otherwise be a 16-wide carry chain plus output mux across a clock cycle.

### Latency Event Selection

A combinational priority encoder (`w_lat_sel` / `w_has_lat`) picks the first slot with `r_latency_over_thresh` asserted, off the registered pipeline so it does not recreate the wide combinational path.

### Edge-Sticky Flags

Two flags prevent re-firing on the same crossing every cycle:

- `r_active_crossed` — set when an active-count packet is accepted (`pkt_taken` with matching type/event code); cleared automatically when the active count drops back to or below the threshold.
- `r_latency_crossed` — set when a latency packet is accepted; gates further latency detections until re-armed.

### Output Multiplexer

Active-count beats latency. When `w_active_detect` is asserted, `pkt_valid` fires with `AXI_THRESH_ACTIVE_COUNT`, `pkt_data` = zero-extended active count, and `pkt_channel` = 0. Otherwise, when a latency event is pending and the output is free (`w_has_lat && !output_busy`), `pkt_valid` fires with `AXI_THRESH_LATENCY`, `pkt_data` = the selected slot's latency, and `pkt_channel` = that slot's channel (low 6 bits, zero-extended).

---

## Usage Example

This block is instantiated inside `axi_monitor_reporter`, not by users directly:

```systemverilog
axi_monitor_reporter_threshold #(
    .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
    .IS_READ          (IS_READ)
) u_reporter_threshold (
    .aclk                   (aclk),
    .aresetn                (aresetn),

    .trans_table            (w_trans_table),
    .cfg_threshold_enable   (cfg_threshold_enable),
    .active_trans_threshold (cfg_active_trans_threshold),
    .latency_threshold      (cfg_latency_threshold),

    .output_busy            (w_output_busy),
    .pkt_taken              (w_thresh_pkt_taken),

    .pkt_valid              (w_thresh_pkt_valid),
    .pkt_type               (w_thresh_pkt_type),
    .pkt_event_code         (w_thresh_pkt_event_code),
    .pkt_channel            (w_thresh_pkt_channel),
    .pkt_data               (w_thresh_pkt_data)
);
```

---

## Design Notes

### Threshold Packets Bypass the FIFO

Unlike error/completion packets, threshold packets inject directly into the output rather than routing through the reporter FIFO. That is why the block needs `output_busy` — to avoid overwriting a packet already in flight on the MonBus.

### Active Count vs Latency Priority

Active count is an instantaneous, whole-table condition; latency is a per-slot event that has already been captured in the pipeline flag. The mux deliberately favors the active-count crossing so the more time-sensitive congestion signal is never starved by a queue of latency reports.

### Latency Pipeline Is the Area Cost

The 16 × 32-bit latency registers plus 16 threshold flags are the reason disabling this block (`ENABLE_THRESHOLD_LOGIC=0`) yields a meaningful area reduction. When the feature is not needed, dropping the block removes the entire pipeline.

### Read vs Write Latency

`IS_READ` selects which timestamp pair defines latency. Instantiate a read-monitor threshold block with `IS_READ=1` and a write-monitor block with `IS_READ=0` so the measured interval matches the protocol phase of interest.

---

## Related Modules

### Used By
- **axi_monitor_reporter.sv** — instantiates this block as its threshold-packet sub-emitter
- **axi_monitor_base.sv** — top-level monitor scaffold

### Uses
- **monitor_common_pkg** — `PktTypeThreshold`, `bus_transaction_t`, transaction states
- **monitor_amba4_pkg** — `AXI_THRESH_ACTIVE_COUNT` / `AXI_THRESH_LATENCY` event codes
- **reset_defs.svh** — reset macros

### See Also
- **axi_monitor_reporter_perf.sv** — performance packet emitter (sibling)
- **axi_monitor_reporter_timeout.sv** — timeout packet emitter (sibling)
- **axi_monitor_trans_mgr.sv** — maintains the `trans_table` consumed here

---

## References

### Source Code
- RTL: `rtl/amba/shared/axi_monitor_reporter_threshold.sv`
- Parent: `rtl/amba/shared/axi_monitor_reporter.sv`
- Packages: `rtl/amba/includes/monitor_common_pkg.sv`, `rtl/amba/includes/monitor_amba4_pkg.sv`

### Documentation
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- Monitor Base: `docs/markdown/RTLAmba/axi_monitor_base.md`
- Packet Format: `docs/markdown/RTLAmba/includes/monitor_package_spec.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
