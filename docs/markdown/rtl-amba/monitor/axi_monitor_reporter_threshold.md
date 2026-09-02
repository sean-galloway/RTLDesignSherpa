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
**Location:** `rtl/amba/monitor/`
**Status:** Production Ready

---

## Overview

The `axi_monitor_reporter_threshold` module is the threshold-crossing packet emitter for the AXI/AXIL monitor family. It is one of the per-packet-type sub-blocks dispatched by the top-level `axi_monitor_reporter`. It watches two conditions — the number of currently active transactions crossing a configured limit, and any transaction's measured latency exceeding a configured limit — and emits `PktTypeThreshold` packets when either crossing occurs.

The block was split out of the original monolithic reporter so integrators can drop it (`ENABLE_THRESHOLD_LOGIC=0`) and recover real area, because it owns the per-slot latency pipeline (16 x 32-bit latency flops plus 16 threshold flags).

`threshold` is a **fault class** ([taxonomy](monitor_system_architecture.md#healthy-classes-vs-fault-classes)) — an early-warning fault, one step below a hard timeout. Exercise it by **injecting a slow slave**: hold responses long enough that latency crosses `LATENCY_THRESH` but stays under the timeout window (or push enough concurrent traffic to cross the active-count limit). It does not occur under healthy traffic, so like the other faults it must be provoked deliberately.

Key features:

- Active-transaction-count threshold detection (instantaneous condition)
- Per-slot latency threshold detection with a registered latency pipeline
- Edge-sticky flags to fire once per crossing rather than every cycle
- Read/write latency measurement selectable via `IS_READ`
- Internal arbitration: active-count wins over latency events
- One packet at a time via `pkt_valid` / `pkt_taken` handshake
- Emits `AXI_THRESH_ACTIVE_COUNT` and `AXI_THRESH_LATENCY` event codes

Monitoring a bus for congestion and latency outliers requires two distinct checks: how many transactions are in flight right now, and whether any individual transaction took too long. This block performs both. The active count is computed combinationally by scanning the transaction table; latency is computed per slot in a registered pipeline (splitting the wide subtract-and-compare across a cycle to close timing) and compared against the configured latency threshold.

**Use cases:**

- Detecting bus congestion when outstanding-transaction count exceeds a budget
- Flagging latency-outlier transactions that exceed a service-level target
- Feeding threshold-crossing telemetry to a host for QoS monitoring
- Regression checks that latency stays within expected bounds

**Key benefit:** real area savings when disabled (the 16-deep latency pipeline is removed), plus a timing-friendly split of the latency compare so the wide carry chain does not sit on the packet-generation critical path.

---

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `MAX_TRANSACTIONS` | int | 16 | Number of transaction slots scanned for active count and latency |
| `IS_READ` | bit | 1'b1 | 1 = measure read latency (data - addr timestamp); 0 = measure write latency (resp - addr timestamp) |
| `IDX_W` | int | `$clog2(MAX_TRANSACTIONS)` | Derived width of the selected-slot index |

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|---|---|---|---|
| `aclk` | Input | 1 | Monitor clock |
| `aresetn` | Input | 1 | Active-low asynchronous reset |

### Transaction Table and Configuration

| Port | Direction | Width | Description |
|---|---|---|---|
| `trans_table` | Input | `bus_transaction_t [MAX_TRANSACTIONS]` | Live outstanding-transaction table (valid, state, timestamps, channel) |
| `cfg_threshold_enable` | Input | 1 | Enable threshold detection |
| `active_trans_threshold` | Input | 16 | Active-transaction-count limit; crossing above it fires a packet |
| `latency_threshold` | Input | 32 | Per-transaction latency limit (in timestamp ticks) |

### Handshake / Backpressure

| Port | Direction | Width | Description |
|---|---|---|---|
| `output_busy` | Input | 1 | Output bus busy (FIFO read or `monbus_valid`); threshold packets inject directly, so this prevents overwriting an in-flight one |
| `pkt_taken` | Input | 1 | Pulsed by the top reporter when this block's packet was accepted; **sets** the edge-sticky flag so the same crossing cannot re-fire. The flag clears only when the underlying condition lifts |

### Packet Output

| Port | Direction | Width | Description |
|---|---|---|---|
| `pkt_valid` | Output | 1 | A threshold packet is available this cycle |
| `pkt_type` | Output | 4 | Packet type — constant `PktTypeThreshold` (4'h2) |
| `pkt_event_code` | Output | 8 | Event code: `AXI_THRESH_ACTIVE_COUNT` (8'h0) or `AXI_THRESH_LATENCY` (8'h1) |
| `pkt_channel` | Output | 9 | Channel of the selected transaction (0 for active-count events) |
| `pkt_data` | Output | 64 | Zero-extended active count, or the zero-extended latency value |

---

## Functional Description

### Active-Count Detection

A combinational loop scans `trans_table` and counts slots that are `valid` and in a state other than `TRANS_COMPLETE` or `TRANS_ERROR` — that is, transactions genuinely in flight. `w_active_detect` asserts when threshold detection is enabled, the count strictly exceeds `active_trans_threshold`, the edge flag `r_active_crossed` is not already set, and the output is not busy. Because this reflects an instantaneous condition, it takes priority in the output mux.

### Per-Slot Latency Pipeline

For each slot, a registered pipeline computes latency from the live transaction table: `data_timestamp - addr_timestamp` for reads (`IS_READ=1`) or `resp_timestamp - addr_timestamp` for writes. The result is stored in `r_latency[idx]`, and a companion flag `r_latency_over_thresh[idx]` is set when the slot is valid, in `TRANS_COMPLETE` state, and its latency exceeds `latency_threshold`. It is deliberately **not** qualified by the latency edge flag — folding the flag in here would make the condition self-clearing, since the flag would suppress the very term that keeps it set. `r_latency_crossed` gates only the output mux. Registering the subtract and compare splits what would otherwise be a 16-wide carry chain plus output mux across a clock cycle.

### Latency Event Selection

A combinational priority encoder (`w_lat_sel` / `w_has_lat`) picks the first slot with `r_latency_over_thresh` asserted, off the registered pipeline so it does not recreate the wide combinational path.

### Edge-Sticky Flags

Two flags prevent re-firing on the same crossing every cycle:

- `r_active_crossed` — set when an active-count packet is accepted (`pkt_taken` with matching type/event code); cleared automatically when the active count drops back to or below the threshold.
- `r_latency_crossed` — set when a latency packet is accepted; gates further latency detections until re-armed.

### Output Multiplexer

Active-count beats latency. When `w_active_detect` is asserted, `pkt_valid` fires with `AXI_THRESH_ACTIVE_COUNT`, `pkt_data` = zero-extended active count, and `pkt_channel` = 0. Otherwise, when a latency event is pending and the output is free (`w_has_lat && !output_busy`), `pkt_valid` fires with `AXI_THRESH_LATENCY`, `pkt_data` = the selected slot's latency, and `pkt_channel` = that slot's channel (low 6 bits, zero-extended).

---

## Timing Characteristics

This module is **sequential**: it contains clocked logic (via `always_ff` or
the repository's `ALWAYS_FF_RST` macro) and therefore holds state. Outputs
driven from those blocks are registered and appear one clock after the inputs
that produced them.

Per-path cycle counts are not enumerated here; read the block that drives the
signal you care about. No synthesis frequency or area figures are quoted --
none have been measured against a target device.

Timing closure is therefore a question of the surrounding logic's slack, not of
this module's cycle count. No synthesis figures are quoted; none have been
measured.

---

## Usage Examples
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

The 16 x 32-bit latency registers plus 16 threshold flags are the reason disabling this block (`ENABLE_THRESHOLD_LOGIC=0`) yields a meaningful area reduction. When the feature is not needed, dropping the block removes the entire pipeline.

### Read vs Write Latency

`IS_READ` selects which timestamp pair defines latency. Instantiate a read-monitor threshold block with `IS_READ=1` and a write-monitor block with `IS_READ=0` so the measured interval matches the protocol phase of interest.

---

## Related Modules

**Used by:**

- **axi_monitor_reporter.sv** — instantiates this block as its threshold-packet sub-emitter
- **axi_monitor_base.sv** — top-level monitor scaffold

**Uses:**

- **monitor_common_pkg** — `PktTypeThreshold`, `bus_transaction_t`, transaction states
- **monitor_amba4_pkg** — `AXI_THRESH_ACTIVE_COUNT` / `AXI_THRESH_LATENCY` event codes
- **reset_defs.svh** — reset macros

**See also:**

- **axi_monitor_reporter_perf.sv** — performance packet emitter (sibling)
- **axi_monitor_reporter_timeout.sv** — timeout packet emitter (sibling)
- **axi_monitor_trans_mgr.sv** — maintains the `trans_table` consumed here

---

## Testing

**No dedicated testbench for this module.** It has no
`val/**/test_axi_monitor_reporter_threshold.py`. It is exercised indirectly, through the tests of
modules that instantiate it (directly or further up):

- `axi4_master_rd_mon` -- `val/**/test_axi4_master_rd_mon.py`
- `axi4_master_wr_mon` -- `val/**/test_axi4_master_wr_mon.py`
- `axi4_slave_rd_mon` -- `val/**/test_axi4_slave_rd_mon.py`
- `axi4_slave_wr_mon` -- `val/**/test_axi4_slave_wr_mon.py`
- `axi5_master_rd_mon` -- `val/**/test_axi5_master_rd_mon.py`

Indirect coverage exercises this module only in the configurations those
parents elaborate. A parameter or mode no parent uses is untested.

Treat any behaviour described on this page as unverified by simulation.

---

## References

### Source Code
- RTL: `rtl/amba/monitor/axi_monitor_reporter_threshold.sv`
- Parent: `rtl/amba/monitor/axi_monitor_reporter.sv`
- Packages: `rtl/amba/includes/monitor_common_pkg.sv`, `rtl/amba/includes/monitor_amba4_pkg.sv`

### Documentation
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- Monitor Base: `docs/markdown/rtl-amba/monitor/axi_monitor_base.md`
- Packet Format: `docs/markdown/rtl-amba/includes/monitor_package_spec.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- **[Back to Shared Infrastructure Index](../_book_monitor_index.md)**
- **[Back to rtl-amba Index](../index.md)**
