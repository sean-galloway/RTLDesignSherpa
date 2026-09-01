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

# AXI4 Slave Read Monitor (Clock-Gated)

**Module:** `axi4_slave_rd_mon_cg.sv`
**Base Module:** [axi4_slave_rd_mon](./axi4_slave_rd_mon.md)
**Location:** `rtl/amba/axi4/` (protocol monitors live with their protocol; only the monitor CORE pieces are in `rtl/amba/monitor/`)
**Status:** Production Ready

---

## Overview

This is the **clock-gated variant** of [axi4_slave_rd_mon](./axi4_slave_rd_mon.md) — the same monitored slave read, with activity-based clock gating wrapped around it.

For complete clock-gating documentation, usage examples, and configuration guidelines, see the **[Clock-Gated Variants Guide](../shared/clock_gated_variants.md)**.

What the wrapper buys you:

- **Same Functionality:** 100% equivalent to base module
- **Power Savings:** traffic-dependent; unmeasured in this repo -- treat any percentage as a placeholder until characterized
- **Configurable:** Idle threshold, gating domains, enable/disable
- **Zero Overhead When Disabled:** `cfg_cg_enable=0` bypasses the gate at runtime

---

## Parameters

MOST [axi4_slave_rd_mon](./axi4_slave_rd_mon.md) parameters pass through. As of 2026-09-01 only
`ACTIVE_TRANS_THRESHOLD` is NOT forwarded, and that one is harmless: its inner
default is `MAX_TRANSACTIONS/2`, computed from the `MAX_TRANSACTIONS` this
wrapper DOES forward.

An earlier version of this page listed nine more as unforwarded, which was
accurate when written. `ACLK_MHZ`, `CFI_MIN_FREQ_MHZ`, `CFI_MAX_FREQ_MHZ`,
`USE_WDATA_ORDER_Q`, `NUM_BANKS` and `ADDR_RANGE_IS_ERROR` were threaded
through every `_cg` wrapper on 2026-09-01, and `ID_FILTER_ENABLE` /
`ID_MATCH_BASE` / `ID_MATCH_COUNT` the day before. Until then a clock-gated
build could not state its clock frequency, so the 1 us timer tick was pinned
to the 100 MHz default and every microsecond-denominated timeout was
miscalibrated on any other clock -- silently.

| Parameter | Default | Description |
|-----------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | 4 | Width of the idle countdown, sizing `cfg_cg_idle_count` |
| `USE_MONITOR` | 1 | Synthesis-time monitor enable (forwarded to inner monitor). |
| `N_ADDR_RANGES` | 0 | Number of address-range comparators (forwarded to base module). |
| `ADDR_FILTER_ENABLE` | 0 | Synthesises the address-range report filter. **The parameter only decides whether the logic EXISTS** -- a build that sets it and leaves `cfg_addr_filter_enable` low filters nothing and looks broken. |
| `ID_FILTER_ENABLE` | 0 | Synthesises the ID report filter (see `cfg_id_*` for the runtime override). |
| `ID_MATCH_BASE` | 0 | First ID this instance owns. |
| `ID_MATCH_COUNT` | 0 | How many IDs; `0` means ALL, so a zeroed register block does not silently filter everything away. |

Gating is controlled by RUNTIME inputs `cfg_cg_enable` /
`cfg_cg_idle_count` with status outputs `cg_gating` / `cg_idle`; ONE
`amba_clock_gate_ctrl` gates the entire inner module. (The
ENABLE_CLOCK_GATING / CG_IDLE_CYCLES / CG_GATE_* interface this page once
documented never existed.)

Base-module ports are forwarded EXCEPT `debug_block_ready`, which this wrapper ties off (use the base module for the backpressure tap) -- including the full performance-monitoring interface (see [Performance Monitoring](#performance-monitoring) below). The six `ENABLE_*_LOGIC` synthesis-cone parameters (`ENABLE_ERROR_LOGIC`, `ENABLE_TIMEOUT_LOGIC`, `ENABLE_COMPL_LOGIC`, `ENABLE_THRESHOLD_LOGIC`, `ENABLE_PERF_LOGIC`, `ENABLE_DEBUG_LOGIC`) and the `cfg_compl_enable` / `cfg_threshold_enable` / `cfg_debug_enable` control enables are also passed straight through.

### Filter configuration (forwarded)

These reach the inner monitor through this wrapper; before 2026-09-01 they did not.

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_addr_filter_enable` | Input | 1 | High: suppress packets for transactions outside the window. Low: inert, whatever `ADDR_FILTER_ENABLE` says |
| `cfg_addr_filter_low` | Input | ADDR_WIDTH | Window base, inclusive |
| `cfg_addr_filter_high` | Input | ADDR_WIDTH | Window limit, inclusive |
| `cfg_id_filter_enable` | Input | 1 | High: use the runtime window below instead of the `ID_MATCH_*` parameters |
| `cfg_id_match_base` | Input | ID_WIDTH | First ID to accept |
| `cfg_id_match_count` | Input | ID_WIDTH+1 | How many; `0` means ALL |

Neither filter un-filters entries already admitted to the transaction table,
which is what makes changing them at runtime safe.

---

## Functional Description

### Performance Monitoring

The clock-gated wrapper exposes the full perfmon interface of the base module and **forwards every port unchanged** to the inner `axi4_slave_rd_mon`. The measurement-window state machine, the four R-channel utilization buckets (productive / back-pressure / starvation / idle), and the beat/byte/burst throughput counters behave exactly as documented in the base module — see [Performance Monitoring in axi4_slave_rd_mon](./axi4_slave_rd_mon.md#performance-monitoring) for the full narrative and per-bit semantics.

Forwarded perfmon ports (identical width and direction to the base module):

- **Inputs:** `cfg_perf_enable`, `cfg_start_event_sel` (3), `cfg_end_event_sel` (3), `cfg_start_trigger`, `cfg_end_trigger`, `cfg_window_force_close`
- **Outputs:** `window_active`, `window_cycles` (32), `perf_prod_cycles` (32), `perf_bp_cycles` (32), `perf_starv_cycles` (32), `perf_idle_cycles` (32), `perf_beat_count` (32), `perf_byte_count` (64), `perf_burst_count` (32)

The `perf_burst_count` output tracks AR (read address) handshakes. **WARNING -- gating vs window accounting:** an open measurement window is
NOT a wake term, and the entire inner monitor (window state machine and
counters included) runs on the gated clock. If the bus idles past
`cfg_cg_idle_count` with a window open, the counters FREEZE while
wall-clock time passes, and trigger pulses arriving while gated are
DROPPED. For exact wall-clock windows or idle-bus triggering, hold
`cfg_cg_enable` low around the measurement, or use the base module.

---

## Usage Example

```systemverilog
axi4_slave_rd_mon_cg #(
    // Base module parameters (see axi4_slave_rd_mon.md)
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    .CG_IDLE_COUNT_WIDTH(4)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    .cfg_cg_enable(1'b1),
    .cfg_cg_idle_count(4'd8),
    .cg_gating(), .cg_idle(),
    // ... all other ports same as axi4_slave_rd_mon (except debug_block_ready)
);
```

---

## Related Modules

- **Base Module Functionality:** [axi4_slave_rd_mon.md](./axi4_slave_rd_mon.md)
- **Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb4_slave_cg.md](../apb4/apb4_slave_cg.md) (APB interface)

---

## Navigation

- **[← Back to AXI4 Index](../_book_monitor_index.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
