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

# AXI4 Master Write Monitor (Clock-Gated)

**Module:** `axi4_master_wr_mon_cg.sv`
**Base Module:** [axi4_master_wr_mon](./axi4_master_wr_mon.md)
**Location:** `rtl/amba/axi4/` (protocol monitors live with their protocol; only the monitor CORE pieces are in `rtl/amba/monitor/`)
**Status:** ✅ Production Ready

---

## Quick Reference

This is the **clock-gated variant** of [axi4_master_wr_mon](./axi4_master_wr_mon.md).

**For complete clock-gating documentation, usage examples, and configuration guidelines, see:**

**→ [Clock-Gated Variants Guide](../shared/clock_gated_variants.md)**

---

## Summary

The `axi4_master_wr_mon_cg` module adds power optimization to `axi4_master_wr_mon` through activity-based clock gating:

- ✅ **Same Functionality:** 100% equivalent to base module
- ✅ **Power Savings:** traffic-dependent; unmeasured in this repo -- treat any percentage as a placeholder until characterized
- ✅ **Configurable:** Idle threshold, gating domains, enable/disable
- ✅ **Zero Overhead When Disabled:** `cfg_cg_enable=0` bypasses the gate at runtime

---

## Common Parameters

MOST [axi4_master_wr_mon](./axi4_master_wr_mon.md) parameters pass through -- with these NOT
forwarded: `ACLK_MHZ`, `CFI_MIN_FREQ_MHZ`, `CFI_MAX_FREQ_MHZ`,
`ADDR_RANGE_IS_ERROR`, `ACTIVE_TRANS_THRESHOLD`, `USE_WDATA_ORDER_Q`,
`NUM_BANKS`, `ID_FILTER_ENABLE`, `ID_MATCH_BASE`, `ID_MATCH_COUNT` (use the
base module when you need those knobs; on this wrapper the inner defaults
apply and setting them fails elaboration).

| Parameter | Default | Description |
|-----------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | 4 | Width of the idle countdown, sizing `cfg_cg_idle_count` |
| `USE_MONITOR` | 1 | Synthesis-time monitor enable (forwarded to inner monitor). |
| `N_ADDR_RANGES` | 0 | Number of address-range comparators (forwarded to base module). |

Gating is controlled by RUNTIME inputs `cfg_cg_enable` /
`cfg_cg_idle_count` with status outputs `cg_gating` / `cg_idle`; ONE
`amba_clock_gate_ctrl` gates the entire inner module (no per-domain
gates). (The ENABLE_CLOCK_GATING / CG_IDLE_CYCLES / CG_GATE_* interface
this page once documented never existed.)

Base-module ports are forwarded EXCEPT `debug_block_ready`, which this wrapper ties off (use the base module for the backpressure tap). `cam_clear` is forwarded (Input, 1) - synchronous clear of the monitor transaction CAM (driven from the harness clear control bit, e.g. CTRL[4]) - and the full performance-monitoring interface (see [Performance Monitoring](#performance-monitoring) below). The six `ENABLE_*_LOGIC` synthesis-cone parameters and the `cfg_compl_enable` / `cfg_threshold_enable` / `cfg_debug_enable` control enables are also passed straight through.

---

## Performance Monitoring

The clock-gated wrapper exposes the full perfmon interface of the base module and **forwards every port unchanged** to the inner `axi4_master_wr_mon`. The measurement-window state machine, the four W-channel utilization buckets (productive / back-pressure / starvation / idle), and the beat/byte/burst throughput counters behave exactly as documented in the base module — see [Performance Monitoring in axi4_master_wr_mon](./axi4_master_wr_mon.md#performance-monitoring) for the full narrative and per-bit semantics.

Forwarded perfmon ports (identical width and direction to the base module):

- **Inputs:** `cfg_perf_enable`, `cfg_start_event_sel` (3), `cfg_end_event_sel` (3), `cfg_start_trigger`, `cfg_end_trigger`, `cfg_window_force_close`
- **Outputs:** `window_active`, `window_cycles` (32), `perf_prod_cycles` (32), `perf_bp_cycles` (32), `perf_starv_cycles` (32), `perf_idle_cycles` (32), `perf_beat_count` (32), `perf_byte_count` (64), `perf_burst_count` (32)

**WARNING -- gating vs window accounting:** an open measurement window is
NOT a wake term, and the entire inner monitor (window state machine and
counters included) runs on the gated clock. If the bus idles past
`cfg_cg_idle_count` with a window open, the counters FREEZE while
wall-clock time passes, and trigger pulses (`cfg_start_trigger`,
`cfg_end_trigger`, `cfg_window_force_close`, `cam_clear`) arriving while
gated are DROPPED. For exact wall-clock windows or idle-bus triggering,
hold `cfg_cg_enable` low around the measurement, or use the base module.

---

## Quick Usage

```systemverilog
axi4_master_wr_mon_cg #(
    // Base module parameters (see axi4_master_wr_mon.md)
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
    // ... all other ports same as axi4_master_wr_mon (except debug_block_ready)
);
```

---

## Documentation

- **Base Module Functionality:** [axi4_master_wr_mon.md](./axi4_master_wr_mon.md)
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
