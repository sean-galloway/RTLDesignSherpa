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
**Location:** `rtl/amba/axi4/`
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
- ✅ **Power Savings:** 25-70% depending on traffic utilization
- ✅ **Configurable:** Idle threshold, gating domains, enable/disable
- ✅ **Zero Overhead When Disabled:** `ENABLE_CLOCK_GATING=0` → identical to base

---

## Common Parameters

In addition to all [axi4_master_wr_mon](./axi4_master_wr_mon.md) parameters (including `USE_MONITOR`):

| Parameter | Default | Description |
|-----------|---------|-------------|
| `ENABLE_CLOCK_GATING` | 1 | Master enable (0=disable, identical to base) |
| `CG_IDLE_CYCLES` | 8 | Cycles before clock gating activates |
| `CG_GATE_*` | 1 | Domain-specific gating enables |
| `USE_MONITOR` | 1 | Synthesis-time monitor enable (forwarded to inner monitor). |
| `N_ADDR_RANGES` | 0 | Number of address-range comparators (forwarded to base module). |

All base-module ports are forwarded unchanged, including the `cam_clear` control input (Input, 1) - synchronous clear of the monitor transaction CAM (driven from the harness clear control bit, e.g. CTRL[4]) - and the full performance-monitoring interface (see [Performance Monitoring](#performance-monitoring) below). The six `ENABLE_*_LOGIC` synthesis-cone parameters and the `cfg_compl_enable` / `cfg_threshold_enable` / `cfg_debug_enable` control enables are also passed straight through.

---

## Performance Monitoring

The clock-gated wrapper exposes the full perfmon interface of the base module and **forwards every port unchanged** to the inner `axi4_master_wr_mon`. The measurement-window state machine, the four W-channel utilization buckets (productive / back-pressure / starvation / idle), and the beat/byte/burst throughput counters behave exactly as documented in the base module — see [Performance Monitoring in axi4_master_wr_mon](./axi4_master_wr_mon.md#performance-monitoring) for the full narrative and per-bit semantics.

Forwarded perfmon ports (identical width and direction to the base module):

- **Inputs:** `cfg_perf_enable`, `cfg_start_event_sel` (3), `cfg_end_event_sel` (3), `cfg_start_trigger`, `cfg_end_trigger`, `cfg_window_force_close`
- **Outputs:** `window_active`, `window_cycles` (32), `perf_prod_cycles` (32), `perf_bp_cycles` (32), `perf_starv_cycles` (32), `perf_idle_cycles` (32), `perf_beat_count` (32), `perf_byte_count` (64), `perf_burst_count` (32)

Clock gating never suppresses these paths: while a measurement window is open the monitor stays awake, so window cycle accounting remains exact regardless of `CG_IDLE_CYCLES`.

---

## Quick Usage

```systemverilog
axi4_master_wr_mon_cg #(
    // Base module parameters (see axi4_master_wr_mon.md)
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    // Clock gating (see CG guide for details)
    .ENABLE_CLOCK_GATING(1),
    .CG_IDLE_CYCLES(8)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    // ... all other ports same as axi4_master_wr_mon
);
```

---

## Documentation

- **Base Module Functionality:** [axi4_master_wr_mon.md](./axi4_master_wr_mon.md)
- **Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb_slave_cg.md](../apb/apb_slave_cg.md) (APB interface)

---

## Navigation

- **[← Back to AXI4 Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
