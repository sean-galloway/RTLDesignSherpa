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

# AXIL4 Slave Read Monitor (Clock-Gated)

**Module:** `axil4_slave_rd_mon_cg.sv`
**Base Module:** [axil4_slave_rd_mon](./axil4_slave_rd_mon.md)
**Location:** `rtl/amba/axil4/`
**Status:** ✅ Production Ready

---

## Quick Reference

This is the **clock-gated variant** of [axil4_slave_rd_mon](./axil4_slave_rd_mon.md).

**For complete clock-gating documentation, usage examples, and configuration guidelines, see:**

**→ [Clock-Gated Variants Guide](../shared/clock_gated_variants.md)**

---

## Summary

The `axil4_slave_rd_mon_cg` module adds power optimization to `axil4_slave_rd_mon` through activity-based clock gating:

- ✅ **Same Functionality:** 100% equivalent to base module
- ✅ **Power Savings:** 25-70% depending on traffic utilization
- ✅ **Configurable:** Idle threshold, gating domains, enable/disable
- ✅ **Zero Overhead When Disabled:** `ENABLE_CLOCK_GATING=0` → identical to base

---

## Common Parameters

In addition to all [axil4_slave_rd_mon](./axil4_slave_rd_mon.md) parameters (including `USE_MONITOR` and `N_ADDR_RANGES`):

| Parameter | Default | Description |
|-----------|---------|-------------|
| `ENABLE_CLOCK_GATING` | 1 | Master enable (0=disable, identical to base) |
| `CG_IDLE_CYCLES` | 8 | Cycles before clock gating activates |
| `CG_GATE_*` | 1 | Domain-specific gating enables |
| `USE_MONITOR` | 1 | Synthesis-time monitor enable (forwarded to inner monitor). |

All base-module ports are forwarded unchanged, including the `cam_clear` control input (Input, 1) - synchronous clear of the monitor transaction CAM (driven from the harness clear control bit, e.g. CTRL[4]).

---

## Performance Monitoring

The clock-gated wrapper forwards the base module's full performance-monitoring interface to `axi_monitor_base` **unchanged** — clock gating neither adds, removes, nor retimes any perfmon port. They behave exactly as documented for [axil4_slave_rd_mon](./axil4_slave_rd_mon.md#performance-monitoring):

- **Config inputs:** `cfg_perf_enable`, `cfg_start_event_sel`, `cfg_end_event_sel`, `cfg_start_trigger`, `cfg_end_trigger`, `cfg_window_force_close`
- **Status / counters:** `window_active`, `window_cycles`, `perf_prod_cycles`, `perf_bp_cycles`, `perf_starv_cycles`, `perf_idle_cycles`, `perf_beat_count`, `perf_byte_count`, `perf_burst_count`

The completion/threshold/debug enables (`cfg_compl_enable`, `cfg_threshold_enable`, `cfg_debug_enable`) and the synthesis-cone parameters (`ENABLE_ERROR_LOGIC`, `ENABLE_TIMEOUT_LOGIC`, `ENABLE_COMPL_LOGIC`, `ENABLE_THRESHOLD_LOGIC`, `ENABLE_PERF_LOGIC`, `ENABLE_DEBUG_LOGIC`) are likewise forwarded unchanged. The utilization buckets watch the **R** (read-data) channel; for AXI4-Lite each transaction is a single data beat, so `perf_burst_count` counts AR handshakes = transactions.

---

## Quick Usage

```systemverilog
axil4_slave_rd_mon_cg #(
    // Base module parameters (see axil4_slave_rd_mon.md)
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    // Clock gating (see CG guide for details)
    .ENABLE_CLOCK_GATING(1),
    .CG_IDLE_CYCLES(8)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    // ... all other ports same as axil4_slave_rd_mon
);
```

---

## Documentation

- **Base Module Functionality:** [axil4_slave_rd_mon.md](./axil4_slave_rd_mon.md)
- **Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb_slave_cg.md](../apb/apb_slave_cg.md) (APB interface)

---

## Navigation

- **[← Back to AXIL4 Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
