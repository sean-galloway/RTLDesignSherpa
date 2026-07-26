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

# AXIL4 Slave Write Monitor (Clock-Gated)

**Module:** `axil4_slave_wr_mon_cg.sv`
**Base Module:** [axil4_slave_wr_mon](./axil4_slave_wr_mon.md)
**Location:** `rtl/amba/monitor/`
**Status:** ⚠️ Partial — see [Implementation Status](#implementation-status)

---

## Implementation Status

**This wrapper does not currently gate any clock.** The RTL contains no
`amba_clock_gate_ctrl` instance, no ICG cell, and no gated clock net; the base
`axil4_slave_wr_mon` inside it runs on the ungated `aclk`. What the wrapper
actually does today is:

1. **Gate the monitor functionally**, by ANDing the gating enable into the
   monitor enable: `cfg_monitor_enable & cfg_cg_enable`. With
   `cfg_cg_enable = 0` the monitor stops observing.
2. **Count idle cycles** into `cg_cycles_saved`, incremented whenever
   `cfg_cg_enable && !busy`. The RTL labels this block
   "Clock Gating Statistics (Placeholder)". It is an *estimate of cycles
   during which gating would have been possible*, not a measurement of cycles
   actually saved.

The `ENABLE_CLOCK_GATING` and `CG_IDLE_CYCLES` parameters and the
`cfg_cg_idle_threshold` port are **declared but not referenced** anywhere in
the module body. Setting them has no effect.

**Consequence for integrators:** instantiating this wrapper instead of
`axil4_slave_wr_mon` will not reduce dynamic power. If you need real clock
gating on an AXI4-Lite transport path today, use the plain
[`_cg` transport modules](../axil4/axil4_clock_gating_guide.md)
(`axil4_master_rd_cg` and friends), which do instantiate
`amba_clock_gate_ctrl` and a real ICG cell.

---

## Overview

`axil4_slave_wr_mon_cg` wraps [axil4_slave_wr_mon](./axil4_slave_wr_mon.md) and adds a
power-management control and status interface. All monitoring, filtering,
address-range checking, and performance-monitoring behavior is that of the base
module; see [axil4_slave_wr_mon.md](./axil4_slave_wr_mon.md) for the complete
functional specification.

---

## Additional Parameters

In addition to all [axil4_slave_wr_mon](./axil4_slave_wr_mon.md) parameters
(including `USE_MONITOR` and `N_ADDR_RANGES`):

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `ENABLE_CLOCK_GATING` | bit | 1 | Declared but **unused** in the current RTL |
| `CG_IDLE_CYCLES` | int | 4 | Declared but **unused** in the current RTL |

There are no `CG_GATE_MONITOR`, `CG_GATE_REPORTER`, or `CG_GATE_TIMERS`
parameters, and no independent gating domains. Earlier revisions of this
document described such a scheme; it was never implemented.

---

## Additional Ports

All base-module ports are forwarded unchanged, including the `cam_clear`
control input (Input, 1) - synchronous clear of the monitor transaction CAM
(driven from the harness clear control bit, e.g. CTRL[4]). The wrapper adds:

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_cg_enable` | Input | 1 | Gates the monitor functionally (ANDed into `cfg_monitor_enable`). 0 = monitor disabled. |
| `cfg_cg_idle_threshold` | Input | 8 | Declared but **unused** in the current RTL |
| `cg_cycles_saved` | Output | 32 | Count of cycles where `cfg_cg_enable && !busy`; an estimate, not a measurement |

The base module's `busy` output remains available on this wrapper.

---

## Performance Monitoring

The wrapper forwards the base module's full performance-monitoring interface to
`axi_monitor_base` **unchanged** — the power-management interface neither adds,
removes, nor retimes any perfmon port. They behave exactly as documented for
[axil4_slave_wr_mon](./axil4_slave_wr_mon.md#performance-monitoring):

- **Config inputs:** `cfg_perf_enable`, `cfg_start_event_sel`, `cfg_end_event_sel`, `cfg_start_trigger`, `cfg_end_trigger`, `cfg_window_force_close`
- **Status / counters:** `window_active`, `window_cycles`, `perf_prod_cycles`, `perf_bp_cycles`, `perf_starv_cycles`, `perf_idle_cycles`, `perf_beat_count`, `perf_byte_count`, `perf_burst_count`

The completion/threshold/debug enables (`cfg_compl_enable`, `cfg_threshold_enable`, `cfg_debug_enable`) and the synthesis-cone parameters (`ENABLE_ERROR_LOGIC`, `ENABLE_TIMEOUT_LOGIC`, `ENABLE_COMPL_LOGIC`, `ENABLE_THRESHOLD_LOGIC`, `ENABLE_PERF_LOGIC`, `ENABLE_DEBUG_LOGIC`) are likewise forwarded unchanged. The utilization buckets watch the **W** (write-data) channel; for AXI4-Lite each transaction is a single data beat, so `perf_burst_count` counts AW handshakes = transactions.

> Note that `cfg_cg_enable = 0` disables the monitor, and therefore stops the
> performance counters as well.

---

## Usage Example

```systemverilog
axil4_slave_wr_mon_cg #(
    // Base module parameters (see axil4_slave_wr_mon.md)
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .SKID_DEPTH_AW(2),
    .SKID_DEPTH_W(2),
    .SKID_DEPTH_B(2),

    // Monitor parameters
    .UNIT_ID(8'h01),
    .AGENT_ID(16'h000A),
    .MAX_TRANSACTIONS(8)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),

    // Power-management interface
    .cfg_cg_enable(1'b1),            // 0 would disable the monitor
    .cfg_cg_idle_threshold(8'd4),    // currently unused by the RTL
    .cg_cycles_saved(idle_cycle_est),

    // ... all other ports same as axil4_slave_wr_mon
);
```

---

## Verification Considerations

Because no clock is actually gated, simulation of this wrapper behaves exactly
like the base module as long as `cfg_cg_enable = 1`. Drive `cfg_cg_enable = 1`
for any test that expects monitor packets — with it low the monitor is off and
no packets are emitted.

---

## Related Modules

- **[axil4_slave_wr_mon](./axil4_slave_wr_mon.md)** - Base module (functional specification)
- **[axil4_slave_rd_mon_cg](./axil4_slave_rd_mon_cg.md)** - Companion monitor wrapper
- **[axi_monitor_base](axi_monitor_base.md)** - Core monitoring infrastructure
- **[axi_monitor_filtered](axi_monitor_filtered.md)** - Filtering capabilities
- **[AXIL4 Clock-Gated Variants Guide](../axil4/axil4_clock_gating_guide.md)** - The transport-level `_cg` modules, which do perform real clock gating

---

**Last Updated:** 2026-07-19

---

## Navigation

- **[← Back to Base Module](./axil4_slave_wr_mon.md)**
- **[← Back to AXIL4 Index](../axil4/README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
