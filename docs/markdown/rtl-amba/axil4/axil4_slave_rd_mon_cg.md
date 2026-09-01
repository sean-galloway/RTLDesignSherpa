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
**Location:** `rtl/amba/monitor/`
**Status:** ⚠️ Partial — see [Implementation Status](#implementation-status)

---

## Implementation Status

This wrapper gates the monitor's clock for real. It instantiates
`amba_clock_gate_ctrl`, and the base `axil4_slave_rd_mon` inside it is driven from
`gated_aclk`, not from `aclk`.

What it does:

1. **Gates the clock.** `amba_clock_gate_ctrl` counts `cfg_cg_idle_count`
   idle cycles and stops `gated_aclk`, reporting on `cg_gating` (the gated
   clock is stopped) and `cg_idle` (no activity observed).
2. **Holds off the interfaces while gated.** `s_axil_arready` and `fub_axil_rready` are forced
   low under `cg_gating`, so nothing is accepted into a stopped clock.
3. **Masks the monbus valid while gated** (`monbus_valid = w_monbus_valid &&
   !cg_gating`), which is what makes delivery exactly-once across a gating
   edge rather than a held valid replayed on wake.

Two earlier versions of this page were wrong in opposite directions, so both
are worth naming. One described a `cg_cycles_saved` output, a
`cfg_cg_idle_threshold` input and `ENABLE_CLOCK_GATING` / `CG_IDLE_CYCLES`
parameters; none of those exist anywhere in `rtl/amba`. The other -- the
correction to the first -- concluded that the wrapper therefore gates
nothing and "will not reduce dynamic power". That was the more damaging
error: it is false, and it steers an integrator away from the right part.
The real controls are `cfg_cg_enable` and `cfg_cg_idle_count` (width
`CG_IDLE_COUNT_WIDTH`); there is no cycles-saved counter of any kind.

Gating behaviour is asserted directly by `val/amba/test_mon_cg_gating.py`
(phase 5 for the ready hold-off, phase 6 for exactly-once monbus delivery).

---

## Overview

`axil4_slave_rd_mon_cg` wraps [axil4_slave_rd_mon](./axil4_slave_rd_mon.md) and adds a
power-management control and status interface. All monitoring, filtering,
address-range checking, and performance-monitoring behavior is that of the base
module; see [axil4_slave_rd_mon.md](./axil4_slave_rd_mon.md) for the complete
functional specification.

---

## Additional Parameters

In addition to all [axil4_slave_rd_mon](./axil4_slave_rd_mon.md) parameters
(including `USE_MONITOR` and `N_ADDR_RANGES`):

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `ACLK_MHZ` | int | 100 | Clock frequency in MHz. Builds the microsecond tick LUT in `counter_freq_invariant`. **Leave this at 100 on a 90 MHz part and every us-denominated timeout is wrong, silently** -- it was unreachable through this wrapper until 2026-09-01. |
| `CFI_MIN_FREQ_MHZ` | int | `ACLK_MHZ` | Lowest frequency the tick LUT must cover (dynamic-frequency builds). |
| `CFI_MAX_FREQ_MHZ` | int | `ACLK_MHZ` | Highest frequency the tick LUT must cover. |
| `USE_WDATA_ORDER_Q` | bit | 0 | Write-data ordering queue. Required (=1) whenever `NUM_BANKS` > 1. |
| `NUM_BANKS` | int | 1 | Transaction-table banking. The `USE_WDATA_ORDER_Q` pairing rule applies to WRITE monitors only -- `axi_monitor_trans_mgr` guards on `(NUM_BANKS > 1) && !IS_READ && !USE_WDATA_ORDER_Q`, so a read monitor may bank freely. |
| `ADDR_FILTER_ENABLE` | bit | 0 | Synthesises the address-range report filter. **The parameter only decides whether the logic EXISTS** -- a build that sets it and leaves `cfg_addr_filter_enable` low filters nothing and looks broken. |
| `CG_IDLE_COUNT_WIDTH` | int | 4 | Width of `cfg_cg_idle_count`; sets the longest programmable idle threshold |

There are no `CG_GATE_MONITOR`, `CG_GATE_REPORTER`, or `CG_GATE_TIMERS`
parameters, and no independent gating domains. Earlier revisions of this
document described such a scheme; it was never implemented.

---

### Derived Parameters (do not override)

These are declared as `parameter` so the elaborator can compute them, not so callers can set them. Each defaults to an expression over the parameters above; overriding one desynchronises it from its source and the design fails to elaborate or silently mis-sizes a bus. Set the parameters they are derived FROM and leave these alone.

| Derived parameter | Default expression |
|---|---|
| `AW` | `AXIL_ADDR_WIDTH` |
| `DW` | `AXIL_DATA_WIDTH` |

## Additional Ports


### Filter configuration (forwarded)

These reach the inner monitor through this wrapper; before 2026-09-01 they did not.

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_addr_filter_enable` | Input | 1 | High: suppress packets for transactions outside the window. Low: inert, whatever `ADDR_FILTER_ENABLE` says |
| `cfg_addr_filter_low` | Input | ADDR_WIDTH | Window base, inclusive |
| `cfg_addr_filter_high` | Input | ADDR_WIDTH | Window limit, inclusive |

There is no runtime ID filter on AXI4-Lite: the protocol has no IDs to match.

All base-module ports are forwarded unchanged, including the `cam_clear`
control input (Input, 1) - synchronous clear of the monitor transaction CAM
(driven from the harness clear control bit, e.g. CTRL[4]). The wrapper adds:

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_cg_enable` | Input | 1 | Gates the monitor functionally (ANDed into `cfg_monitor_enable`). 0 = monitor disabled. |

The base module's `busy` output remains available on this wrapper.

---

## Performance Monitoring

The wrapper forwards the base module's full performance-monitoring interface to
`axi_monitor_base` **unchanged** — the power-management interface neither adds,
removes, nor retimes any perfmon port. They behave exactly as documented for
[axil4_slave_rd_mon](./axil4_slave_rd_mon.md#performance-monitoring):

- **Config inputs:** `cfg_perf_enable`, `cfg_start_event_sel`, `cfg_end_event_sel`, `cfg_start_trigger`, `cfg_end_trigger`, `cfg_window_force_close`
- **Status / counters:** `window_active`, `window_cycles`, `perf_prod_cycles`, `perf_bp_cycles`, `perf_starv_cycles`, `perf_idle_cycles`, `perf_beat_count`, `perf_byte_count`, `perf_burst_count`

The completion/threshold/debug enables (`cfg_compl_enable`, `cfg_threshold_enable`, `cfg_debug_enable`) and the synthesis-cone parameters (`ENABLE_ERROR_LOGIC`, `ENABLE_TIMEOUT_LOGIC`, `ENABLE_COMPL_LOGIC`, `ENABLE_THRESHOLD_LOGIC`, `ENABLE_PERF_LOGIC`, `ENABLE_DEBUG_LOGIC`) are likewise forwarded unchanged. The utilization buckets watch the **R** (read-data) channel; for AXI4-Lite each transaction is a single data beat, so `perf_burst_count` counts AR handshakes = transactions.

> Note that `cfg_cg_enable = 0` disables the monitor, and therefore stops the
> performance counters as well.

---

## Usage Example

```systemverilog
axil4_slave_rd_mon_cg #(
    // Base module parameters (see axil4_slave_rd_mon.md)
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4),

    // Monitor parameters
    .UNIT_ID(8'h01),
    .AGENT_ID(16'h000A),
    .MAX_TRANSACTIONS(8)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),

    // Power-management interface
    .cfg_cg_enable(1'b1),            // 0 would disable the monitor
    .cfg_cg_idle_count(4'd4),        // idle cycles before the clock stops
    .cg_gating(cg_gating),           // high while the gated clock is stopped
    .cg_idle(cg_idle),

    // ... all other ports same as axil4_slave_rd_mon
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

- **[axil4_slave_rd_mon](./axil4_slave_rd_mon.md)** - Base module (functional specification)
- **[axil4_slave_wr_mon_cg](./axil4_slave_wr_mon_cg.md)** - Companion monitor wrapper
- **[axi_monitor_base](../monitor/axi_monitor_base.md)** - Core monitoring infrastructure
- **[axi_monitor_filtered](../monitor/axi_monitor_filtered.md)** - Filtering capabilities
- **[AXIL4 Clock-Gated Variants Guide](../axil4/axil4_clock_gating_guide.md)** - The transport-level `_cg` modules, which do perform real clock gating

---

**Last Updated:** 2026-07-19

---

## Navigation

- **[← Back to Base Module](./axil4_slave_rd_mon.md)**
- **[← Back to AXIL4 Index](../axil4/README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
