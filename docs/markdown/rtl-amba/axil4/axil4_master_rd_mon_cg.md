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

# AXIL4 Master Read Monitor (Clock-Gated)

**Module:** `axil4_master_rd_mon_cg.sv`
**Base Module:** [axil4_master_rd_mon](./axil4_master_rd_mon.md)
**Location:** `rtl/amba/axil4/`
**Status:** Partial — see [Implementation Status](#implementation-status)

---

## Overview

`axil4_master_rd_mon_cg` wraps [axil4_master_rd_mon](./axil4_master_rd_mon.md) and adds a
power-management control and status interface. All monitoring, filtering,
address-range checking, and performance-monitoring behavior is that of the base
module; see [axil4_master_rd_mon.md](./axil4_master_rd_mon.md) for the complete
functional specification.

### Implementation Status

This wrapper gates the monitor's clock for real. It instantiates
`amba_clock_gate_ctrl`, and the base `axil4_master_rd_mon` inside it is driven from
`gated_aclk`, not from `aclk`.

What it does:

1. **Gates the clock.** `amba_clock_gate_ctrl` counts `cfg_cg_idle_count`
   idle cycles and stops `gated_aclk`, reporting on `cg_gating` (the gated
   clock is stopped) and `cg_idle` (no activity observed).
2. **Holds off the interfaces while gated.** `fub_axil_arready` and `m_axil_rready` are forced
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

## Parameters

In addition to all [axil4_master_rd_mon](./axil4_master_rd_mon.md) parameters
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
| `ADD_PIPELINE_STAGE` | bit | `0` | Insert a register stage for timing closure. Costs a cycle of latency. (Add register stage for timing closure) |
| `ENABLE_FILTERING` | bit | `1` | Enable packet filtering: two active drop levels (packet type, then event code). Level 2 is reserved and routes nothing. |

There are no `CG_GATE_MONITOR`, `CG_GATE_REPORTER`, or `CG_GATE_TIMERS`
parameters, and no independent gating domains. Earlier revisions of this
document described such a scheme; it was never implemented.

### Derived Parameters (do not override)

These are declared as `parameter` so the elaborator can compute them, not so callers can set them. Each defaults to an expression over the parameters above; overriding one desynchronises it from its source and the design fails to elaborate or silently mis-sizes a bus. Set the parameters they are derived FROM and leave these alone.

| Derived parameter | Default expression |
|---|---|
| `AW` | `AXIL_ADDR_WIDTH` |
| `DW` | `AXIL_DATA_WIDTH` |

---

## Ports

### Filter configuration (forwarded)

These reach the inner monitor through this wrapper; before 2026-09-01 they did not.

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_addr_filter_enable` | Input | 1 | High: suppress packets for transactions outside the window. Low: inert, whatever `ADDR_FILTER_ENABLE` says |
| `cfg_addr_filter_low` | Input | ADDR_WIDTH | Window base, inclusive |
| `cfg_addr_filter_high` | Input | ADDR_WIDTH | Window limit, inclusive |

There is no runtime ID filter on AXI4-Lite: the protocol has no IDs to match.

Base-module ports are forwarded unchanged EXCEPT `debug_block_ready`, which
this wrapper does not bring out (use the base module when you need that tap).
That includes the `cam_clear` control input (Input, 1) - synchronous clear of
the monitor transaction CAM, driven from the harness clear control bit, e.g.
CTRL[4]. The wrapper adds four ports:

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_cg_enable` | Input | 1 | Arms clock gating. It reaches `amba_clock_gate_ctrl` only -- `cfg_monitor_enable` is forwarded to the inner monitor untouched, so 0 here does NOT disable the monitor, it just leaves the clock free-running. |
| `cfg_cg_idle_count` | Input | `CG_IDLE_COUNT_WIDTH` | Idle cycles before the clock gates. The clock stops `cfg_cg_idle_count` + 2 cycles after the last bus activity (one extra for the `r_wakeup` flop). |
| `cg_gating` | Output | 1 | High while the clock is gated. |
| `cg_idle` | Output | 1 | High while the activity terms are quiet. |

The base module's `busy` output remains available on this wrapper.

---

## Functional Description

### Performance Monitoring

The wrapper forwards the base module's full performance-monitoring interface to
`axi_monitor_base` **unchanged** — the power-management interface neither adds,
removes, nor retimes any perfmon port. They behave exactly as documented for
[axil4_master_rd_mon](./axil4_master_rd_mon.md#performance-monitoring):

- **Config inputs:** `cfg_perf_enable`, `cfg_start_event_sel`, `cfg_end_event_sel`, `cfg_start_trigger`, `cfg_end_trigger`, `cfg_window_force_close`
- **Status / counters:** `window_active`, `window_cycles`, `perf_prod_cycles`, `perf_bp_cycles`, `perf_starv_cycles`, `perf_idle_cycles`, `perf_beat_count`, `perf_byte_count`, `perf_burst_count`

The completion/threshold/debug enables (`cfg_compl_enable`, `cfg_threshold_enable`, `cfg_debug_enable`) and the synthesis-cone parameters (`ENABLE_ERROR_LOGIC`, `ENABLE_TIMEOUT_LOGIC`, `ENABLE_COMPL_LOGIC`, `ENABLE_THRESHOLD_LOGIC`, `ENABLE_PERF_LOGIC`, `ENABLE_DEBUG_LOGIC`) are likewise forwarded unchanged. The utilization buckets watch the **R** (read-data) channel; for AXI4-Lite each transaction is a single data beat, so `perf_burst_count` counts AR handshakes = transactions.

> Note that `cfg_cg_enable = 0` does NOT disable the monitor. It only
> disarms clock gating, leaving the inner monitor on a free-running clock
> and behaving exactly like the base module. Use `cfg_monitor_enable = 0`
> to actually stop monitoring.

---

## Usage Examples
```systemverilog
axil4_master_rd_mon_cg #(
    // Base module parameters (see axil4_master_rd_mon.md)
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
    .cfg_cg_enable(1'b1),            // arm gating; 0 = clock free-runs
    .cfg_cg_idle_count(4'd4),        // idle cycles before the clock stops
    .cg_gating(cg_gating),           // high while the gated clock is stopped
    .cg_idle(cg_idle),

    // ... all other ports same as axil4_master_rd_mon
);
```

---

## Design Notes

**Monitor cost is not incremental.** The transaction table is
`bus_transaction_t` x `MAX_TRANSACTIONS`, and the reporter keeps a second full
copy (`r_trans_table_local`), so a monitored interface is a multiple of the
unmonitored one rather than a few percent on top. `MAX_TRANSACTIONS` is the
knob and the cost is linear in it.

**`perf_byte_count` scales with the bus width.** `cmd_size` is derived as
`$clog2(AXIL_DATA_WIDTH/8)`. It was hardwired to `3'b010` (4 bytes) until
2026-09-02, which halved every byte count on a 64-bit Lite bus without failing
anything. `val/amba/test_axil_perf_byte_count.py` pins it at both legal widths.

**Do not enable completion and performance packets together under load.** The
monitor bus sustains at most one packet per two cycles. Use `cfg_axi_pkt_mask`
to drop a class while keeping its marking and counting.

**The ID filter is inert and must stay that way.** AXI4-Lite has no IDs, so
this wrapper ties the monitor's ID inputs to zero; enabling `ID_FILTER_ENABLE`
with an `ID_MATCH_BASE` above 0 makes `id_owned(0)` false for every
transaction and drops ALL monitoring rather than narrowing it.

---

## Testing

A clock IS gated here -- that is the wrapper's entire purpose.
`amba_clock_gate_ctrl` drives the inner monitor's clock, and it stops when the
activity terms go quiet for `cfg_cg_idle_count` cycles.

`cfg_cg_enable` arms that gating. It is NOT a monitor kill-switch: with it low
the clock simply free-runs and the monitor behaves exactly like the base
module, packets included. Drive it low for any test that wants the base
module's timing without gating effects; drive it high to exercise the gating
itself, and expect the counters and any trigger pulse to be lost while the
clock is stopped (see the warning under Performance Monitoring).

---

## Timing Characteristics

### Buffer Depths and Latency

| Parameter | Default | Channel |
|-----------|---------|---------|
| `SKID_DEPTH_AR` | 2 entries | Skid depth on the AR channel |
| `SKID_DEPTH_R` | 4 entries | Skid depth on the R channel |

Each channel traverses one `gaxi_skid_buffer`. That module registers both
`rd_valid` and the storage array, so the **1-cycle input-to-output latency
applies on every transfer, including the unstalled case** -- there is no
combinational bypass from the upstream payload to the downstream one. Full
throughput (one transfer per cycle) is still sustained once the pipeline is
primed; the depth sets how much backpressure can be absorbed before it
propagates upstream, not the steady-state rate.

Legal depth range is 2..8 inclusive, odd values included.

---

## Related Modules

- **[axil4_master_rd_mon](./axil4_master_rd_mon.md)** - Base module (functional specification)
- **[axil4_master_wr_mon_cg](./axil4_master_wr_mon_cg.md)** - Companion monitor wrapper
- **[axi_monitor_base](../monitor/axi_monitor_base.md)** - Core monitoring infrastructure
- **[axi_monitor_filtered](../monitor/axi_monitor_filtered.md)** - Filtering capabilities
- **[AXIL4 Clock-Gated Variants Guide](../axil4/axil4_clock_gating_guide.md)** - The transport-level `_cg` modules, which do perform real clock gating

---

**Last Updated:** 2026-07-19

---

## Navigation

- **[← Back to Base Module](./axil4_master_rd_mon.md)**
- **[← Back to AXIL4 Index](../axil4/README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
