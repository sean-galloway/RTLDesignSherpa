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

# axi4_master_rd_mon_cg

**Module:** `axi4_master_rd_mon_cg.sv`
**Base Module:** [axi4_master_rd_mon](./axi4_master_rd_mon.md)
**Location:** `rtl/amba/axi4/` (protocol monitors live with their protocol; only the monitor CORE pieces are in `rtl/amba/monitor/`)
**Status:** Production Ready

---

## Overview

The `axi4_master_rd_mon_cg` module is a clock-gated variant of [axi4_master_rd_mon](./axi4_master_rd_mon.md) that adds comprehensive power optimization capabilities through activity-based clock gating.

### Key Differences from Base Module

- **Activity-Based Clock Gating:** one gate for the whole module, woken by bus valids, core busy, and a pending monitor packet
- **Runtime Control:** `cfg_cg_enable` / `cfg_cg_idle_count` (no per-domain policies)
- **Gating Status:** `cg_gating` / `cg_idle` outputs (no built-in power statistics)
- **Functional differences from base:** ten base parameters not forwarded, `debug_block_ready` tied off, and gated-clock caveats for windows/triggers (see the WARNING below) -- use the base module when those matter

All other functionality is identical to the base module. See [axi4_master_rd_mon.md](./axi4_master_rd_mon.md) for complete functional specification.

### When to Use the Clock-Gated Variant

**Use `axi4_master_rd_mon_cg` when:**
- Power consumption is a critical concern
- Design has periods of inactivity (burst traffic patterns)
- FPGA/ASIC has integrated clock gating support
- Meeting power budgets for battery-operated systems

**Use base module (`axi4_master_rd_mon`) when:**
- Maximum performance with no power constraints
- Continuous high-activity traffic
- Simpler design with fewer configuration parameters
- Minimizing gate count is priority

---

## Parameters

### Clock Gating Parameters

In addition to all parameters from [axi4_master_rd_mon](./axi4_master_rd_mon.md), this module adds:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | int | 4 | Width of the idle countdown, sizing `cfg_cg_idle_count` |

The gating controls are RUNTIME INPUTS: `cfg_cg_enable` and
`cfg_cg_idle_count`; status outputs are `cg_gating` / `cg_idle`. ONE
`amba_clock_gate_ctrl` gates the entire inner monitor module -- there are
no per-domain gates and no `cg_*_gated` status signals. (The
ENABLE_CLOCK_GATING / CG_IDLE_CYCLES / CG_GATE_* interface this page once
documented never existed.)

### Base Module Parameters

MOST base-module parameters pass through, with these NOT forwarded:
`ADDR_RANGE_IS_ERROR` (error-flavored address ranges are unreachable
through this wrapper), `ACTIVE_TRANS_THRESHOLD`, `ACLK_MHZ`,
`CFI_MIN_FREQ_MHZ`, `CFI_MAX_FREQ_MHZ`, `USE_WDATA_ORDER_Q`, `NUM_BANKS`,
`ID_FILTER_ENABLE`, `ID_MATCH_BASE`, `ID_MATCH_COUNT`. Among the
forwarded ones:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `USE_MONITOR` | bit | 1 | Synthesis-time monitor enable. 0 = omit monitor and tie outputs to safe non-blocking defaults; 1 = full monitor functionality. |
| `N_ADDR_RANGES` | int | 0 | Number of address-range comparators (forwarded to base module). |

Base-module ports are forwarded EXCEPT `debug_block_ready`, which the wrapper ties off (use the base module when you need the backpressure tap). `cam_clear` is forwarded (Input, 1) - synchronous clear of the monitor transaction CAM (driven from the harness clear control bit, e.g. CTRL[4]) - and the full performance-monitoring interface (see [Performance Monitoring](#performance-monitoring) below). The six `ENABLE_*_LOGIC` synthesis-cone parameters and the `cfg_compl_enable` / `cfg_threshold_enable` / `cfg_debug_enable` control enables are also passed straight through.

### Parameter Relationships

- **`cfg_cg_enable = 0`**: bypasses the gate at runtime; behavior is identical to base
- **`cfg_cg_idle_count`**: higher values keep the clock running longer after traffic stops, so the block is gated less often. It does not change wake-up latency, which is fixed at 1 register stage / 2 clocks to the first usable edge.

---

## Functional Description

### Clock Gating Architecture

ONE `amba_clock_gate_ctrl` gates the whole inner monitor module. The wake
term is bus activity plus pending monitor-bus work (`fub_axi_arvalid ||
fub_axi_rvalid || int_busy || w_monbus_valid` on the user side,
`m_axi_arvalid || m_axi_rvalid` on the AXI side); when both sides idle for
`cfg_cg_idle_count` cycles with nothing pending on the monitor bus,
everything inside -- transaction tracking, reporter, timers, perf counters
-- stops together. There are no per-domain gates. The external
`monbus_valid` is masked with `!cg_gating`, so monitor-bus delivery is
exactly-once across gating (`val/amba/test_mon_cg_gating.py` phase 6): a
packet pending delivery holds the block awake, and a packet emitted in the
few-cycle reporter latency after the last transaction (possible only when
`cfg_cg_idle_count` is smaller than that latency) parks in the reporter
FIFO and delivers exactly once at the next wake.

### Gating State Machine

```
ACTIVE ───────► IDLE_COUNT ───────► GATED
  ▲                                    │
  │                                    │
  └────────────────────────────────────┘
        (Activity Detected)

States:
- ACTIVE: Clocks enabled, monitoring activity
- IDLE_COUNT: Counting cfg_cg_idle_count before gating
- GATED: Clocks disabled, waiting for activity
```

### Performance Monitoring

The clock-gated wrapper exposes the full perfmon interface of the base module and **forwards every port unchanged** to the inner `axi4_master_rd_mon`. The measurement-window state machine, the four R-channel utilization buckets (productive / back-pressure / starvation / idle), and the beat/byte/burst throughput counters behave exactly as documented in the base module — see [Performance Monitoring in axi4_master_rd_mon](./axi4_master_rd_mon.md#performance-monitoring) for the full narrative and per-bit semantics.

Forwarded perfmon ports (identical width and direction to the base module):

- **Inputs:** `cfg_perf_enable`, `cfg_start_event_sel` (3), `cfg_end_event_sel` (3), `cfg_start_trigger`, `cfg_end_trigger`, `cfg_window_force_close`
- **Outputs:** `window_active`, `window_cycles` (32), `perf_prod_cycles` (32), `perf_bp_cycles` (32), `perf_starv_cycles` (32), `perf_idle_cycles` (32), `perf_beat_count` (32), `perf_byte_count` (64), `perf_burst_count` (32)

**WARNING -- gating vs window accounting:** an open measurement window is
NOT an activity term (`user_valid` is bus valids, busy, and pending
monitor-bus work only), and the
entire inner monitor -- window state machine and counters included -- runs
on the gated clock. If the bus idles past the countdown while a window is
open, the clock gates and `window_cycles` / perf counters FREEZE while
wall-clock time passes: the host reads an under-counted window. The same
applies to configuration and trigger pulses (`cam_clear`,
`cfg_start_trigger`, `cfg_end_trigger`, `cfg_window_force_close`): they
are sampled in the gated domain and a pulse arriving while gated is
DROPPED. For exact wall-clock windows or reliable idle-bus triggering,
hold `cfg_cg_enable` low around the measurement, or use the base module.

---

## Timing

### Wake-Up and Gating Latency

Wake-up latency does not depend on `cfg_cg_idle_count`. Activity is registered once
(AXI4, AXI5, AXI4-Lite, AXI4-Stream) or twice (APB, APB5, AXI5-Stream) before
reaching the ICG enable, which is combinational. This monitor wrapper drives the
activity terms combinationally, so it has **1 register stage** and the first
usable gated-clock edge arrives **2 clock cycles** after activity asserts.

`cfg_cg_idle_count` sets the going-to-sleep delay only: gating engages
`cfg_cg_idle_count + 1` clocks after the internal wakeup deasserts, which is
`cfg_cg_idle_count + 2` clocks after the last bus activity.

| Configuration | Clocks from last activity to gating | Use Case |
|---------------|-------------------------------------|----------|
| `cfg_cg_idle_count=4` | 6 clock cycles | Low-latency, frequent bursts |
| `cfg_cg_idle_count=8` | 10 clock cycles | Balanced |
| `cfg_cg_idle_count=15` | 17 clock cycles | Maximum power savings, infrequent traffic |

---

## Usage Example

### Example 1: Maximum Power Savings (Burst Traffic)

```systemverilog
axi4_master_rd_mon_cg #(
    // Base parameters (see axi4_master_rd_mon.md)
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    .CG_IDLE_COUNT_WIDTH(4)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    // Clock gating -- aggressive: gate quickly after 4 idle cycles
    .cfg_cg_enable(1'b1),
    .cfg_cg_idle_count(4'd4),
    .cg_gating(), .cg_idle(),
    // ... connect signals same as base module
);
```

### Example 2: Balanced Performance and Power

```systemverilog
axi4_master_rd_mon_cg #(
    // Base parameters
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    .CG_IDLE_COUNT_WIDTH(4)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    // Clock gating -- balanced: wait longer before gating (gated less often)
    .cfg_cg_enable(1'b1),
    .cfg_cg_idle_count(4'd15),
    .cg_gating(), .cg_idle(),
    // ... connect signals same as base module
);
```

### Example 3: Clock Gating Disabled (Functional Verification)

```systemverilog
axi4_master_rd_mon_cg #(
    // Base parameters
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    .CG_IDLE_COUNT_WIDTH(4)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    // Clock gating -- DISABLED for verification (runtime bypass)
    .cfg_cg_enable(1'b0),
    .cfg_cg_idle_count(4'd0),
    .cg_gating(), .cg_idle(),
    // ... connect signals same as base module
);
```

**Note:** With `cfg_cg_enable=0`, this module is functionally identical to the base module.

---

## Design Notes

### Power Savings Analysis

Based on representative workloads:

| Traffic Pattern | Clock Gating Enabled | Power Savings |
|----------------|---------------------|---------------|
| 10% Utilization | Aggressive (`cfg_cg_idle_count=4`) | 60-70% |
| 25% Utilization | Balanced (`cfg_cg_idle_count=8`) | 45-55% |
| 50% Utilization | Conservative (`cfg_cg_idle_count=15`) | 25-35% |
| 90% Utilization | Any configuration | 5-10% |

**Note:** Actual savings depend on FPGA/ASIC technology, tool implementation, and traffic patterns.

### Power Monitoring Signals

The module provides these status signals for power analysis:

| Signal | Width | Description |
|--------|-------|-------------|
| `cg_gating` | 1 | The (single) gated clock is currently stopped |
| `cg_idle` | 1 | No activity this cycle (`~r_wakeup` -- asserts one cycle after the interfaces go quiet; it does NOT wait for the countdown) |

### Verification Considerations

**Recommendation:** Disable clock gating during functional verification:

```systemverilog
// Testbench instantiation
axi4_master_rd_mon_cg dut (
    .cfg_cg_enable(1'b0),   // runtime bypass for faster simulation
    // ... connections
);
```

**Rationale:**
- Simpler waveforms (no clock gating events)
- Faster simulation (no gating overhead)
- Easier debug (no timing dependencies)

For power-specific verification:

1. **Enable clock gating** with realistic parameters
2. **Monitor gating signals** (`cg_gating` / `cg_idle`) to verify expected behavior
3. **Vary traffic patterns** to test gating effectiveness
4. **Check wake-up timing** meets system requirements

### Synthesis Considerations

**FPGA Implementations**

**Xilinx:**
- Drive `cfg_cg_enable=1` and let synthesis map the ICG to `BUFGCE` primitives
- Tool will infer clock enables automatically
- Verify with post-synthesis power analysis

**Intel (Altera):**
- Drive `cfg_cg_enable=1` and let synthesis map the ICG to `ALTCLKCTRL`
- May need vendor-specific clock gating primitives
- Check power reports for gating effectiveness

**Lattice:**
- Basic clock gating supported
- May require manual instantiation of clock enables
- Verify functionality in timing simulation

**ASIC Implementations:**
- Work with foundry to select appropriate clock gating cells
- Integrated Clock Gating (ICG) cells provide best results
- Consider hold-time implications of clock gating
- Verify power intent with UPF (Unified Power Format)

---

## Related Modules

- **[axi4_master_rd_mon](./axi4_master_rd_mon.md)** - Base module (non-clock-gated)
- **[axi_monitor_base](../monitor/axi_monitor_base.md)** - Core monitoring infrastructure
- **[axi_monitor_filtered](../monitor/axi_monitor_filtered.md)** - Filtering capabilities

### See Also

- **Power Optimization Guide:** `docs/POWER_OPTIMIZATION_GUIDE.md`
- **Clock Gating Best Practices:** `docs/CLOCK_GATING_GUIDE.md`
- **AMBA Subsystem Overview:** `docs/markdown/rtl-amba/overview.md`

---

## Navigation

- **[← Back to Base Module](./axi4_master_rd_mon.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
