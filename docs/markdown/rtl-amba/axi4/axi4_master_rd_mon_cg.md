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
- **Functional differences from base:** `ACTIVE_TRANS_THRESHOLD` not forwarded (harmless -- its inner default is derived from the forwarded `MAX_TRANSACTIONS`), `debug_block_ready` tied off, and gated-clock caveats for windows/triggers (see the WARNING below) -- use the base module when those matter

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
| `ADD_PIPELINE_STAGE` | bit | `0` | Insert a register stage for timing closure. Costs a cycle of latency. (Add register stage for timing closure) |
| `ENABLE_COMPL_LOGIC` | bit | `1'b1` | Synthesise the completion-packet cone. 0 removes the logic entirely. |
| `ENABLE_DEBUG_LOGIC` | bit | `1'b0` | Synthesise the debug-packet cone. 0 removes the logic entirely. |
| `ENABLE_ERROR_LOGIC` | bit | `1'b1` | Synthesise the error detection cone. 0 removes the logic entirely. |
| `ENABLE_FILTERING` | bit | `1` | Enable packet filtering: two active drop levels (packet type, then event code). Level 2 is reserved and routes nothing. |
| `ENABLE_PERF_LOGIC` | bit | `1'b1` | Synthesise the reporter's performance cone (`g_perf`). Does NOT gate the perfmon window state machine or its counters. |
| `ENABLE_THRESHOLD_LOGIC` | bit | `1'b1` | Synthesise the threshold-packet cone. 0 removes the logic entirely. |
| `ENABLE_TIMEOUT_LOGIC` | bit | `1'b1` | Synthesise the timeout detection cone. 0 removes the logic entirely. |
| `SKID_DEPTH_AR` | int | `2` | Skid-buffer depth on the AR channel. Legal range 2..8 inclusive; odd depths are legal. |
| `SKID_DEPTH_R` | int | `4` | Skid-buffer depth on the R channel. Legal range 2..8 inclusive; odd depths are legal. |
| `AGENT_ID` | logic | `16'h000A` | Agent identifier emitted in the `agent_id` field of every monitor packet. Pairs with `UNIT_ID` to identify the packet source. (16-bit Agent ID for monitor packets) |
| `UNIT_ID` | logic | `8'h01` | Unit identifier emitted in the `unit_id` field of every monitor packet. Give each monitored interface a distinct value or the packets cannot be told apart at the collector. (8-bit Unit ID for monitor packets) |

The gating controls are RUNTIME INPUTS: `cfg_cg_enable` and
`cfg_cg_idle_count`; status outputs are `cg_gating` / `cg_idle`. ONE
`amba_clock_gate_ctrl` gates the entire inner monitor module -- there are
no per-domain gates and no `cg_*_gated` status signals. (The
ENABLE_CLOCK_GATING / CG_IDLE_CYCLES / CG_GATE_* interface this page once
documented never existed.)

### Base Module Parameters

MOST base-module parameters pass through. As of 2026-09-01 only
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

Among the forwarded ones:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `USE_MONITOR` | bit | 1 | Synthesis-time monitor enable. 0 = omit monitor and tie outputs to safe non-blocking defaults; 1 = full monitor functionality. |
| `N_ADDR_RANGES` | int | 0 | Number of address-range comparators (forwarded to base module). |
| `ADDR_FILTER_ENABLE` | bit | 0 | Synthesises the address-range report filter. **The parameter only decides whether the logic EXISTS** -- a build that sets it and leaves `cfg_addr_filter_enable` low filters nothing and looks broken. |
| `ID_FILTER_ENABLE` | bit | 0 | Synthesises the ID report filter (see `cfg_id_*` for the runtime override). |
| `ID_MATCH_BASE` | int | 0 | First ID this instance owns. |
| `ID_MATCH_COUNT` | int | 0 | How many IDs; `0` means ALL, so a zeroed register block does not silently filter everything away. |

Base-module ports are forwarded EXCEPT `debug_block_ready`, which the wrapper ties off (use the base module when you need the backpressure tap). `cam_clear` is forwarded (Input, 1) - synchronous clear of the monitor transaction CAM (driven from the harness clear control bit, e.g. CTRL[4]) - and the full performance-monitoring interface (see [Performance Monitoring](#performance-monitoring) below). The six `ENABLE_*_LOGIC` synthesis-cone parameters and the `cfg_compl_enable` / `cfg_threshold_enable` / `cfg_debug_enable` control enables are also passed straight through.

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

### Parameter Relationships

- **`cfg_cg_enable = 0`**: bypasses the gate at runtime; behavior is identical to base
- **`cfg_cg_idle_count`**: higher values keep the clock running longer after traffic stops, so the block is gated less often. It does not change wake-up latency, which is fixed at 1 register stage / 2 clocks to the first usable edge.

---

### Derived Parameters (do not override)

These are declared as `parameter` so the elaborator can compute them, not so callers can set them. Each defaults to an expression over the parameters above; overriding one desynchronises it from its source and the design fails to elaborate or silently mis-sizes a bus. Set the parameters they are derived FROM and leave these alone.

| Derived parameter | Default expression |
|---|---|
| `AXI_WSTRB_WIDTH` | `AXI_DATA_WIDTH / 8` |
| `AW` | `AXI_ADDR_WIDTH` |
| `DW` | `AXI_DATA_WIDTH` |
| `IW` | `AXI_ID_WIDTH` |
| `SW` | `AXI_WSTRB_WIDTH` |
| `UW` | `AXI_USER_WIDTH` |

## Functional Description

### Clock Gating Architecture

ONE `amba_clock_gate_ctrl` gates the whole inner monitor module. The wake
term is bus activity plus pending monitor work (`fub_axi_arvalid ||
fub_axi_rvalid || int_busy || w_monbus_valid || (|active_transactions)`
on the user side, `m_axi_arvalid || m_axi_rvalid` on the AXI side); when
both sides idle for `cfg_cg_idle_count` cycles with nothing pending on
the monitor bus and the monitor CAM empty, everything inside --
transaction tracking, reporter, timers, perf counters -- stops together.
There are no per-domain gates. The external `monbus_valid` is masked with
`!cg_gating`, so monitor-bus delivery is exactly-once across gating at
any idle count (`val/amba/test_mon_cg_gating.py` phase 6): a packet
pending delivery holds the block awake, and the CAM-occupancy term covers
the reporter's few-cycle retire -> FIFO -> output emission window, so a
trailing packet cannot be stranded by the clock stopping before its valid
rises -- even at `cfg_cg_idle_count = 0`.

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

**WARNING -- gating vs window accounting.** The whole inner monitor runs on
the gated clock, window state machine and counters included. An open
measurement window is not one of the terms that keeps the clock alive:
`user_valid` is bus valids, `busy`, and pending monitor-bus work, and nothing
else.

Two consequences:

- **Counters freeze.** If the bus idles past the countdown while a window is
  open, the clock gates and `window_cycles` and the perf counters stop while
  wall-clock time keeps passing. The host reads an under-counted window and
  has no indication it was short.
- **Pulses are dropped.** `cam_clear`, `cfg_start_trigger`, `cfg_end_trigger`
  and `cfg_window_force_close` are sampled in the gated domain, so a pulse
  that arrives while the clock is gated is lost entirely.

For exact wall-clock windows, or for triggering on an idle bus, hold
`cfg_cg_enable` low across the measurement or use the base module.

---

## Timing Characteristics

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

## Usage Examples

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

**These numbers are illustrative, not measured.** No power analysis has been
run on this library -- `axi4_master_rd_cg.md` states the ground truth: power
saving is "traffic-dependent; unmeasured in this repo -- treat any percentage
as a placeholder until characterized." The shape of the curve (more idle time
and a shorter idle count save more) is sound; the specific percentages are
not sourced and disagree with the guide's table at comparable duty cycles.
Treat the rows as a sketch of the trend.

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

## Testing

`val/amba/test_axi4_master_rd_mon_cg.py` exercises this module. It collects 3 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/amba/test_axi4_master_rd_mon_cg.py -v
```

---

## Navigation

- **[← Back to Base Module](./axi4_master_rd_mon.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
