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
**Status:** Production Ready

---

## Overview

This is the **clock-gated variant** of [axi4_master_wr_mon](./axi4_master_wr_mon.md) — the same monitored master write, with activity-based clock gating wrapped around it.

For complete clock-gating documentation, usage examples, and configuration guidelines, see the **[Clock-Gated Variants Guide](../shared/clock_gated_variants.md)**.

What the wrapper buys you:

- **Same Functionality:** 100% equivalent to base module
- **Power Savings:** traffic-dependent; unmeasured in this repo -- treat any percentage as a placeholder until characterized
- **Configurable:** Idle threshold, gating domains, enable/disable
- **Zero Overhead When Disabled:** `cfg_cg_enable=0` bypasses the gate at runtime

---

## Parameters

MOST [axi4_master_wr_mon](./axi4_master_wr_mon.md) parameters pass through. As of 2026-09-01 only
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
| `ADD_PIPELINE_STAGE` | `0` | Insert a register stage for timing closure. Costs a cycle of latency. (Add register stage for timing closure) |
| `ENABLE_COMPL_LOGIC` | `1'b1` | Synthesise the completion-packet cone. 0 removes the logic entirely. |
| `ENABLE_DEBUG_LOGIC` | `1'b0` | Synthesise the debug-packet cone. 0 removes the logic entirely. |
| `ENABLE_ERROR_LOGIC` | `1'b1` | Synthesise the error detection cone. 0 removes the logic entirely. |
| `ENABLE_FILTERING` | `1` | Enable packet filtering: two active drop levels (packet type, then event code). Level 2 is reserved and routes nothing. |
| `ENABLE_PERF_LOGIC` | `1'b1` | Synthesise the reporter's performance cone (`g_perf`). Does NOT gate the perfmon window state machine or its counters. |
| `ENABLE_THRESHOLD_LOGIC` | `1'b1` | Synthesise the threshold-packet cone. 0 removes the logic entirely. |
| `ENABLE_TIMEOUT_LOGIC` | `1'b1` | Synthesise the timeout detection cone. 0 removes the logic entirely. |
| `SKID_DEPTH_AW` | `2` | Skid-buffer depth on the AW channel. Legal range 2..8 inclusive; odd depths are legal. |
| `SKID_DEPTH_B` | `2` | Skid-buffer depth on the B channel. Legal range 2..8 inclusive; odd depths are legal. |
| `SKID_DEPTH_W` | `4` | Skid-buffer depth on the W channel. Legal range 2..8 inclusive; odd depths are legal. |
| `AGENT_ID` | `16'h000B` | Agent identifier emitted in the `agent_id` field of every monitor packet. Pairs with `UNIT_ID` to identify the packet source. (16-bit Agent ID for monitor packets) |
| `UNIT_ID` | `8'h01` | Unit identifier emitted in the `unit_id` field of every monitor packet. Give each monitored interface a distinct value or the packets cannot be told apart at the collector. (8-bit Unit ID for monitor packets) |

Gating is controlled by RUNTIME inputs `cfg_cg_enable` /
`cfg_cg_idle_count` with status outputs `cg_gating` / `cg_idle`; ONE
`amba_clock_gate_ctrl` gates the entire inner module (no per-domain
gates). (The ENABLE_CLOCK_GATING / CG_IDLE_CYCLES / CG_GATE_* interface
this page once documented never existed.)

Base-module ports are forwarded EXCEPT `debug_block_ready`, which this wrapper ties off (use the base module for the backpressure tap). `cam_clear` is forwarded (Input, 1) - synchronous clear of the monitor transaction CAM (driven from the harness clear control bit, e.g. CTRL[4]) - and the full performance-monitoring interface (see [Performance Monitoring](#performance-monitoring) below). The six `ENABLE_*_LOGIC` synthesis-cone parameters and the `cfg_compl_enable` / `cfg_threshold_enable` / `cfg_debug_enable` control enables are also passed straight through.

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

## Ports

| Port | Dir | Width | Description |
|---|---|---|---|
| `aclk` | In | 1 |  |
| `aresetn` | In | 1 |  |
| `cam_clear` | In | 1 | sync clear of the monitor trans CAM |
| `fub_axi_awid` | In | `[IW-1:0]` |  |
| `fub_axi_awaddr` | In | `[AW-1:0]` |  |
| `fub_axi_awlen` | In | `[7:0]` |  |
| `fub_axi_awsize` | In | `[2:0]` |  |
| `fub_axi_awburst` | In | `[1:0]` |  |
| `fub_axi_awlock` | In | 1 |  |
| `fub_axi_awcache` | In | `[3:0]` |  |
| `fub_axi_awprot` | In | `[2:0]` |  |
| `fub_axi_awqos` | In | `[3:0]` |  |
| `fub_axi_awregion` | In | `[3:0]` |  |
| `fub_axi_awuser` | In | `[UW-1:0]` |  |
| `fub_axi_awvalid` | In | 1 |  |
| `fub_axi_awready` | Out | 1 |  |
| `fub_axi_wdata` | In | `[DW-1:0]` |  |
| `fub_axi_wstrb` | In | `[SW-1:0]` |  |
| `fub_axi_wlast` | In | 1 |  |
| `fub_axi_wuser` | In | `[UW-1:0]` |  |
| `fub_axi_wvalid` | In | 1 |  |
| `fub_axi_wready` | Out | 1 |  |
| `fub_axi_bid` | Out | `[IW-1:0]` |  |
| `fub_axi_bresp` | Out | `[1:0]` |  |
| `fub_axi_buser` | Out | `[UW-1:0]` |  |
| `fub_axi_bvalid` | Out | 1 |  |
| `fub_axi_bready` | In | 1 |  |
| `m_axi_awid` | Out | `[IW-1:0]` |  |
| `m_axi_awaddr` | Out | `[AW-1:0]` |  |
| `m_axi_awlen` | Out | `[7:0]` |  |
| `m_axi_awsize` | Out | `[2:0]` |  |
| `m_axi_awburst` | Out | `[1:0]` |  |
| `m_axi_awlock` | Out | 1 |  |
| `m_axi_awcache` | Out | `[3:0]` |  |
| `m_axi_awprot` | Out | `[2:0]` |  |
| `m_axi_awqos` | Out | `[3:0]` |  |
| `m_axi_awregion` | Out | `[3:0]` |  |
| `m_axi_awuser` | Out | `[UW-1:0]` |  |
| `m_axi_awvalid` | Out | 1 |  |
| `m_axi_awready` | In | 1 |  |
| `m_axi_wdata` | Out | `[DW-1:0]` |  |
| `m_axi_wstrb` | Out | `[SW-1:0]` |  |
| `m_axi_wlast` | Out | 1 |  |
| `m_axi_wuser` | Out | `[UW-1:0]` |  |
| `m_axi_wvalid` | Out | 1 |  |
| `m_axi_wready` | In | 1 |  |
| `m_axi_bid` | In | `[IW-1:0]` |  |
| `m_axi_bresp` | In | `[1:0]` |  |
| `m_axi_buser` | In | `[UW-1:0]` |  |
| `m_axi_bvalid` | In | 1 |  |
| `m_axi_bready` | Out | 1 |  |
| `cfg_monitor_enable` | In | 1 | Enable monitoring |
| `cfg_error_enable` | In | 1 | Enable error detection |
| `cfg_timeout_enable` | In | 1 | Enable timeout detection |
| `cfg_perf_enable` | In | 1 | Enable performance monitoring |
| `cfg_compl_enable` | In | 1 | Enable completion packets |
| `cfg_threshold_enable` | In | 1 | Enable threshold packets |
| `cfg_debug_enable` | In | 1 | Enable debug packets |
| `cfg_timeout_cycles` | In | `[15:0]` | Timeout threshold in MICROSECONDS (1 us tick), despite the name |
| `cfg_freq_sel` | In | `[3:0]` | counter_freq_invariant LUT index |
| `cfg_latency_threshold` | In | `[31:0]` | Latency threshold for alerts |
| `cfg_axi_pkt_mask` | In | `[15:0]` | Drop mask for packet types |
| `cfg_axi_err_select` | In | `[15:0]` | Error select for packet types (for future routing) |
| `cfg_axi_error_mask` | In | `[15:0]` | Individual error event mask |
| `cfg_axi_timeout_mask` | In | `[15:0]` | Individual timeout event mask |
| `cfg_axi_compl_mask` | In | `[15:0]` | Individual completion event mask |
| `cfg_axi_thresh_mask` | In | `[15:0]` | Individual threshold event mask |
| `cfg_axi_perf_mask` | In | `[15:0]` | Individual performance event mask |
| `cfg_axi_addr_mask` | In | `[15:0]` | Individual address match event mask |
| `cfg_axi_debug_mask` | In | `[15:0]` | Individual debug event mask |
| `cfg_cg_enable` | In | 1 | Enable clock gating |
| `cfg_cg_idle_count` | In | `[CG_IDLE_COUNT_WIDTH-1:0]` | Idle cycles before gating |
| `cfg_addr_check_enable` | In | 1 |  |
| `cfg_addr_range_enable` | In | `[(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]` |  |
| `cfg_addr_range_low` | In | `[(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]` |  |
| `cfg_addr_range_high` | In | `[(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]` |  |
| `cfg_addr_filter_enable` | In | 1 |  |
| `cfg_addr_filter_low` | In | `[AW-1:0]` |  |
| `cfg_addr_filter_high` | In | `[AW-1:0]` |  |
| `cfg_id_filter_enable` | In | 1 |  |
| `cfg_id_match_base` | In | `[IW-1:0]` |  |
| `cfg_id_match_count` | In | `[IW:0]` |  |
| `i_mon_time` | In | 1 |  |
| `monbus_valid` | Out | 1 | Monitor bus valid |
| `monbus_ready` | In | 1 | Monitor bus ready |
| `monbus_packet` | Out | 1 | Monitor packet (128-bit) |
| `monbus_timestamp` | Out | 1 | Side-band sampled time |
| `busy` | Out | 1 |  |
| `active_transactions` | Out | `[7:0]` | Number of active transactions |
| `error_count` | Out | `[15:0]` | Total error count |
| `transaction_count` | Out | `[31:0]` | Total transaction count |
| `cg_gating` | Out | 1 | Gated clock is stopped |
| `cg_idle` | Out | 1 | No activity observed |
| `cfg_conflict_error` | Out | 1 | Configuration conflict detected |
| `cfg_start_event_sel` | In | `[2:0]` |  |
| `cfg_end_event_sel` | In | `[2:0]` |  |
| `cfg_start_trigger` | In | 1 |  |
| `cfg_end_trigger` | In | 1 |  |
| `cfg_window_force_close` | In | 1 |  |
| `window_active` | Out | 1 |  |
| `window_cycles` | Out | `[31:0]` |  |
| `perf_prod_cycles` | Out | `[31:0]` |  |
| `perf_bp_cycles` | Out | `[31:0]` |  |
| `perf_starv_cycles` | Out | `[31:0]` |  |
| `perf_idle_cycles` | Out | `[31:0]` |  |
| `perf_beat_count` | Out | `[31:0]` |  |
| `perf_byte_count` | Out | `[63:0]` |  |
| `perf_burst_count` | Out | `[31:0]` |  |

---

## Functional Description

### Performance Monitoring

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

## Timing Characteristics

| Skid parameter | Default depth |
|---|---|
| `SKID_DEPTH_AW` | 2 entries |
| `SKID_DEPTH_W` | 4 entries |
| `SKID_DEPTH_B` | 2 entries |

Each channel traverses one `gaxi_skid_buffer`, which registers both `rd_valid`
and its storage. The **1-cycle input-to-output latency therefore applies on
every transfer, including the unstalled case** -- there is no combinational
bypass. Depth buys backpressure absorption, not throughput; full rate is
sustained once the pipeline is primed. Legal range is 2..8 inclusive, odd
values included.

Clocking: `aclk`, reset `aresetn` (active-low asynchronous).

No synthesis numbers are quoted here. Frequency and area depend on the target
device and the parameters you elaborate with; run your own build.

---

## Usage Examples
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

## Related Modules

- **Base Module Functionality:** [axi4_master_wr_mon.md](./axi4_master_wr_mon.md)
- **Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb4_slave_cg.md](../apb4/apb4_slave_cg.md) (APB interface)

---

## Testing

`val/amba/test_axi4_master_wr_mon_cg.py` exercises this module. It collects 3 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/amba/test_axi4_master_wr_mon_cg.py -v
```

---

## Navigation

- **[← Back to AXI4 Index](../_book_monitor_index.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
