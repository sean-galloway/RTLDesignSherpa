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

# AXI5 Master Read with Monitor and Clock Gating

**Module:** `axi5_master_rd_mon_cg.sv`
**Location:** `rtl/amba/axi5/` (protocol monitors live with their protocol; only the monitor CORE pieces are in `rtl/amba/monitor/`)
**Status:** Production Ready

---

## Overview

The AXI5 Master Read with Monitor and Clock Gating module combines `axi5_master_rd_mon` (AXI5 master with integrated monitoring) with intelligent clock gating for power optimization. This is the everything variant: comprehensive transaction monitoring, error detection, and automatic power management in one instantiation.

### Key Features

- Full AMBA AXI5 protocol compliance
- **All AXI5 extensions:** NSAID, TRACE, MPAM, MECID, UNIQUE, CHUNKING, MTE, POISON
- **Integrated AXI monitor** with 2-Level Filtering: packet-type drop masks + per-event masks (err_select is reserved -- no routing)
- **Error detection:** Protocol violations, SLVERR, DECERR
- **Timeout monitoring:** Stuck transactions, stalled channels
- **Performance metrics:** Latency, throughput, outstanding transactions
- **MonBus output:** Standardized 128-bit monitor packet format paired with 64-bit side-band timestamp
- **Automatic clock gating** based on activity detection
- **Configurable idle threshold** before clock gating activates
- **Power savings** during idle periods
- **Transparent operation** - no protocol changes
- **Dual status outputs:** Monitor status + clock gating status

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH_AR | int | 2 | AR channel SKID buffer depth |
| SKID_DEPTH_R | int | 4 | R channel SKID buffer depth |
| AXI_ID_WIDTH | int | 8 | Transaction ID width |
| AXI_ADDR_WIDTH | int | 32 | Address bus width |
| AXI_DATA_WIDTH | int | 32 | Data bus width |
| AXI_USER_WIDTH | int | 1 | User signal width |
| AXI_NSAID_WIDTH | int | 4 | Non-secure access ID width |
| AXI_MPAM_WIDTH | int | 11 | MPAM width (PartID + PMG) |
| AXI_MECID_WIDTH | int | 16 | Memory encryption context ID width |
| AXI_TAG_WIDTH | int | 4 | Memory tag width per 16 bytes |
| AXI_TAGOP_WIDTH | int | 2 | Tag operation width |
| AXI_CHUNKNUM_WIDTH | int | 4 | Chunk number width |
| ENABLE_NSAID | bit | 1 | Enable non-secure access ID |
| ENABLE_TRACE | bit | 1 | Enable trace signals |
| ENABLE_MPAM | bit | 1 | Enable memory partitioning |
| ENABLE_MECID | bit | 1 | Enable memory encryption context |
| ENABLE_UNIQUE | bit | 1 | Enable unique ID indicator |
| ENABLE_CHUNKING | bit | 1 | Enable data chunking |
| ENABLE_MTE | bit | 1 | Enable Memory Tagging Extension |
| ENABLE_POISON | bit | 1 | Enable poison indicator |
| UNIT_ID | int | 1 | Monitor unit identifier |
| AGENT_ID | int | 10 | Monitor agent identifier |
| MAX_TRANSACTIONS | int | 16 | Transaction table size |
| `ENABLE_FILTERING` | bit | 1 | Enable packet filtering: two active drop levels (packet type, then event code). Level 2 is reserved and routes nothing |
| ADD_PIPELINE_STAGE | bit | 0 | Add pipeline stage in monitor |
| USE_MONITOR | bit | 1 | Synthesis-time monitor enable (forwarded to inner monitor). |
| N_ADDR_RANGES | int | 0 | Number of address-range comparators (forwarded to base module). |
| ENABLE_ERROR_LOGIC | bit | 1 | Synthesis-cone enable for error detection (forwarded to base module) |
| ENABLE_TIMEOUT_LOGIC | bit | 1 | Synthesis-cone enable for timeout detection (forwarded to base module) |
| ENABLE_COMPL_LOGIC | bit | 1 | Synthesis-cone enable for completion tracking (forwarded to base module) |
| ENABLE_THRESHOLD_LOGIC | bit | 1 | Synthesis-cone enable for threshold detection (forwarded to base module) |
| ENABLE_PERF_LOGIC | bit | 1 | Synthesis-cone enable for the REPORTER's legacy perf-packet cone and the two lifetime counters only -- the window FSM and bucket/beat/byte/burst counters are unconditional (always compiled, always live) |
| ENABLE_DEBUG_LOGIC | bit | 0 | Synthesis-cone enable for the debug/trace cone (forwarded to base module) |
| CG_IDLE_COUNT_WIDTH | int | 4 | Width of idle counter (max 2^N-1 cycles) |

---

## Ports

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| aclk | 1 | Input | AXI clock (ungated) |
| aresetn | 1 | Input | AXI active-low reset |

### Clock Gating Configuration

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cfg_cg_enable | 1 | Input | Clock gating enable (1=enable, 0=always active) |
| cfg_cg_idle_count | CG_IDLE_COUNT_WIDTH | Input | Idle cycles before gating activates |

### FUB AXI5 Interface (Slave Side - Input)

Same as `axi5_master_rd_mon` - see [AXI5 Master Read Monitor](axi5_master_rd_mon.md).

### Master AXI5 Interface (Output Side)

Same as `axi5_master_rd_mon` - see [AXI5 Master Read Monitor](axi5_master_rd_mon.md).

### Monitor Configuration

Same as `axi5_master_rd_mon` - see [AXI5 Master Read Monitor](axi5_master_rd_mon.md).

### Monitor Bus Output

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| monbus_valid | 1 | Output | Monitor packet valid |
| monbus_ready | 1 | Input | Monitor packet ready (backpressure) |
| monbus_packet | 128 | Output | `monitor_packet_t` (128-bit format) |
| monbus_timestamp | 64 | Output | `monbus_timestamp_t` paired atomically with `monbus_packet` |
| i_mon_time | 64 | Input | Free-running counter from `monbus_group_core`, sampled at packet emission |

### Status Outputs

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| busy | 1 | Output | Core busy indicator |
| active_transactions | 8 | Output | Number of outstanding transactions |
| error_count | 16 | Output | Cumulative error count (live -- driven from the reporter's lifetime counter) |
| transaction_count | 32 | Output | Total transaction count (live -- reporter lifetime counter, zero-extended) |
| cfg_conflict_error | 1 | Output | Configuration conflict detected |
| cg_gating | 1 | Output | Clock gating active (1=gated, 0=running) |
| cg_idle | 1 | Output | Interface idle (1=no activity) |

---

## Functional Description

### Architecture

```mermaid
flowchart TB
    subgraph FUB["FUB Interface"]
        direction LR
        fub_ar["AR Channel"]
        fub_r["R Channel"]
    end

    subgraph CG["Clock Gating Controller"]
        direction TB
        activity["Activity<br/>Detection"]
        idle_cnt["Idle Counter"]
        gate_ctrl["Gate Control"]

        activity --> idle_cnt
        idle_cnt --> gate_ctrl
    end

    subgraph MON_CORE["AXI5 Master Read Monitor"]
        direction TB
        axi5_core["AXI5 Master<br/>+ SKID Buffers"]
        monitor["AXI Monitor<br/>Filtered"]

        axi5_core -->|Taps| monitor
    end

    subgraph OUTPUTS["Outputs"]
        direction TB
        m_axi["AXI5 Master<br/>Interface"]
        monbus["Monitor Bus<br/>Packets"]
        status["Status:<br/>busy, active_trans<br/>cg_gating, cg_idle"]
    end

    fub_ar --> activity
    fub_r --> activity
    m_axi --> activity

    activity --> idle_cnt
    gate_ctrl -->|gated_aclk| axi5_core

    fub_ar --> axi5_core
    axi5_core --> fub_r
    axi5_core --> m_axi

    monitor --> monbus
    axi5_core --> status
    gate_ctrl --> status
```

### Combined Monitoring and Power Management

This module provides the best of both worlds:

**Monitoring (from axi5_master_rd_mon):**
- Real-time transaction monitoring
- Error and timeout detection
- Performance metrics collection
- Configurable packet filtering
- MonBus output for system integration

**Power Management (from axi5_master_rd_cg):**
- Automatic clock gating during idle periods
- Configurable idle threshold
- Activity-based wake-up
- Status outputs for power monitoring

### Clock Gating with Monitor Active

The clock gating logic considers monitor activity:

```systemverilog
user_valid = fub_axi_arvalid || fub_axi_rvalid || int_busy ||
             w_monbus_valid || (|active_transactions);  // peer VALID, never peer READY
axi_valid = m_axi_arvalid || m_axi_rvalid;

// Clock remains active if:
// - User interface active (AR or R channels)
// - AXI interface active
// - CORE busy (transactions in flight in the datapath)
// - A monitor packet is pending on the monitor bus (w_monbus_valid)
// - The monitor CAM still holds entries (|active_transactions) -- covers
//   the reporter's retire -> FIFO -> output emission window
```

**Monitor-bus delivery is exactly-once across gating, at any idle count.**
A packet pending on the monitor bus is a wake term: the block stays awake
(or re-wakes within a cycle) until the consumer accepts it, and the
external `monbus_valid` is masked with `!cg_gating` so a consumer can
never sample a valid that the reporter's stopped clock could not retire.
The monitor CAM's occupancy (`active_transactions`) is a wake term too: a
tracked entry stays in the CAM until its packet is marked into the
reporter FIFO, and the registered count lags one cycle past that, meeting
`monbus_valid`'s assertion -- so the clock cannot stop inside the
reporter's few-cycle emission window and strand a trailing packet, even
at `cfg_cg_idle_count = 0`. `val/amba/test_mon_cg_gating.py` phase 6
asserts exactly-once delivery of exactly the packets generated.

### Ready Signal Control During Gating

When clock gating is active, ready signals are forced low to prevent new transactions:

```systemverilog
fub_axi_arready = cg_gating ? 1'b0 : int_arready;
m_axi_rready = cg_gating ? 1'b0 : int_rready;
```

This ensures protocol compliance during power management.

### Performance Monitoring

The clock-gated wrapper exposes the full perfmon interface of the base module and **forwards every port unchanged** to the inner `axi5_master_rd_mon`. The measurement-window state machine, the four R-channel utilization buckets (productive / back-pressure / starvation / idle), and the beat/byte/burst throughput counters behave exactly as documented in the base module — see [Performance Monitoring in axi5_master_rd_mon](axi5_master_rd_mon.md#performance-monitoring) for the full narrative and per-bit semantics.

Forwarded perfmon ports (identical width and direction to the base module):

- **Inputs:** `cfg_perf_enable`, `cfg_start_event_sel` (3), `cfg_end_event_sel` (3), `cfg_start_trigger`, `cfg_end_trigger`, `cfg_window_force_close`
- **Outputs:** `window_active`, `window_cycles` (32), `perf_prod_cycles` (32), `perf_bp_cycles` (32), `perf_starv_cycles` (32), `perf_idle_cycles` (32), `perf_beat_count` (32), `perf_byte_count` (64), `perf_burst_count` (32)

The `perf_burst_count` output tracks AR (read address) handshakes.
**WARNING:** an open measurement window is NOT a wake term -- the window
FSM and all counters run on the gated clock, so if the bus idles past
`cfg_cg_idle_count` mid-window, `window_cycles` and the four buckets
FREEZE while wall-clock time passes. For exact wall-clock windows hold
`cfg_cg_enable` low around the measurement, or use the base module.

Alongside perfmon, the wrapper forwards the `cfg_compl_enable`, `cfg_threshold_enable`, and `cfg_debug_enable` control inputs, plus the six `ENABLE_*_LOGIC` synthesis-cone parameters (see [Parameters](#parameters)), straight through to the base monitor.

---

## Timing

### Clock Gating with Monitor Activity

> **Timing diagram pending.** The signals and sequence this scenario
> exercises:
>
> - ACLK (ungated)
> - GATED_ACLK (gated clock)
> - AXI transaction sequence
> - Monitor packet generation
> - Idle period detection
> - cg_gating activation
> - Monitor quiescent before clock stops


### Wake-up with Immediate Monitoring

> **Timing diagram pending.** The signals and sequence this scenario
> exercises:
>
> - ACLK (ungated)
> - GATED_ACLK resuming
> - ARVALID assertion (wake trigger)
> - cg_gating deactivation
> - AXI transaction proceeds
> - Monitor packets generated immediately


---

## Usage Example

### Comprehensive Debug + Power Optimization

```systemverilog
axi5_master_rd_mon_cg #(
    .AXI_ID_WIDTH       (8),
    .AXI_ADDR_WIDTH     (32),
    .AXI_DATA_WIDTH     (64),
    .AXI_USER_WIDTH     (4),
    .SKID_DEPTH_AR      (2),
    .SKID_DEPTH_R       (4),
    // Enable all AXI5 features
    .ENABLE_NSAID       (1),
    .ENABLE_TRACE       (1),
    .ENABLE_MPAM        (1),
    .ENABLE_MECID       (1),
    .ENABLE_UNIQUE      (1),
    .ENABLE_CHUNKING    (1),
    .ENABLE_MTE         (1),
    .ENABLE_POISON      (1),
    // Monitor configuration
    .UNIT_ID            (1),
    .AGENT_ID           (10),
    .MAX_TRANSACTIONS   (16),
    .ENABLE_FILTERING   (1),
    // Clock gating configuration
    .CG_IDLE_COUNT_WIDTH (4)
) u_axi5_master_rd_mon_cg (
    .aclk               (axi_clk),
    .aresetn            (axi_rst_n),

    // Clock gating configuration
    .cfg_cg_enable      (power_save_enable),
    .cfg_cg_idle_count  (4'd3),  // Gate after 4 idle cycles

    // FUB and Master interfaces
    // ... (connect AXI5 signals)

    // Monitor configuration - FUNCTIONAL DEBUG MODE
    .cfg_monitor_enable (1'b1),        // master monitor enable
    .cfg_compl_enable   (1'b1),        // completions (real port -- floating it defeats the FFF4 mask's intent)
    .cfg_error_enable   (1'b1),        // Errors
    .cfg_timeout_enable (1'b1),        // Timeouts
    .cfg_perf_enable    (1'b0),        // DISABLED
    .cfg_timeout_cycles (16'd10),   // 10 microseconds per phase (full 16-bit range)
    .cfg_latency_threshold (32'd500),

    // Filtering configuration
    .cfg_axi_pkt_mask   (16'hFFF4),    // Drop all but ERROR|COMPL|TIMEOUT (set bit = drop)
    .cfg_axi_err_select (16'h0000),  // No error re-routing
    .cfg_axi_error_mask (16'h0000),    // set bit = drop
    .cfg_axi_timeout_mask (16'h0000),
    .cfg_axi_compl_mask (16'h0000),

    // Monitor bus
    .monbus_valid       (mon_valid),
    .monbus_ready       (mon_ready),
    .monbus_packet      (mon_pkt),

    // Status outputs
    .busy               (master_busy),
    .active_transactions (active_trans),
    .cfg_conflict_error (cfg_error),
    .cg_gating          (clock_gated),
    .cg_idle            (interface_idle)
);

// Monitor packet consumer with power-aware handling
always_ff @(posedge axi_clk or negedge axi_rst_n) begin
    if (!axi_rst_n) begin
        mon_pkt_count <= '0;
        power_cycles_saved <= '0;
    end else begin
        // Count monitor packets
        if (mon_valid && mon_ready)
            mon_pkt_count <= mon_pkt_count + 1;

        // Track power savings
        if (clock_gated)
            power_cycles_saved <= power_cycles_saved + 1;
    end
end

// Alert on configuration conflicts
assert property (@(posedge axi_clk) disable iff (!axi_rst_n)
    !cfg_error
) else $error("Monitor configuration conflict detected!");

// Downstream FIFO for monitor packets
gaxi_fifo_sync #(
    .DATA_WIDTH (128),
    .DEPTH      (256)
) u_mon_fifo (
    .axi_aclk      (axi_clk),
    .axi_aresetn    (axi_rst_n),
    .wr_valid    (mon_valid),
    .wr_data     (mon_pkt),
    .wr_ready    (mon_ready),
    .rd_valid    (fifo_valid),
    .rd_data     (fifo_pkt),
    .rd_ready    (consumer_ready)
);
```

---

## Design Notes

### When to Use This Module

**Ideal for:**
- Battery-powered or power-sensitive systems
- Bursty traffic patterns with significant idle periods
- Systems requiring comprehensive debug visibility
- Production systems needing runtime monitoring + power optimization

**Consider alternatives if:**
- Continuous, high-throughput traffic (clock gating ineffective)
- Ultra-low latency requirements (avoid gating overhead)
- Area-constrained designs (monitor + CG adds ~10% area)

### Configuration Strategy Matrix

| Scenario | Monitor Config | Clock Gating Config | Expected Benefit |
|----------|---------------|---------------------|------------------|
| **Development/Debug** | ERROR + COMPL + TIMEOUT | Disabled | Full visibility, no wake latency |
| **Performance Tuning** | ERROR + PERF | Disabled | Metrics without power interference |
| **Power Testing** | ERROR only | Aggressive (count=0) | Maximum power savings |
| **Production** | ERROR + TIMEOUT | Balanced (count=3) | Error detection + power savings |

### Monitor + Clock Gating Interaction

**Key Considerations:**

1. **Monitor packets generated before gating:**
   - Monitor processes all events before idle state
   - MonBus packets FREEZE when the clock stops (see the WARNING above -- nothing flushes them)
   - No events lost during gating transition

2. **Wake latency includes monitor initialization:**
   - 1 wake-up register stage; first usable gated-clock edge 2 cycles after activity
   - Monitor ready immediately (no reset needed)
   - First transaction monitored correctly

3. **Power savings account for monitor overhead:**
   - Monitor adds ~10% dynamic power when active
   - Clock gating saves ~80-90% when idle (first-order estimate -- no power analysis has been run; same disclaimer as the sibling _cg page)
   - Net savings: 70-80% during idle periods

### Verification Recommendations

1. **Test monitor + CG independently first:**
   ```systemverilog
   // Phase 1: Monitor only (CG disabled)
   .cfg_cg_enable (1'b0)
   // Verify all monitor features

   // Phase 2: CG only (monitor minimal)
   .cfg_monitor_enable (1'b0)
   .cfg_error_enable   (1'b0)
   .cfg_cg_enable      (1'b1)
   // Verify clock gating behavior

   // Phase 3: Combined
   // Both enabled, verify interaction
   ```

2. **Check monitor packet integrity across gating:**
   - No packets lost during gating transitions
   - No duplicate packets
   - Timestamps/latencies accurate

3. **Measure actual power savings:**
   - Instrument with power counters
   - Compare vs. always-on baseline
   - Verify efficiency in target traffic patterns

---

## Related Modules

- **[AXI5 Master Read](../axi5/axi5_master_rd.md)** - Base module
- **[AXI5 Master Read CG](../axi5/axi5_master_rd_cg.md)** - Clock gating only
- **[AXI5 Master Read Monitor](axi5_master_rd_mon.md)** - Monitor only
- **[AXI5 Master Write Monitor CG](axi5_master_wr_mon_cg.md)** - Write variant
- **[AXI Monitor Configuration Guide](../../../user-guides/AXI_Monitor_Configuration_Guide.md)** - Monitor setup
- **[AMBA Clock Gate Controller](../shared/amba_clock_gate_ctrl.md)** - Clock gating details

---

## Navigation

- **[← Back to AXI5 Index](../_book_monitor_index.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
