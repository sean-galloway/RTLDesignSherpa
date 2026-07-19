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

# AXI4 Slave Write Monitor

**Module:** `axi4_slave_wr_mon.sv`
**Location:** `rtl/amba/axi4/`
**Status:** ✅ Production Ready

---

## Overview

The AXI4 Slave Write Monitor module combines a functional AXI4 slave write interface with comprehensive transaction monitoring and filtering capabilities. This module is essential for verification environments, providing real-time protocol checking, error detection, performance metrics, and configurable packet filtering for slave-side write transactions.

### Key Features

- ✅ **Integrated Monitoring:** Combines `axi4_slave_wr` with `axi_monitor_filtered`
- ✅ **3-Level Filtering:** Packet type masks, error routing, individual event masking
- ✅ **Error Detection:** Protocol violations, SLVERR, DECERR, orphan transactions
- ✅ **Timeout Monitoring:** Configurable timeout detection for stuck transactions
- ✅ **Performance Metrics:** Latency tracking, transaction counting, throughput analysis
- ✅ **Monitor Bus Output:** 128-bit packets paired with 64-bit side-band timestamps
- ✅ **Configuration Validation:** Detects conflicting configuration settings
- ✅ **Clock Gating Support:** Busy signal for power management

---

## Module Architecture

```mermaid
flowchart LR
    subgraph SL["Slave<br/>(s_axi)"]
        aw["aw* →"]
        w["w* →"]
        b["← b*"]
    end

    subgraph CORE["Slave Core"]
        sc["axi4_slave_wr<br/>(buffered)"]
    end

    subgraph MON["Monitor"]
        mf["axi_monitor<br/>_filtered"]
        features["•error<br/>•timeout<br/>•perf"]
    end

    subgraph MB["Monitor Bus"]
        mbv["monbus_valid"]
        mbp["monbus_packet"]
    end

    aw --> sc
    w --> sc
    sc --> b
    sc --> mf
    mf --> mbv
    mf --> mbp
    sc --> fub["Backend (fub_axi)"]
```

The module instantiates two sub-modules:
1. **axi4_slave_wr** - Core AXI4 slave write functionality with buffering
2. **axi_monitor_filtered** - Transaction monitoring with 3-level filtering

---

## Parameters

### AXI4 Slave Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `SKID_DEPTH_AW` | int | 2 | AW channel skid buffer depth |
| `SKID_DEPTH_W` | int | 4 | W channel skid buffer depth |
| `SKID_DEPTH_B` | int | 2 | B channel skid buffer depth |
| `AXI_ID_WIDTH` | int | 8 | Transaction ID width |
| `AXI_ADDR_WIDTH` | int | 32 | Address bus width |
| `AXI_DATA_WIDTH` | int | 32 | Data bus width |
| `AXI_USER_WIDTH` | int | 1 | User signal width |

### Monitor Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `UNIT_ID` | int | 2 | 4-bit unit identifier in monitor packets |
| `AGENT_ID` | int | 21 | 8-bit agent identifier in monitor packets |
| `MAX_TRANSACTIONS` | int | 16 | Maximum concurrent outstanding transactions |
| `ENABLE_FILTERING` | bit | 1 | Enable packet filtering (0=pass all packets) |
| `ADD_PIPELINE_STAGE` | bit | 0 | Add register stage for timing closure |
| `USE_MONITOR` | bit | 1 | Synthesis-time monitor enable. 0 = omit monitor and tie outputs to safe non-blocking defaults; 1 = full monitor functionality. |
| `N_ADDR_RANGES` | int | 0 | Number of address-range comparators. 0 = checker omitted (zero area). >0 = N independent [low, high] ranges; hits emit PktTypeError + AXI_ERR_ADDR_RANGE on monbus. |

### Synthesis-Cone Parameters

Each detection cone can be compiled out to save area. The classic cones default on; the debug cone defaults off. Setting a bit to 0 drops the corresponding cone at synthesis via a `generate`-if inside `axi_monitor_reporter` — the area saving is real.

| Parameter | Type | Default | Effect when 0 |
|-----------|------|:-------:|---------------|
| `ENABLE_ERROR_LOGIC`     | bit | 1 | Drop the error-detection cone |
| `ENABLE_TIMEOUT_LOGIC`   | bit | 1 | Drop the timeout cone **and** the `axi_monitor_timeout` instance |
| `ENABLE_COMPL_LOGIC`     | bit | 1 | Drop the completion cone |
| `ENABLE_THRESHOLD_LOGIC` | bit | 1 | Drop the threshold cone |
| `ENABLE_PERF_LOGIC`      | bit | 1 | Drop the perfmon window + counters |
| `ENABLE_DEBUG_LOGIC`     | bit | 0 | Drop the debug (trace) cone — the 6th reporter sub-block (off by default) |

Internally the wrapper hardwires two master switches on its `axi_monitor_filtered` instance: `ENABLE_PERF_PACKETS = 1` (perf datapath present, so `ENABLE_PERF_LOGIC` alone gates the window/counters) and `ENABLE_DEBUG_MODULE = 0` (debug tracking module omitted). These are not top-level parameters of the wrapper.

The transaction CAM is always pipelined.

---

## Monitor Backpressure (block_ready)

The monitor exposes a `block_ready` signal that goes low when its internal FIFO is saturated and cannot accept a new in-flight transaction. The wrapper ANDs `block_ready` into the upstream-facing `s_axi_awready` so a saturated monitor stalls new transactions on the wire instead of dropping events.

- **Where the stall lands**: the upstream `s_axi_awready` is forced low until the monitor drains.
- **When `USE_MONITOR=0`**: `block_ready` is internally tied high, so the wrapper imposes no stall and runs at full bandwidth.

This replaces a previous bug where `block_ready` was left unconnected and a full monitor FIFO would silently lose events.

---

## Address-Range Checker

The wrapper can be parameterized with `N_ADDR_RANGES > 0` to instantiate an N-comparator address-range checker that watches every accepted AW handshake and emits a `PktTypeError` monbus packet (event code `AXI_ERR_ADDR_RANGE = 8'h0D`) when an address falls inside any of the configured `[low, high]` inclusive ranges.

**Config inputs (active only when `N_ADDR_RANGES > 0`):**
- `cfg_addr_check_enable` — master on/off for the checker.
- `cfg_addr_range_enable[N-1:0]` — per-range enable bit.
- `cfg_addr_range_low[N-1:0][AXI_ADDR_WIDTH-1:0]` — inclusive low bound for each range.
- `cfg_addr_range_high[N-1:0][AXI_ADDR_WIDTH-1:0]` — inclusive high bound for each range.

**Event encoding** (within the standard 128-bit `monitor_packet_t`, event_data field):
- `packet_type` = `PktTypeError` (4'h0)
- `protocol`    = AXI (3'b000)
- `event_code`  = `AXI_ERR_ADDR_RANGE` (8'h0D)
- `event_data[63:60]` = `range_index` (4 bits; supports up to 16 ranges)
- `event_data[59:0]`  = full matched address (up to 60 bits, zero-padded if narrower)

**Exact match:** set `cfg_addr_range_low[i] == cfg_addr_range_high[i]`.

**Filtering:** the existing `cfg_axi_error_mask[13]` bit masks this event code; set it high to suppress range packets without disabling other errors. No new mask wiring needed.

**Per-range coalescing:** if a range hits again before its packet has been emitted, the latched address is overwritten (latest hit wins). One packet per cycle drains the pending mask via a lowest-index priority encoder. Distinct ranges never lose events; under sustained per-range bursts, only the latest address per range is reported per emission cycle.

---

## Performance Monitoring

The wrapper hardwires `ENABLE_PERF_PACKETS = 1` on its inner `axi_monitor_filtered`, so the perfmon datapath is present whenever `ENABLE_PERF_LOGIC = 1` (the default). It instantiates a **measurement-window state machine** plus a bank of W-data-channel utilization counters. All counters accumulate **only while a window is open** (`window_active = 1`) and hold their values between windows, so the host can read a completed window's totals.

### The Measurement Window

A window is opened by a **start event** and closed by an **end event**. The event sources are selected by `cfg_start_event_sel` / `cfg_end_event_sel` (3-bit; e.g. `3'b010` selects the `cfg_perf_enable` edge) and can also be fired directly by the `cfg_start_trigger` / `cfg_end_trigger` pulses (from an engine or CSR). `cfg_window_force_close` is a software override that closes the window immediately. While the window is open:

- `window_active` is high.
- `window_cycles[31:0]` free-runs, counting every clock elapsed inside the window.

Sample the counters on the cycle `window_active` falls to 0 (drive `cfg_end_trigger`, or wait for the configured end event).

### Utilization Counters (W Data Channel)

Every cycle inside the window is classified by the W channel's `wvalid` / `wready` into exactly one of four buckets:

| Output | Width | Condition | Meaning |
|--------|:-----:|-----------|---------|
| `perf_prod_cycles`  | 32 | wvalid && wready   | productive beat transferred |
| `perf_bp_cycles`    | 32 | wvalid && !wready  | back-pressure (data offered, sink not ready) |
| `perf_starv_cycles` | 32 | !wvalid && wready  | starvation (sink ready, no data) |
| `perf_idle_cycles`  | 32 | !wvalid && !wready | idle |

The four buckets sum to `window_cycles`, so utilization = `perf_prod_cycles / window_cycles`.

### Throughput Counters

| Output | Width | Meaning |
|--------|:-----:|---------|
| `perf_beat_count`  | 32 | W data beats transferred (= `perf_prod_cycles`, 1 beat/cycle) |
| `perf_byte_count`  | 64 | bytes transferred = beats × (1 << AWSIZE), using the AWSIZE captured at the most recent AW address phase |
| `perf_burst_count` | 32 | AW address-phase handshakes |

The integrator computes average burst length as `perf_beat_count / perf_burst_count`.

### Performance Monitoring Ports

| Port | Direction | Width | Description |
|------|-----------|:-----:|-------------|
| `cfg_perf_enable`        | Input  | 1  | Enable performance-metric packet generation |
| `cfg_start_event_sel`    | Input  | 3  | Window **start** event source select |
| `cfg_end_event_sel`      | Input  | 3  | Window **end** event source select |
| `cfg_start_trigger`      | Input  | 1  | Pulse: open the measurement window |
| `cfg_end_trigger`        | Input  | 1  | Pulse: close the measurement window |
| `cfg_window_force_close` | Input  | 1  | Software override: force the window closed |
| `window_active`          | Output | 1  | High while a measurement window is open |
| `window_cycles`          | Output | 32 | Cycles elapsed in the current window |
| `perf_prod_cycles`       | Output | 32 | wvalid && wready cycles |
| `perf_bp_cycles`         | Output | 32 | wvalid && !wready cycles (back-pressure) |
| `perf_starv_cycles`      | Output | 32 | !wvalid && wready cycles (starvation) |
| `perf_idle_cycles`       | Output | 32 | !wvalid && !wready cycles |
| `perf_beat_count`        | Output | 32 | W data beats transferred |
| `perf_byte_count`        | Output | 64 | bytes transferred |
| `perf_burst_count`       | Output | 32 | AW address-phase handshakes |

When `USE_MONITOR = 0`, every perfmon output is tied to 0 and the window never opens.

---

## Port Groups

### AXI4 Write Channels

**Slave Interface (s_axi_*):**
- AW channel: `awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid, awready`
- W channel: `wdata, wstrb, wlast, wuser, wvalid, wready`
- B channel: `bid, bresp, buser, bvalid, bready`

**Backend Interface (fub_axi_*):**
- Same signals as slave, mirrored direction (to memory/backend)

### Monitor Configuration

Configuration ports are identical to other AXI4 monitors:
- Basic enables: `cfg_monitor_enable`, `cfg_error_enable`, `cfg_timeout_enable`, `cfg_perf_enable`, `cfg_compl_enable` (completion packets), `cfg_threshold_enable` (threshold-crossed packets), `cfg_debug_enable` (debug/trace cone — the 6th reporter sub-block)
- Clear: `cam_clear` (Input, 1) - synchronous clear of the monitor transaction CAM (driven from the harness clear control bit, e.g. CTRL[4])
- Thresholds: `cfg_timeout_cycles`, `cfg_latency_threshold`
- Filtering: 7 mask signals (`cfg_axi_*_mask`)
- Performance window control: `cfg_start_event_sel`, `cfg_end_event_sel`, `cfg_start_trigger`, `cfg_end_trigger`, `cfg_window_force_close` (see [Performance Monitoring](#performance-monitoring))

> The inner monitor's `cfg_debug_level` (tied to 0), `cfg_debug_mask` (0) and `cfg_active_trans_threshold` (8) are fixed inside the wrapper and are **not** top-level ports on this module.

### Monitor Bus Output

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `monbus_valid` | Output | 1 | Monitor packet valid |
| `monbus_ready` | Input | 1 | Downstream ready to accept packet |
| `monbus_packet` | Output | 128 | `monitor_packet_t` (see format below) |
| `monbus_timestamp` | Output | 64 | `monbus_timestamp_t` paired atomically with `monbus_packet` |
| `i_mon_time` | Input | 64 | Free-running counter from `monbus_axil_group`, sampled at packet emission |

### Status Outputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `busy` | Output | 1 | Indicates active transactions (for clock gating) |
| `active_transactions` | Output | 8 | Current number of outstanding transactions |
| `error_count` | Output | 16 | Cumulative error count |
| `transaction_count` | Output | 32 | Total transaction count |
| `cfg_conflict_error` | Output | 1 | Configuration conflict detected |

---

## Monitor Packet Format

Identical 128-bit format (with 64-bit side-band timestamp) as other AXI4 monitors. See [axi4_master_rd_mon](axi4_master_rd_mon.md) for complete specification.

---

## Timing Diagrams

The following waveforms show AXI4 slave write monitor behavior from the slave perspective:

### Scenario 1: Single-Beat Write (Slave View)

AXI4 write transaction from slave interface perspective:

![Single Beat Write Slave](../../assets/WAVES/axi4_slave_wr_mon/single_beat_write_001.png)

**WaveJSON:** [single_beat_write_001.json](../../assets/WAVES/axi4_slave_wr_mon/single_beat_write_001.json)

**Key Observations:**
- Slave-side AW channel (s_axi_aw*)
- Slave-side W channel data (s_axi_w*)
- Slave-side B channel response (s_axi_b*)
- Monitor packet generation from slave perspective
- Slave BRESP status monitoring
- Transaction tracking in slave context

### Scenario 2: Alternative Single-Beat Write (Slave View)

Variant write transaction with different timing from slave:

![Single Beat Write Slave Alt](../../assets/WAVES/axi4_slave_wr_mon/single_beat_write_002_001.png)

**WaveJSON:** [single_beat_write_002_001.json](../../assets/WAVES/axi4_slave_wr_mon/single_beat_write_002_001.json)

**Key Observations:**
- Slave ready signal behavior
- AWREADY backpressure effects
- WREADY flow control
- BVALID generation timing
- Slave latency monitoring
- Error detection from slave side

---

## Configuration Strategies

### Strategy 1: Functional Verification (Recommended)

**Goal:** Catch slave-side write errors

```systemverilog
// Enable configuration
.cfg_monitor_enable     (1'b1),
.cfg_error_enable       (1'b1),      // Detect SLVERR/DECERR from backend
.cfg_timeout_enable     (1'b1),      // Detect backend timeouts
.cfg_perf_enable        (1'b0),      // Disable (reduces traffic)

// Filtering - pass error and timeout only
.cfg_axi_pkt_mask       (16'b1111_1111_0000_0011),
.cfg_axi_error_mask     (16'h0000),  // Pass all errors
.cfg_axi_timeout_mask   (16'h0000),  // Pass all timeouts
.cfg_axi_compl_mask     (16'hFFFF),  // Drop completions
.cfg_axi_perf_mask      (16'hFFFF),  // Drop performance

// Timeouts
.cfg_timeout_cycles     (16'd2000),  // Backend write response timeout
.cfg_latency_threshold  (32'd1000)
```

### Strategy 2: Performance Analysis

**Goal:** Analyze slave write performance

```systemverilog
// Enable configuration
.cfg_monitor_enable     (1'b1),
.cfg_error_enable       (1'b1),
.cfg_timeout_enable     (1'b0),
.cfg_perf_enable        (1'b1),      // Enable performance metrics

// Filtering - pass error and performance only
.cfg_axi_pkt_mask       (16'b1111_1110_0000_0001),
.cfg_axi_error_mask     (16'h0000),  // Pass all errors
.cfg_axi_perf_mask      (16'h0000),  // Pass all performance
.cfg_axi_compl_mask     (16'hFFFF),  // Drop completions
```

---

## Usage Example

### Basic Integration with Memory

```systemverilog
axi4_slave_wr_mon #(
    .SKID_DEPTH_AW      (2),
    .SKID_DEPTH_W       (4),
    .SKID_DEPTH_B       (2),
    .AXI_ID_WIDTH       (4),
    .AXI_ADDR_WIDTH     (32),
    .AXI_DATA_WIDTH     (64),
    .AXI_USER_WIDTH     (1),
    .UNIT_ID            (2),
    .AGENT_ID           (21),
    .MAX_TRANSACTIONS   (16),
    .ENABLE_FILTERING   (1)
) u_slave_wr_mon (
    .aclk               (axi_aclk),
    .aresetn            (axi_aresetn),

    // Slave interface (from interconnect)
    .s_axi_awid         (s_axi_awid),
    .s_axi_awaddr       (s_axi_awaddr),
    // ... rest of AW/W/B signals

    // Backend interface (to memory controller)
    .fub_axi_awid       (mem_awid),
    .fub_axi_awaddr     (mem_awaddr),
    // ... rest of AW/W/B signals

    // Monitor configuration
    .cfg_monitor_enable     (1'b1),
    .cfg_error_enable       (1'b1),
    .cfg_timeout_enable     (1'b1),
    .cfg_perf_enable        (1'b0),
    .cfg_timeout_cycles     (16'd2000),  // Higher for memory latency
    .cfg_latency_threshold  (32'd1000),

    .cfg_axi_pkt_mask       (16'b1111_1111_0000_0011),
    .cfg_axi_error_mask     (16'h0000),
    .cfg_axi_timeout_mask   (16'h0000),
    .cfg_axi_compl_mask     (16'hFFFF),
    // ... rest of mask signals

    // Monitor bus output
    .monbus_valid           (mon_valid),
    .monbus_ready           (mon_ready),
    .monbus_packet          (mon_packet),

    // Status
    .busy                   (wr_slave_busy),
    .active_transactions    (wr_active),
    .error_count            (wr_errors),
    .transaction_count      (wr_count),
    .cfg_conflict_error     (cfg_conflict)
);

// Memory controller backend
memory_controller u_mem (
    .axi_aclk       (axi_aclk),
    .axi_aresetn    (axi_aresetn),
    // Connect to fub_axi_* signals
    .axi_awid       (mem_awid),
    .axi_awaddr     (mem_awaddr),
    // ...
);
```

---

## Design Notes

### Slave-Side Monitoring

**Key Differences from Master Monitors:**
- Monitors from slave perspective (interconnect → backend)
- Tracks backend write response latency
- Detects backend timeout scenarios
- Default UNIT_ID=2, AGENT_ID=21 (distinguishes from master)

**Slave Write Sequence:**
1. AW channel: Master write address arrives at slave
2. Monitor captures: Address, ID, burst parameters
3. AW forwarded to backend (memory/logic)
4. W channel: Master sends data beats
5. Monitor tracks: Write beat count, WLAST
6. B channel: Backend returns write response
7. Monitor tracks: Response latency, BRESP
8. B forwarded back to master via interconnect

**Common Slave Errors Detected:**
- **Backend timeout:** AW accepted but B never returned
- **Write data timeout:** AW accepted but W never completed
- **SLVERR:** Slave error (access violation, parity error, write protection)
- **DECERR:** Decode error (shouldn't occur at slave, but detected)
- **Burst mismatch:** W beats don't match AWLEN+1
- **ID corruption:** BID doesn't match tracked AWID
- **WSTRB protocol violations:** Invalid byte lane enables

### Performance Considerations

**Backend Latency Monitoring:**
- Tracks AW → B response latency
- Includes W channel completion time
- Configurable timeout threshold
- Separate from master-side latency

**Typical Timeout Values:**
- SRAM backend: 100-500 cycles
- DDR controller: 1000-5000 cycles
- Flash/EEPROM: 10000+ cycles (write operations)
- PCIe/external: 10000+ cycles

**Write-Specific Timing:**
- AW-W ordering flexible in AXI4
- Backend may wait for WLAST before responding
- B response latency includes W channel completion

### Buffer Depth Guidelines

Same as [axi4_slave_wr](axi4_slave_wr.md):
- **SKID_DEPTH_AW:** 2 (default) - handles interconnect backpressure
- **SKID_DEPTH_W:** 4 (default) - buffers burst write data
- **SKID_DEPTH_B:** 2 (default) - write responses are single-beat
- Increase for high-latency backends or large bursts

### Write Transaction Characteristics

**Burst Write Monitoring:**
- Monitors AW channel for address capture
- Tracks W channel beats until WLAST
- Correlates B channel response with AWID
- Validates burst length (W beats == AWLEN+1)
- Checks WSTRB validity per beat

**Performance Impact:**
- Write bursts more efficient than single writes
- Backend may buffer/pipeline write data
- B response can occur before W completion (with reordering)
- Monitor packets generated per transaction, not per beat

---

## Related Modules

### Companion Monitors
- **[axi4_master_rd_mon](axi4_master_rd_mon.md)** - AXI4 master read with monitoring
- **[axi4_master_wr_mon](axi4_master_wr_mon.md)** - AXI4 master write with monitoring
- **[axi4_slave_rd_mon](axi4_slave_rd_mon.md)** - AXI4 slave read with monitoring

### Base Modules
- **[axi4_slave_wr](axi4_slave_wr.md)** - Functional AXI4 slave write (without monitoring)
- **axi_monitor_filtered** - Monitoring engine with filtering (shared/)

### Used Components
- **[gaxi_skid_buffer](../gaxi/gaxi_skid_buffer.md)** - Elastic buffering
- **axi_monitor_base** - Core monitoring logic (shared/)
- **axi_monitor_trans_mgr** - Transaction tracking (shared/)

---

## References

### Specifications
- ARM IHI 0022E: AMBA AXI Protocol Specification (AXI4)
- Monitor Bus Packet Format: [monitor_package_spec.md](../includes/monitor_package_spec.md)

### Source Code
- RTL: `rtl/amba/monitor/axi4_slave_wr_mon.sv`
- Tests: `val/amba/test_axi4_slave_wr_mon.py`
- Framework: `bin/TBClasses/components/axi4/`

### Documentation
- Configuration Guide: [AXI Monitor Base](axi_monitor_base.md)
- Architecture: [RTLAmba Overview](../overview.md)
- AXI4 Index: [README.md](README.md)

---

**Last Updated:** 2026-07-18

---

## Navigation

- **[← Back to AXI4 Index](README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
