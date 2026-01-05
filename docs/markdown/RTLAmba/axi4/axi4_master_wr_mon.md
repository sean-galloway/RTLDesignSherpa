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

# AXI4 Master Write Monitor

**Module:** `axi4_master_wr_mon.sv`
**Location:** `rtl/amba/axi4/`
**Status:** ✅ Production Ready

---

## Overview

The AXI4 Master Write Monitor module combines a functional AXI4 master write interface with comprehensive transaction monitoring and filtering capabilities. This module is essential for verification environments, providing real-time protocol checking, error detection, performance metrics, and configurable packet filtering for write transactions.

### Key Features

- ✅ **Integrated Monitoring:** Combines `axi4_master_wr` with `axi_monitor_filtered`
- ✅ **3-Level Filtering:** Packet type masks, error routing, individual event masking
- ✅ **Error Detection:** Protocol violations, SLVERR, DECERR, orphan transactions
- ✅ **Timeout Monitoring:** Configurable timeout detection for stuck transactions
- ✅ **Performance Metrics:** Latency tracking, transaction counting, throughput analysis
- ✅ **Monitor Bus Output:** 64-bit standardized packets for system-level monitoring
- ✅ **Configuration Validation:** Detects conflicting configuration settings
- ✅ **Clock Gating Support:** Busy signal for power management

---

## Module Architecture

```mermaid
flowchart LR
    subgraph FE["Frontend<br/>(fub_axi)"]
        aw["aw* →"]
        w["w* →"]
        b["← b*"]
    end

    subgraph CORE["Master Core"]
        mc["axi4_master_wr<br/>(buffered)"]
    end

    subgraph MON["Monitor"]
        mf["axi_monitor<br/>_filtered"]
        features["•error<br/>•timeout<br/>•perf"]
    end

    subgraph MB["Monitor Bus"]
        mbv["monbus_valid"]
        mbp["monbus_packet"]
    end

    aw --> mc
    w --> mc
    mc --> b
    mc --> mf
    mf --> mbv
    mf --> mbp
    mc --> maxi["Master (m_axi)"]
```

The module instantiates two sub-modules:
1. **axi4_master_wr** - Core AXI4 write functionality with buffering
2. **axi_monitor_filtered** - Transaction monitoring with 3-level filtering

---

## Parameters

### AXI4 Master Parameters

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
| `UNIT_ID` | int | 1 | 4-bit unit identifier in monitor packets |
| `AGENT_ID` | int | 11 | 8-bit agent identifier in monitor packets |
| `MAX_TRANSACTIONS` | int | 16 | Maximum concurrent outstanding transactions |
| `ENABLE_FILTERING` | bit | 1 | Enable packet filtering (0=pass all packets) |
| `ADD_PIPELINE_STAGE` | bit | 0 | Add register stage for timing closure |

---

## Port Groups

### AXI4 Write Channels

**Frontend Interface (fub_axi_*):**
- AW channel: `awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid, awready`
- W channel: `wdata, wstrb, wlast, wuser, wvalid, wready`
- B channel: `bid, bresp, buser, bvalid, bready`

**Master Interface (m_axi_*):**
- Same signals as frontend, mirrored direction

### Monitor Configuration

Configuration ports are identical to [axi4_master_rd_mon](axi4_master_rd_mon.md):
- Basic: `cfg_monitor_enable`, `cfg_error_enable`, `cfg_timeout_enable`, `cfg_perf_enable`
- Thresholds: `cfg_timeout_cycles`, `cfg_latency_threshold`
- Filtering: 7 mask signals (`cfg_axi_*_mask`)

### Monitor Bus Output

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `monbus_valid` | Output | 1 | Monitor packet valid |
| `monbus_ready` | Input | 1 | Downstream ready to accept packet |
| `monbus_packet` | Output | 64 | Monitor packet data |

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

Identical 64-bit format as [axi4_master_rd_mon](axi4_master_rd_mon.md):

```
Bits [63:60] - Packet Type (ERROR, COMPL, TIMEOUT, THRESH, PERF, ADDR, DEBUG)
Bits [59:57] - Protocol: 0x0 (AXI)
Bits [56:53] - Event Code
Bits [52:47] - Channel ID
Bits [46:43] - Unit ID
Bits [42:35] - Agent ID
Bits [34:0]  - Event Data
```

---

## Timing Diagrams

The following waveforms show AXI4 master write monitor behavior:

### Scenario 1: Single-Beat Write Transaction

Complete AXI4 write transaction showing AW, W, and B channels:

![Single Beat Write](../../assets/WAVES/axi4_master_wr_mon/single_beat_write_001.png)

**WaveJSON:** [single_beat_write_001.json](../../assets/WAVES/axi4_master_wr_mon/single_beat_write_001.json)

**Key Observations:**
- AW channel handshake (AWVALID/AWREADY)
- W channel data (WVALID/WREADY/WLAST/WSTRB)
- B channel response (BVALID/BREADY/BRESP)
- Monitor bus packet generation
- Three-channel write protocol coordination

### Scenario 2: Alternative Single-Beat Write

Variant single-beat write with different backpressure pattern:

![Single Beat Write Alt](../../assets/WAVES/axi4_master_wr_mon/single_beat_write_002_001.png)

**WaveJSON:** [single_beat_write_002_001.json](../../assets/WAVES/axi4_master_wr_mon/single_beat_write_002_001.json)

**Key Observations:**
- Different ready signal timing
- Channel interleaving effects
- Write strobe (WSTRB) handling
- Response latency variation
- Monitor packet correlation with transaction ID

---

## Configuration Strategies

### Strategy 1: Functional Verification (Recommended)

**Goal:** Catch write errors and track completion

```systemverilog
// Enable configuration
.cfg_monitor_enable     (1'b1),
.cfg_error_enable       (1'b1),      // Catch SLVERR/DECERR
.cfg_timeout_enable     (1'b1),      // Detect stuck writes
.cfg_perf_enable        (1'b0),      // Disable (reduces traffic)

// Filtering - pass error and timeout only
.cfg_axi_pkt_mask       (16'b1111_1111_0000_0011),
.cfg_axi_error_mask     (16'h0000),  // Pass all errors
.cfg_axi_timeout_mask   (16'h0000),  // Pass all timeouts
.cfg_axi_compl_mask     (16'hFFFF),  // Drop completions
.cfg_axi_perf_mask      (16'hFFFF),  // Drop performance

// Timeouts
.cfg_timeout_cycles     (16'd1000),
.cfg_latency_threshold  (32'd500)
```

### Strategy 2: Performance Analysis

**Goal:** Collect write performance metrics

```systemverilog
// Enable configuration
.cfg_monitor_enable     (1'b1),
.cfg_error_enable       (1'b1),      // Still catch errors
.cfg_timeout_enable     (1'b0),      // Disable timeouts
.cfg_perf_enable        (1'b1),      // Enable performance

// Filtering - pass error and performance only
.cfg_axi_pkt_mask       (16'b1111_1110_0000_0001),
.cfg_axi_error_mask     (16'h0000),  // Pass all errors
.cfg_axi_perf_mask      (16'h0000),  // Pass all performance
.cfg_axi_compl_mask     (16'hFFFF),  // Drop completions
.cfg_axi_timeout_mask   (16'hFFFF)   // Drop timeouts
```

### Strategy 3: Debug Mode

**Goal:** Maximum visibility for write transactions

```systemverilog
// Enable everything
.cfg_monitor_enable     (1'b1),
.cfg_error_enable       (1'b1),
.cfg_timeout_enable     (1'b1),
.cfg_perf_enable        (1'b1),

// Filtering - pass all packets
.cfg_axi_pkt_mask       (16'h0000),  // Pass all
// All individual masks set to 16'h0000
```

**⚠️ WARNING:** Never enable all packet types in high-throughput write scenarios!

---

## Usage Example

### Basic Integration

```systemverilog
axi4_master_wr_mon #(
    .SKID_DEPTH_AW      (2),
    .SKID_DEPTH_W       (4),
    .SKID_DEPTH_B       (2),
    .AXI_ID_WIDTH       (4),
    .AXI_ADDR_WIDTH     (32),
    .AXI_DATA_WIDTH     (64),
    .AXI_USER_WIDTH     (1),
    .UNIT_ID            (1),
    .AGENT_ID           (11),
    .MAX_TRANSACTIONS   (16),
    .ENABLE_FILTERING   (1)
) u_master_wr_mon (
    .aclk               (axi_aclk),
    .aresetn            (axi_aresetn),

    // Frontend interface (from write initiator)
    .fub_axi_awid       (write_awid),
    .fub_axi_awaddr     (write_awaddr),
    // ... rest of AW/W/B signals

    // Master interface (to interconnect)
    .m_axi_awid         (m_axi_awid),
    .m_axi_awaddr       (m_axi_awaddr),
    // ... rest of AW/W/B signals

    // Monitor configuration (Strategy 1 - Functional)
    .cfg_monitor_enable     (1'b1),
    .cfg_error_enable       (1'b1),
    .cfg_timeout_enable     (1'b1),
    .cfg_perf_enable        (1'b0),
    .cfg_timeout_cycles     (16'd1000),
    .cfg_latency_threshold  (32'd500),

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
    .busy                   (wr_busy),
    .active_transactions    (wr_active),
    .error_count            (wr_errors),
    .transaction_count      (wr_count),
    .cfg_conflict_error     (cfg_conflict)
);
```

---

## Design Notes

### Write-Specific Monitoring

**Write Response Tracking:**
- Monitors AW channel for write address capture
- Tracks W channel beats (WLAST detection)
- Correlates B channel responses with AWID
- Detects mismatched burst lengths (W beats vs AWLEN+1)

**Common Write Errors Detected:**
- **SLVERR:** Slave error response (decode failure, access violation)
- **DECERR:** Decode error (address not mapped)
- **Orphan transactions:** AWID without matching BID
- **Timeout:** Write address or response stuck beyond threshold
- **Protocol violations:** Invalid WSTRB, missing WLAST

### Performance Considerations

**Write Transaction Bandwidth:**
- AW channel: 1 transaction/cycle (when buffer not full)
- W channel: 1 beat/cycle sustained (burst pipelining)
- B channel: 1 response/cycle (sparse compared to W beats)

**Monitor Packet Budget (Write):**
- Typical: 2-3 packets per write transaction
- Burst writes: More efficient packet/beat ratio
- Single writes: Higher packet overhead

### Buffer Depth Guidelines

Same as [axi4_master_wr](axi4_master_wr.md):
- **SKID_DEPTH_AW:** 2 (default) - sufficient for most systems
- **SKID_DEPTH_W:** 4 (default) - accommodates moderate bursts
- **SKID_DEPTH_B:** 2 (default) - responses are single-beat

Increase depths for high-latency or high-throughput scenarios.

---

## Related Modules

### Companion Monitors
- **[axi4_master_rd_mon](axi4_master_rd_mon.md)** - AXI4 master read with monitoring
- **axi4_slave_rd_mon** - AXI4 slave read with monitoring
- **axi4_slave_wr_mon** - AXI4 slave write with monitoring

### Base Modules
- **[axi4_master_wr](axi4_master_wr.md)** - Functional AXI4 master write (without monitoring)
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
- RTL: `rtl/amba/axi4/axi4_master_wr_mon.sv`
- Tests: `val/amba/test_axi4_master_wr_mon.py`
- Framework: `bin/CocoTBFramework/components/axi4/`

### Documentation
- Configuration Guide: [AXI_Monitor_Configuration_Guide.md](../../AXI_Monitor_Configuration_Guide.md)
- Architecture: [RTLAmba Overview](../overview.md)
- AXI4 Index: [README.md](README.md)

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to AXI4 Index](README.md)**
- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**
