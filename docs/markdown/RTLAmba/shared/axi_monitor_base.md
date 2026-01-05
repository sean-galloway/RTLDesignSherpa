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

# AXI Monitor Base

**Module:** `axi_monitor_base.sv`
**Location:** `rtl/amba/shared/`
**Category:** Core Infrastructure
**Status:** ✅ Production Ready

---

## Overview

The `axi_monitor_base` module provides Core transaction tracking and event reporting for AXI/AXIL monitors.

This is a **shared infrastructure module** used internally by AXI/AXIL monitors. It is not typically instantiated directly by users but is critical for understanding the monitor architecture.

---

## Key Features

- ✅ **Transaction-based tracking for AXI and AXI-Lite protocols:** Transaction-based tracking for AXI and AXI-Lite protocols
- ✅ **Out-of-order transaction handling with ID-based tracking:** Out-of-order transaction handling with ID-based tracking
- ✅ **Data-before-address support (slave-side scenarios):** Data-before-address support (slave-side scenarios)
- ✅ **64-bit standardized monitor bus packet output:** 64-bit standardized monitor bus packet output
- ✅ **Configurable performance metrics tracking:** Configurable performance metrics tracking
- ✅ **Timeout detection and threshold monitoring:** Timeout detection and threshold monitoring
- ✅ **Debug trace support with verbosity levels:** Debug trace support with verbosity levels

---

## Module Purpose

The `axi_monitor_base` module is the core building block for:

1. **Transaction Tracking:** Maintains state for all outstanding AXI/AXIL transactions
2. **Event Detection:** Identifies protocol errors, timeouts, threshold violations
3. **Packet Generation:** Creates standardized 64-bit monitor bus packets
4. **Flow Control:** Manages backpressure and transaction table exhaustion
5. **Performance Metrics:** Optional latency and throughput tracking

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `UNIT_ID` | int | 9 | 4-bit unit identifier for packet routing |
| `AGENT_ID` | int | 99 | 8-bit agent identifier for packet routing |
| `MAX_TRANSACTIONS` | int | 16 | Maximum outstanding transactions |
| `ADDR_WIDTH` | int | 32 | Address bus width |
| `ID_WIDTH` | int | 8 | Transaction ID width (0 for AXIL) |
| `IS_READ` | int | 1 | 1=read monitor, 0=write monitor |
| `IS_AXI` | int | 1 | 1=AXI protocol, 0=AXI-Lite |
| `ENABLE_PERF_PACKETS` | int | 0 | Enable performance metrics |
| `ENABLE_DEBUG_MODULE` | int | 0 | Enable debug tracing |

---

## Port Groups

### Command Phase Interface (AW/AR)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cmd_addr` | Input | ADDR_WIDTH | Command address value |
| `cmd_id` | Input | ID_WIDTH | Transaction ID |
| `cmd_len` | Input | 8 | Burst length (AXI only) |
| `cmd_size` | Input | 3 | Burst size (AXI only) |
| `cmd_burst` | Input | 2 | Burst type (AXI only) |
| `cmd_valid` | Input | 1 | Command valid |
| `cmd_ready` | Input | 1 | Command ready |

### Data Channel Interface (R/W)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `data_id` | Input | ID_WIDTH | Data transaction ID |
| `data_last` | Input | 1 | Last data beat indicator |
| `data_resp` | Input | 2 | Response code (OKAY/EXOKAY/SLVERR/DECERR) |
| `data_valid` | Input | 1 | Data valid |
| `data_ready` | Input | 1 | Data ready |

### Response Channel Interface (B)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `resp_id` | Input | ID_WIDTH | Response transaction ID |
| `resp_code` | Input | 2 | Response code |
| `resp_valid` | Input | 1 | Response valid |
| `resp_ready` | Input | 1 | Response ready |

### Configuration Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_freq_sel` | Input | 4 | Frequency selection for timeout scaling |
| `cfg_addr_cnt` | Input | 4 | Address phase timeout count |
| `cfg_data_cnt` | Input | 4 | Data phase timeout count |
| `cfg_resp_cnt` | Input | 4 | Response phase timeout count |
| `cfg_error_enable` | Input | 1 | Enable error event packets |
| `cfg_compl_enable` | Input | 1 | Enable completion packets |
| `cfg_threshold_enable` | Input | 1 | Enable threshold packets |
| `cfg_timeout_enable` | Input | 1 | Enable timeout packets |
| `cfg_perf_enable` | Input | 1 | Enable performance packets |
| `cfg_debug_enable` | Input | 1 | Enable debug packets |

### Monitor Bus Output

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `monbus_valid` | Output | 1 | Monitor packet valid |
| `monbus_ready` | Input | 1 | Monitor packet ready (from downstream) |
| `monbus_packet` | Output | 64 | Standardized monitor packet |
| `block_ready` | Output | 1 | Flow control signal |
| `busy` | Output | 1 | Monitor is busy indicator |
| `active_count` | Output | 8 | Number of active transactions |

---

## Architecture

```
  Command     Data      Response
  Channel    Channel    Channel
     │          │          │
     ▼          ▼          ▼
┌────────────────────────────────┐
│  Transaction Manager           │
│  - ID-based tracking           │
│  - Beat counting               │
│  - Latency calculation         │
└──────────┬─────────────────────┘
           │
┌──────────▼─────────────────────┐
│  Timeout Monitor               │
│  - Per-phase timeouts          │
│  - Configurable thresholds     │
└──────────┬─────────────────────┘
           │
┌──────────▼─────────────────────┐
│  Reporter                      │
│  - Packet formatting           │
│  - Event queuing               │
└──────────┬─────────────────────┘
           │
           ▼
      Monitor Bus
        (64-bit)
```

The module coordinates four sub-components:
1. **Transaction Manager:** Tracks transactions, manages table
2. **Timeout Monitor:** Detects stuck transactions
3. **Performance Tracker:** Optional latency/throughput metrics
4. **Reporter:** Generates standardized packets

---

## Usage in Monitor System

This module is used by:

- **axi4_master_rd_mon**
- **axi4_master_wr_mon**
- **axi4_slave_rd_mon**
- **axi4_slave_wr_mon**
- **axil4_master_rd_mon**
- **axil4_master_wr_mon**
- **axil4_slave_rd_mon**
- **axil4_slave_wr_mon**

### Integration Example

**Not typically instantiated directly by users.** Instead, use high-level monitors:

```systemverilog
// User instantiates this:
axi4_master_rd_mon #(...) u_mon (...);

// Which internally uses:
// - axi4_master_rd (frontend)
// - axi_monitor_base (this module)
// - axi_monitor_filtered
```

---

## Configuration Guidelines

### Transaction Table Sizing

| Design Scenario | MAX_TRANSACTIONS | Rationale |
|----------------|------------------|-----------|
| AXI4 Master (Burst) | 16-32 | Support multiple outstanding bursts |
| AXI4 Slave (Burst) | 16-32 | Handle out-of-order responses |
| AXI4-Lite Master | 4-8 | Single-beat, limited concurrency |
| AXI4-Lite Slave | 4-8 | Simple protocol, fewer outstanding |

### Timeout Configuration

- **`cfg_addr_cnt`**: Command phase timeout (AR/AW)
- **`cfg_data_cnt`**: Data phase timeout (R/W)
- **`cfg_resp_cnt`**: Response phase timeout (B)

**Typical values:**
- Burst traffic: `cfg_*_cnt = 4-8` (aggressive timeout)
- Memory controllers: `cfg_*_cnt = 10-15` (allow latency)
- External interfaces: `cfg_*_cnt = 15` (max tolerance)

---

## Performance Characteristics

| Metric | Value | Notes |
|--------|-------|-------|
| Latency | 2-3 cycles | Event detection to packet output |
| Throughput | 1 packet/cycle | Maximum packet generation rate |
| Table Lookup | 1 cycle | ID-based transaction lookup |
| Resource Usage | ~500 LUTs | Depends on MAX_TRANSACTIONS |

---

## Verification Considerations

### Key Test Scenarios

1. **Transaction Table Management:**
   - Fill table to MAX_TRANSACTIONS
   - Verify table exhaustion handling
   - Test ID reuse after completion

2. **Out-of-Order Transactions:**
   - Issue multiple transactions with different IDs
   - Complete in random order
   - Verify correct ID matching

3. **Timeout Detection:**
   - Initiate transaction without completion
   - Verify timeout event at configured threshold
   - Check timeout packet contains correct ID

4. **Performance Metrics:**
   - Enable `ENABLE_PERF_PACKETS`
   - Verify latency calculations
   - Check throughput tracking

---

## Related Modules

- **[axi_monitor_filtered](./axi_monitor_filtered.md)**
- **[axi_monitor_trans_mgr](./axi_monitor_trans_mgr.md)**
- **[axi_monitor_reporter](./axi_monitor_reporter.md)**
- **[axi_monitor_timeout](./axi_monitor_timeout.md)**

---

## See Also

- **Monitor Architecture:** `docs/markdown/RTLAmba/overview.md`
- **Monitor Configuration Guide:** `docs/AXI_Monitor_Configuration_Guide.md`
- **Packet Format Specification:** `docs/markdown/RTLAmba/includes/monitor_package_spec.md`

---

## Navigation

- **[← Back to Shared Infrastructure Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
