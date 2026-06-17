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

# AXI Monitor Filtered

**Module:** `axi_monitor_filtered.sv`
**Location:** `rtl/amba/shared/`
**Category:** Core Infrastructure
**Status:** ✅ Production Ready

---

## Overview

The `axi_monitor_filtered` module provides 3-level packet filtering for monitor bus traffic management.

This is a **shared infrastructure module** used internally by AXI/AXIL monitors. It is not typically instantiated directly by users but is critical for understanding the monitor architecture.

---

## Key Features

- ✅ **Level 1:** Packet type masks (error/completion/timeout/perf/debug)
- ✅ **Level 2:** Error routing priorities (critical vs informational)
- ✅ **Level 3:** Individual event masking (per-event granularity)
- ✅ **Configuration conflict detection and warnings:** Configuration conflict detection and warnings
- ✅ **Packet statistics and drop counters:** Packet statistics and drop counters
- ✅ **Bypass mode for full pass-through:** Bypass mode for full pass-through

---

## Module Purpose

The `axi_monitor_filtered` module is the core building block for:

1. **Traffic Management:** Reduces monitor bus congestion through intelligent filtering
2. **Prioritization:** Routes critical errors while filtering informational events
3. **Configuration Validation:** Detects conflicting filter settings
4. **Flexibility:** Supports per-packet-type and per-event granular control

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `UNIT_ID` / `AGENT_ID` | logic | `8'h01` / `16'h000A` | Identity bits stamped into emitted monitor packets. |
| `MAX_TRANSACTIONS` | int | 16 | Outstanding transaction table depth (passed to `axi_monitor_base` → `axi_monitor_trans_mgr`). |
| `ADDR_WIDTH` / `ID_WIDTH` | int | 32 / 8 | Address and AXI ID widths. |
| `IS_READ` / `IS_AXI` | bit | 1 / 1 | Direction (read vs write) and protocol family (AXI4 vs AXIL). |
| `ENABLE_PERF_PACKETS` | bit | 1 | Emit perf packets onto the monitor bus. |
| `ENABLE_DEBUG_MODULE` | bit | 0 | Instantiate the debug reporter sub-block. |
| **Reporter sub-block enables** | | | Each gates one of the six reporter sub-blocks (`axi_monitor_reporter_*`) at elaboration time. Pass-through to `axi_monitor_base`. |
| `ENABLE_ERROR_LOGIC` | bit | 1 | Error reporter (orphans, resp errors). |
| `ENABLE_TIMEOUT_LOGIC` | bit | 1 | Timeout reporter (addr/data/resp timers). |
| `ENABLE_COMPL_LOGIC` | bit | 1 | Completion reporter. |
| `ENABLE_THRESHOLD_LOGIC` | bit | 1 | Threshold reporter (latency / active-count thresholds). |
| `ENABLE_PERF_LOGIC` | bit | `ENABLE_PERF_PACKETS` | Perf reporter (the Stage B counters below). |
| `ENABLE_DEBUG_LOGIC` | bit | 0 | Debug reporter. |
| `ENABLE_FILTERING` | bit | 1 | Master enable for filtering. |
| `ADD_PIPELINE_STAGE` | bit | 0 | Add register stage for timing. |
| `N_ADDR_RANGES` | int | 0 | Number of address-range comparators in the [`axi_monitor_addr_check`](axi_monitor_addr_check.md) sub-block (0 = the comparator block is not synthesised at all). |

---

## Port Groups

### Monitor Bus Input

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `i_monbus_valid` | Input | 1 | Input packet valid |
| `i_monbus_ready` | Output | 1 | Input packet ready |
| `i_monbus_packet` | Input | 128 | Input `monitor_packet_t` |

### Monitor Bus Output

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `o_monbus_valid` | Output | 1 | Output packet valid |
| `o_monbus_ready` | Input | 1 | Output packet ready |
| `o_monbus_packet` | Output | 128 | Filtered `monitor_packet_t` |

### Reset and Synchronous Control

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `aclk` / `aresetn` | Input | 1 / 1 | Standard clock and active-low async reset. |
| `clear` | Input | 1 | **Synchronous clear** — passes through to `axi_monitor_base` → `axi_monitor_trans_mgr` to empty the transaction CAM and zero the active-count pipeline without `aresetn`. Pulse one cycle while idle. |

### Filter Configuration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_pkt_type_mask` | Input | 6 | Packet type enable mask (ERROR/COMPL/TIMEOUT/THRESH/PERF/DEBUG) |
| `cfg_error_routing` | Input | 4 | Error priority routing configuration |
| `cfg_event_mask` | Input | 16 | Individual event enable mask |

### Performance Window Control (Stage A of perfmon RFC)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_start_event_sel` | Input | 3 | Event selector that opens the perf window (e.g. command-handshake, first beat, software pulse). |
| `cfg_end_event_sel` | Input | 3 | Event selector that closes the perf window. |
| `cfg_start_trigger` | Input | 1 | Software-driven open pulse (combines with `cfg_start_event_sel`). |
| `cfg_end_trigger` | Input | 1 | Software-driven close pulse. |
| `cfg_window_force_close` | Input | 1 | Asynchronous emergency close (drops any in-flight perf totals). |
| `window_active` | Output | 1 | The perf window is currently open. |
| `window_cycles` | Output | 32 | Number of cycles the current window has been open. |

Tie `cfg_start_event_sel`/`cfg_end_event_sel` to `3'b111` and the
triggers + `cfg_window_force_close` to `1'b0` at instances that don't
use perfmon.

### Performance Counters (Stage B of perfmon RFC)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `perf_prod_cycles` | Output | 32 | Productive cycles (valid + ready both high). |
| `perf_bp_cycles` | Output | 32 | Back-pressure cycles (valid high, ready low). |
| `perf_starv_cycles` | Output | 32 | Starvation cycles (valid low, ready high). |
| `perf_idle_cycles` | Output | 32 | Idle cycles (both low). |
| `perf_beat_count` | Output | 32 | Beat handshakes accumulated this window. |
| `perf_byte_count` | Output | 64 | Bytes transferred this window (derived from `cmd_size`/`cmd_len`). |
| `perf_burst_count` | Output | 32 | Bursts (command handshakes) this window. |

These counters latch on each `window_active` open and freeze on close;
software reads them after the close edge.

---

## Architecture

```mermaid
flowchart TB
    in["Monitor Packets"] --> l1
    subgraph Cascade["Three-Level Filter Cascade"]
        l1["Level 1 Filter<br/>Packet Type Masks<br/>(ERROR/COMPL/etc.)"]
        l1 --> l2["Level 2 Filter<br/>Error Routing<br/>(Critical vs Info)"]
        l2 --> l3["Level 3 Filter<br/>Event Masking<br/>(Per-event control)"]
    end
    l3 --> out["Filtered Packets"]
```

Three-level filtering cascade provides maximum flexibility while minimizing resource usage.

---

## Usage in Monitor System

This module is used by:

- **axi4_master_rd_mon**
- **axi4_master_wr_mon**
- **axi4_slave_rd_mon**
- **axi4_slave_wr_mon**

### Internal Integration

This module is instantiated automatically within higher-level monitor modules. Users configure behavior through top-level monitor parameters.

---

## Configuration Guidelines

### Filter Strategy

**Functional Verification (Default):**
```systemverilog
.cfg_pkt_type_mask(6'b000111)  // ERROR + COMPL + TIMEOUT only
```

**Performance Analysis:**
```systemverilog
.cfg_pkt_type_mask(6'b010001)  // ERROR + PERF only
```

**Debug Mode:**
```systemverilog
.cfg_pkt_type_mask(6'b111111)  // All packet types
```

**Critical Errors Only:**
```systemverilog
.cfg_pkt_type_mask(6'b000001)  // ERROR packets only
.cfg_error_routing(4'b0001)     // Critical errors only
```

---

## Performance Characteristics

| Metric | Value | Notes |
|--------|-------|-------|
| Filtering Latency | 0-1 cycles | Combinatorial (0) or registered (1) |
| Throughput | 1 packet/cycle | No backpressure introduced |
| Resource Usage | ~100 LUTs | Minimal overhead |

---

## Verification Considerations

### Key Test Scenarios

1. **Filter Masking:**
   - Send all packet types
   - Configure masks to allow/block each type
   - Verify correct filtering behavior

2. **Configuration Conflicts:**
   - Set conflicting enables (e.g., `cfg_compl_enable=1` but type mask blocks completions)
   - Verify warning/error detection

3. **Packet Integrity:**
   - Verify filtered packets are not modified (only dropped or passed)
   - Check backpressure handling

---

## Related Modules

- **[axi_monitor_base](./axi_monitor_base.md)**

---

## See Also

- **Monitor Architecture:** `docs/markdown/RTLAmba/overview.md`
- **Monitor Configuration Guide:** [Monitor Base Configuration](./axi_monitor_base.md)
- **Packet Format Specification:** `docs/markdown/RTLAmba/includes/monitor_package_spec.md`

---

## Navigation

- **[← Back to Shared Infrastructure Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
