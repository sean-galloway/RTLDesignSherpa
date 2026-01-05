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

# AXI Monitor Transaction Manager

**Module:** `axi_monitor_trans_mgr.sv`
**Location:** `rtl/amba/shared/`
**Category:** Core Infrastructure
**Status:** ✅ Production Ready

---

## Overview

The `axi_monitor_trans_mgr` module provides Transaction table management for ID-based tracking.

This is a **shared infrastructure module** used internally by AXI/AXIL monitors. It is not typically instantiated directly by users but is critical for understanding the monitor architecture.

---

## Key Features

- ✅ **Transaction table with configurable depth:** Transaction table with configurable depth
- ✅ **ID-based transaction lookup and matching:** ID-based transaction lookup and matching
- ✅ **Out-of-order transaction support:** Out-of-order transaction support
- ✅ **Beat counting for burst transactions:** Beat counting for burst transactions
- ✅ **Transaction start/end event generation:** Transaction start/end event generation
- ✅ **Table exhaustion detection and reporting:** Table exhaustion detection and reporting
- ✅ **Latency calculation per transaction:** Latency calculation per transaction

---

## Module Purpose

The `axi_monitor_trans_mgr` module is the core building block for:

1. **ID-Based Tracking:** Maps transaction IDs to table entries
2. **Burst Handling:** Tracks multi-beat transactions with beat counters
3. **Latency Calculation:** Measures time from command to completion
4. **Out-of-Order Support:** Handles responses in any order
5. **Table Management:** Allocates and deallocates entries dynamically

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `MAX_TRANSACTIONS` | int | 16 | Transaction table depth |
| `ID_WIDTH` | int | 8 | Transaction ID width |
| `ADDR_WIDTH` | int | 32 | Address width for tracking |

---

## Port Groups

**See RTL source:** `rtl/amba/shared/axi_monitor_trans_mgr.sv` for complete port listing.

Key interface groups:
- Clock and reset
- Input signals from monitored interface
- Configuration signals
- Output signals to downstream logic

---

## Architecture

```
     cmd_valid/cmd_id
            │
            ▼
    ┌──────────────┐
    │ ID Lookup    │──► Table Index
    └──────────────┘
            │
            ▼
    ┌──────────────┐
    │ Transaction  │
    │   Table      │
    │ [0..MAX-1]   │
    └──────────────┘
            │
            ▼
    ┌──────────────┐
    │ Beat Counter │──► Transaction Complete
    │ & Latency    │
    └──────────────┘
```

The transaction table stores:
- Transaction ID
- Start address
- Beat count
- Timestamp
- Status flags

---

## Usage in Monitor System

This module is used by:

- **axi_monitor_base**

### Internal Integration

This module is instantiated automatically within higher-level monitor modules. Users configure behavior through top-level monitor parameters.

---

## Configuration Guidelines

**See individual monitor documentation for configuration examples.**

Configuration is typically handled at the top-level monitor instantiation.

---

## Performance Characteristics

| Metric | Value | Notes |
|--------|-------|-------|
| Latency | 1-2 cycles | Typical processing delay |
| Throughput | 1 operation/cycle | Maximum rate |
| Resource Usage | Varies | Depends on configuration |

---

## Verification Considerations

### Test Coverage

- Functional correctness of core logic
- Boundary conditions (min/max values)
- Error handling and recovery
- Interface protocol compliance

**See:** `val/amba/test_axi_monitor_trans_mgr.py` for verification tests

---

## Related Modules

- **[axi_monitor_base](./axi_monitor_base.md)**

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
