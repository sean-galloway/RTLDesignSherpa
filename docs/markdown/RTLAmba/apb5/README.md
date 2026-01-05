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

# APB5 (Advanced Peripheral Bus - AMBA 5) Modules

**Location:** `rtl/amba/apb5/`
**Test Location:** `val/amba/`
**Status:** Production Ready

---

## Overview

The APB5 subsystem provides a complete implementation of the ARM AMBA 5 APB (Advanced Peripheral Bus) protocol, including masters, slaves, monitors, clock domain crossing, and testbench utilities.

APB5 extends APB4 with enhanced features for modern SoC designs while maintaining backward compatibility. The simple two-cycle handshake protocol is preserved, with additional signals for improved security, wake-up signaling, and error handling.

---

## AMBA4 vs AMBA5 Comparison

| Feature | APB4 | APB5 |
|---------|------|------|
| Basic Protocol | Two-phase handshake | Two-phase handshake |
| Protection | PPROT[2:0] | PPROT[2:0] + PNSE |
| Wake-up | Not supported | PWAKEUP signal |
| User Signals | Not supported | PAUSER, PWUSER, PRUSER, PBUSER |
| Atomic Operations | Not supported | PEXCL, PEXOKAY |
| Error Response | PSLVERR | PSLVERR (enhanced semantics) |

---

## Module Categories

### Core Protocol Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb5_master** | Full-featured APB5 master with command/response interface | [apb5_master.md](apb5_master.md) | Documented |
| **apb5_slave** | Complete APB5 slave with buffered cmd/rsp interface | [apb5_slave.md](apb5_slave.md) | Documented |
| **apb5_slave_cdc** | APB5 slave with clock domain crossing support | [apb5_slave_cdc.md](apb5_slave_cdc.md) | Documented |
| **apb5_monitor** | Transaction monitoring with 64-bit monitor bus output | [apb5_monitor.md](apb5_monitor.md) | Documented |

### Clock-Gated Variants

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb5_master_cg** | APB5 master with integrated clock gating | [apb5_master_cg.md](apb5_master_cg.md) | Documented |
| **apb5_slave_cg** | APB5 slave with integrated clock gating | [apb5_slave_cg.md](apb5_slave_cg.md) | Documented |
| **apb5_slave_cdc_cg** | APB5 slave CDC with integrated clock gating | [apb5_slave_cdc_cg.md](apb5_slave_cdc_cg.md) | Documented |

### Testbench Utilities

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb5_master_stub** | Lightweight APB5 master for testbench integration | [apb5_master_stub.md](apb5_master_stub.md) | Documented |
| **apb5_slave_stub** | Lightweight APB5 slave for testbench integration | [apb5_slave_stub.md](apb5_slave_stub.md) | Documented |

---

## Key Features

### APB5 Protocol Support
- **Full APB5 Compliance:** Complete AMBA 5 APB protocol implementation
- **PSTRB Support:** Byte-lane strobes for partial writes
- **PPROT Support:** Protection attributes for security-aware systems
- **PNSE Support:** Non-secure extension for TrustZone integration
- **PWAKEUP Support:** Low-power wake-up signaling
- **User Signals:** PAUSER, PWUSER, PRUSER, PBUSER for sideband data

### Clock Domain Crossing
- **Dual-Clock Operation:** APB (pclk) and backend (aclk) domains
- **Safe CDC:** Proper handshake-based clock domain crossing
- **Independent Frequencies:** Backend can run faster or slower than APB

### Power Management
- **Clock Gating:** Per-module clock gating for power reduction
- **Wake-up Signaling:** PWAKEUP for low-power state exit
- **Idle Detection:** Automatic clock gate when bus is idle

### Monitoring and Debug
- **Transaction Monitoring:** Real-time protocol monitoring
- **64-bit Monitor Bus:** Standardized packet format
- **Error Detection:** Protocol violations, timeout detection
- **Performance Tracking:** Transaction counting, latency measurement

---

## Quick Start

### Using APB5 Master

```systemverilog
apb5_master #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .DEPTH(2)
) u_apb5_master (
    .aclk           (clk),
    .aresetn        (resetn),

    // Command interface
    .cmd_valid      (cmd_valid),
    .cmd_ready      (cmd_ready),
    .cmd_pwrite     (cmd_pwrite),
    .cmd_paddr      (cmd_paddr),
    .cmd_pwdata     (cmd_pwdata),
    .cmd_pstrb      (cmd_pstrb),
    .cmd_pprot      (cmd_pprot),

    // Response interface
    .rsp_valid      (rsp_valid),
    .rsp_ready      (rsp_ready),
    .rsp_prdata     (rsp_prdata),
    .rsp_pslverr    (rsp_pslverr),

    // APB5 master interface
    .m_apb_PSEL     (psel),
    .m_apb_PENABLE  (penable),
    .m_apb_PREADY   (pready),
    .m_apb_PADDR    (paddr),
    .m_apb_PWRITE   (pwrite),
    .m_apb_PWDATA   (pwdata),
    .m_apb_PSTRB    (pstrb),
    .m_apb_PPROT    (pprot),
    .m_apb_PRDATA   (prdata),
    .m_apb_PSLVERR  (pslverr),
    .m_apb_PWAKEUP  (pwakeup)
);
```

### Using APB5 Slave

```systemverilog
apb5_slave #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .DEPTH(2)
) u_apb5_slave (
    .aclk           (clk),
    .aresetn        (resetn),

    // APB5 slave interface
    .s_apb_PSEL     (psel),
    .s_apb_PENABLE  (penable),
    .s_apb_PREADY   (pready),
    .s_apb_PADDR    (paddr),
    .s_apb_PWRITE   (pwrite),
    .s_apb_PWDATA   (pwdata),
    .s_apb_PSTRB    (pstrb),
    .s_apb_PPROT    (pprot),
    .s_apb_PRDATA   (prdata),
    .s_apb_PSLVERR  (pslverr),
    .s_apb_PWAKEUP  (pwakeup),

    // Command interface
    .cmd_valid      (cmd_valid),
    .cmd_ready      (cmd_ready),
    .cmd_pwrite     (cmd_pwrite),
    .cmd_paddr      (cmd_paddr),
    .cmd_pwdata     (cmd_pwdata),
    .cmd_pstrb      (cmd_pstrb),

    // Response interface
    .rsp_valid      (rsp_valid),
    .rsp_ready      (rsp_ready),
    .rsp_prdata     (rsp_prdata),
    .rsp_pslverr    (rsp_pslverr)
);
```

---

## Testing

All APB5 modules are verified using CocoTB-based testbenches located in `val/amba/`:

```bash
# Run all APB5 tests
pytest val/amba/test_apb5*.py -v

# Run specific module tests
pytest val/amba/test_apb5_master.py -v
pytest val/amba/test_apb5_slave.py -v
pytest val/amba/test_apb5_slave_cdc.py -v
pytest val/amba/test_apb5_monitor.py -v
```

---

## Protocol Details

### APB5 Transfer Phases

APB5 uses the same two-phase protocol as APB4:

1. **SETUP Phase:** PSEL asserted, PENABLE low
   - Master presents address, control signals, and write data (if write)
   - Slave prepares for transfer

2. **ACCESS Phase:** PSEL and PENABLE both asserted
   - Slave completes transfer and asserts PREADY when ready
   - For reads, slave presents PRDATA
   - Slave may assert PSLVERR to signal error

### APB5 Signal Descriptions

| Signal | Direction | Description |
|--------|-----------|-------------|
| PCLK | Input | APB clock |
| PRESETn | Input | Active-low reset |
| PSEL | Master to Slave | Slave select |
| PENABLE | Master to Slave | Enable (ACCESS phase indicator) |
| PREADY | Slave to Master | Transfer complete |
| PADDR | Master to Slave | Address bus |
| PWRITE | Master to Slave | Write enable (1=write, 0=read) |
| PWDATA | Master to Slave | Write data |
| PSTRB | Master to Slave | Byte lane strobes |
| PPROT | Master to Slave | Protection attributes |
| PNSE | Master to Slave | Non-secure extension (APB5) |
| PWAKEUP | Master to Slave | Wake-up signal (APB5) |
| PAUSER | Master to Slave | Address phase user signal (APB5) |
| PWUSER | Master to Slave | Write data user signal (APB5) |
| PRDATA | Slave to Master | Read data |
| PSLVERR | Slave to Master | Error response |
| PRUSER | Slave to Master | Read data user signal (APB5) |
| PBUSER | Slave to Master | Write response user signal (APB5) |

---

## Design Notes

### Command/Response Architecture

All APB5 modules use a command/response interface pattern for backend integration, identical to the APB4 architecture:

**Command Interface:**
- `cmd_valid`, `cmd_ready` - Handshake signals
- `cmd_pwrite` - Write/read direction
- `cmd_paddr` - Transaction address
- `cmd_pwdata` - Write data
- `cmd_pstrb` - Byte strobes
- `cmd_pprot` - Protection attributes

**Response Interface:**
- `rsp_valid`, `rsp_ready` - Handshake signals
- `rsp_prdata` - Read data
- `rsp_pslverr` - Error flag

### Migration from APB4

APB5 modules are backward compatible with APB4 systems:
- Connect APB5 signals to APB4 equivalents
- Tie unused APB5 signals (PNSE, PWAKEUP, user signals) to default values
- PNSE typically tied to 0 for secure mode
- PWAKEUP typically tied to 0 for always-awake operation

---

## Related Documentation

- **[APB4 Modules](../apb/README.md)** - APB4 protocol components
- **[AXI5 Modules](../axi5/README.md)** - AXI5 protocol components
- **[AXIS5 Modules](../axis5/README.md)** - AXI5-Stream components
- **[GAXI Modules](../gaxi/README.md)** - Generic AXI utilities

---

## References

### Specifications
- ARM AMBA 5 APB Protocol Specification
- ARM AMBA APB Protocol Specification v2.0 (APB4)

### Source Code
- RTL: `rtl/amba/apb5/`
- Tests: `val/amba/test_apb5*.py`
- Framework: `bin/CocoTBFramework/components/apb/`

---

**Last Updated:** 2025-12-26

---

## Navigation

- **[Back to RTLAmba Index](../index.md)**
- **[Back to Main Documentation Index](../../index.md)**
