# APB (Advanced Peripheral Bus) Modules

**Location:** `rtl/amba/apb/`
**Test Location:** `val/amba/`
**Status:** ✅ Production Ready

---

## Overview

The APB subsystem provides a complete implementation of the ARM AMBA APB (Advanced Peripheral Bus) protocol, including masters, slaves, monitors, interconnect components, and testbench utilities.

APB is a simple, low-power peripheral bus designed for connecting low-bandwidth peripherals to a system bus. It uses a simple two-cycle handshake protocol with minimal control signals.

---

## Module Categories

### Core Protocol Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb_master** | Full-featured APB master with command/response interface | [apb_master.md](apb_master.md) | ✅ Documented |
| **apb_slave** | Complete APB slave with buffered cmd/rsp interface | [apb_slave.md](apb_slave.md) | ✅ Documented |
| **apb_slave_cdc** | APB slave with clock domain crossing support | [apb_slave_cdc.md](apb_slave_cdc.md) | ✅ Documented |
| **apb_monitor** | Transaction monitoring with 64-bit monitor bus output | [apb_monitor.md](apb_monitor.md) | ✅ Documented |

### Testbench Utilities

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb_master_stub** | Lightweight APB master for testbench integration | [apb_master_stub.md](apb_master_stub.md) | ✅ Documented |
| **apb_slave_stub** | Lightweight APB slave for testbench integration | [apb_slave_stub.md](apb_slave_stub.md) | ✅ Documented |

### Interconnect Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb_crossbar** | Full APB crossbar interconnect (NxM topology) | [apb_crossbar.md](apb_crossbar.md) | ✅ Documented |
| **apb_xbar** | APB crossbar with address decoding | [apb_xbar.md](apb_xbar.md) | ✅ Documented |

### Coverage Variants

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **apb_master_cg** | APB master with integrated coverage groups | - | ⏳ Pending |
| **apb_slave_cg** | APB slave with integrated coverage groups | - | ⏳ Pending |
| **apb_slave_cdc_cg** | APB slave CDC with integrated coverage groups | - | ⏳ Pending |

---

## Key Features

### APB Protocol Support
- ✅ **Full APB4/APB5 Compliance:** Complete protocol implementation
- ✅ **PSTRB Support:** Byte-lane strobes for partial writes
- ✅ **PPROT Support:** Protection attributes for security-aware systems
- ✅ **Error Handling:** PSLVERR support for error responses

### Clock Domain Crossing
- ✅ **Dual-Clock Operation:** APB (pclk) and backend (aclk) domains
- ✅ **Safe CDC:** Proper handshake-based clock domain crossing
- ✅ **Independent Frequencies:** Backend can run faster or slower than APB

### Monitoring and Debug
- ✅ **Transaction Monitoring:** Real-time protocol monitoring
- ✅ **64-bit Monitor Bus:** Standardized packet format
- ✅ **Error Detection:** Protocol violations, timeout detection
- ✅ **Performance Tracking:** Transaction counting, latency measurement

### Testbench Integration
- ✅ **Packed Interfaces:** Simplified testbench connectivity
- ✅ **Stub Modules:** Lightweight wrappers for CocoTB integration
- ✅ **WaveDrom Support:** Automated waveform generation

---

## Quick Start

### Using APB Master

```systemverilog
apb_master #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .DEPTH(2)
) u_apb_master (
    .aclk           (clk),
    .aresetn        (resetn),

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
    .rsp_pslverr    (rsp_pslverr),

    // APB master interface
    .m_apb_PSEL     (psel),
    .m_apb_PENABLE  (penable),
    .m_apb_PREADY   (pready),
    .m_apb_PADDR    (paddr),
    .m_apb_PWRITE   (pwrite),
    .m_apb_PWDATA   (pwdata),
    .m_apb_PSTRB    (pstrb),
    .m_apb_PRDATA   (prdata),
    .m_apb_PSLVERR  (pslverr)
);
```

### Using APB Slave

```systemverilog
apb_slave #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .DEPTH(2)
) u_apb_slave (
    .aclk           (clk),
    .aresetn        (resetn),

    // APB slave interface
    .s_apb_PSEL     (psel),
    .s_apb_PENABLE  (penable),
    .s_apb_PREADY   (pready),
    .s_apb_PADDR    (paddr),
    .s_apb_PWRITE   (pwrite),
    .s_apb_PWDATA   (pwdata),
    .s_apb_PSTRB    (pstrb),
    .s_apb_PRDATA   (prdata),
    .s_apb_PSLVERR  (pslverr),

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

All APB modules are verified using CocoTB-based testbenches located in `val/amba/`:

```bash
# Run all APB tests
pytest val/amba/test_apb*.py -v

# Run specific module tests
pytest val/amba/test_apb_master.py -v
pytest val/amba/test_apb_slave.py -v
pytest val/amba/test_apb_slave_cdc.py -v
pytest val/amba/test_apb_monitor.py -v

# Run with waveform generation
env ENABLE_WAVEDROM=1 pytest val/amba/test_apb_slave_wavedrom.py -v
```

### WaveDrom Tests

Several modules have dedicated WaveDrom tests that generate detailed timing diagrams:

- `test_apb_slave_wavedrom.py` - APB slave protocol waveforms
- `test_apb_slave_cdc.py::test_apb_slave_cdc_wavedrom` - CDC timing diagrams

Generated waveforms are stored in:
- JSON format: `_wavedrom/`
- SVG images: `_wavedrom_svg/`

---

## Protocol Details

### APB Transfer Phases

APB uses a simple two-phase protocol:

1. **SETUP Phase:** PSEL asserted, PENABLE low
   - Master presents address, control signals, and write data (if write)
   - Slave prepares for transfer

2. **ACCESS Phase:** PSEL and PENABLE both asserted
   - Slave completes transfer and asserts PREADY when ready
   - For reads, slave presents PRDATA
   - Slave may assert PSLVERR to signal error

### Signal Descriptions

| Signal | Direction | Description |
|--------|-----------|-------------|
| PCLK | Input | APB clock |
| PRESETn | Input | Active-low reset |
| PSEL | Master→Slave | Slave select |
| PENABLE | Master→Slave | Enable (ACCESS phase indicator) |
| PREADY | Slave→Master | Transfer complete |
| PADDR | Master→Slave | Address bus |
| PWRITE | Master→Slave | Write enable (1=write, 0=read) |
| PWDATA | Master→Slave | Write data |
| PSTRB | Master→Slave | Byte lane strobes |
| PPROT | Master→Slave | Protection attributes |
| PRDATA | Slave→Master | Read data |
| PSLVERR | Slave→Master | Error response |

---

## Design Notes

### Command/Response Architecture

All APB modules use a command/response interface pattern for backend integration:

**Command Interface (Master → Backend or APB → Backend):**
- `cmd_valid`, `cmd_ready` - Handshake signals
- `cmd_pwrite` - Write/read direction
- `cmd_paddr` - Transaction address
- `cmd_pwdata` - Write data
- `cmd_pstrb` - Byte strobes
- `cmd_pprot` - Protection attributes

**Response Interface (Backend → Master or Backend → APB):**
- `rsp_valid`, `rsp_ready` - Handshake signals
- `rsp_prdata` - Read data
- `rsp_pslverr` - Error flag

This separation enables:
- Clean clock domain crossing
- Buffering and pipelining
- Easy testbench integration
- Backend processing flexibility

### Monitor Bus Protocol

The APB monitor outputs standardized 64-bit packets:

```
[63:56] - Packet Type
[55:48] - Protocol ID
[47:40] - Event Code
[39:32] - Unit ID
[31:24] - Agent ID
[23:0]  - Event Data
```

See [apb_monitor.md](apb_monitor.md) for detailed packet format.

---

## Related Documentation

- **[AXI4 Modules](../axi4/README.md)** - Full AXI4 protocol components
- **[AXIL4 Modules](../axil4/README.md)** - AXI4-Lite components
- **[AXIS4 Modules](../axis4/README.md)** - AXI4-Stream components
- **[GAXI Modules](../gaxi/README.md)** - Generic AXI utilities

---

## References

### Specifications
- ARM AMBA APB Protocol Specification v2.0
- ARM AMBA 4 APB Protocol Specification

### Source Code
- RTL: `rtl/amba/apb/`
- Tests: `val/amba/test_apb*.py`
- Framework: `bin/CocoTBFramework/components/apb/`

### Test Documentation
- APB Master Tests: `val/amba/test_apb_master.py`
- APB Slave Tests: `val/amba/test_apb_slave.py`
- APB CDC Tests: `val/amba/test_apb_slave_cdc.py`
- APB Monitor Tests: `val/amba/test_apb_monitor.py`

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**
