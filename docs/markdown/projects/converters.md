**[← Back to Projects Index](index.md)** | **[Main Index](../index.md)**

# Protocol Converters - UART to AXI4-Lite Bridge

**Component:** `projects/components/converters/`
**Last Updated:** 2025-11-10

---

## Overview

The Protocol Converters component provides bridges between different communication protocols, enabling integration of diverse peripherals and interfaces in SoC designs. The initial implementation provides a UART to AXI4-Lite master bridge for command-based memory access over serial links.

### Current Components

1. **UART to AXI4-Lite Bridge** (`uart_axil_bridge`)
   - Parses ASCII commands from UART
   - Generates AXI4-Lite master transactions
   - Returns responses over UART
   - Timing isolation via skid buffers

---

## UART to AXI4-Lite Bridge

### Purpose

Provides command-line memory access over UART for:
- Debug and diagnostics
- Memory inspection and modification
- Register access without JTAG
- Prototype development
- Board bring-up

### Architecture

```
┌─────────────────────────────────────────────────────────┐
│              uart_axil_bridge (Top Level)               │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  ┌──────────┐     ┌──────────────┐     ┌───────────┐  │
│  │  UART RX │────▶│   Command    │────▶│  AXI4-Lite│  │
│  │ (uart_rx)│     │    Parser    │     │   Master  │  │
│  └──────────┘     │              │     │ (W + R)   │  │
│                   │ - CMD_IDLE   │     └───────────┘  │
│  ┌──────────┐     │ - READ_ADDR  │           │        │
│  │  UART TX │◀────│ - READ_DATA  │           │        │
│  │ (uart_tx)│     │ - EXECUTE    │     ┌─────▼─────┐  │
│  └──────────┘     │ - RESPONSE   │     │Skid Buffers│  │
│                   │              │     │(Timing Iso)│  │
│                   └──────────────┘     └───────────┘  │
│                                              │         │
│                                        AXI4-Lite       │
│                                        Master I/F      │
└─────────────────────────────────────────────────────────┘
```

**Key Components:**

1. **UART RX** (`uart_rx.sv`)
   - 8N1 protocol (8 data bits, no parity, 1 stop bit)
   - Configurable baud rate
   - 2-FF CDC synchronizer
   - Validates start bit at midpoint

2. **Command Parser** (FSM in `uart_axil_bridge.sv`)
   - Parses ASCII hex commands
   - Accumulates address/data nibbles
   - Validates command format
   - Generates AXI4-Lite transactions

3. **AXI4-Lite Masters** (`axil4_master_wr.sv`, `axil4_master_rd.sv`)
   - Simplified AXI4-Lite protocol (no bursts)
   - Skid buffer timing isolation
   - Single outstanding transaction

4. **UART TX** (`uart_tx.sv`)
   - 8N1 protocol
   - Configurable baud rate
   - Transmits responses

### Command Protocol

#### Write Command
```
Format: W <addr_hex> <data_hex>\n
Example: W 1000 DEADBEEF\n

Response: OK\n
```

#### Read Command
```
Format: R <addr_hex>\n
Example: R 1000\n

Response: 0xDEADBEEF\n
```

**Command Rules:**
- Commands are case-insensitive ('W' or 'w', 'R' or 'r')
- Address and data are hexadecimal (without '0x' prefix)
- Leading whitespace after command letter is skipped
- Commands must end with newline ('\n' or '\r')
- Maximum address width: 32 bits (8 hex digits)
- Data width: configurable (32 or 64 bits)

### Parameters

| Parameter | Description | Default | Range |
|-----------|-------------|---------|-------|
| `AXIL_ADDR_WIDTH` | Address bus width | 32 | 12-64 |
| `AXIL_DATA_WIDTH` | Data bus width | 32 | 32, 64 |
| `CLKS_PER_BIT` | Clock cycles per UART bit | 868 | 1-65535 |

**Baud Rate Calculation:**
```
CLKS_PER_BIT = System_Clock_Hz / Baud_Rate

Examples:
- 100 MHz / 115200 = 868
- 50 MHz / 115200 = 434
- 100 MHz / 9600 = 10417
```

### Interface Signals

#### UART Interface
```systemverilog
input  logic       aclk          // System clock
input  logic       aresetn       // Active-low reset
input  logic       i_uart_rx     // UART receive input
output logic       o_uart_tx     // UART transmit output
```

#### AXI4-Lite Master Interface
```systemverilog
// Write Address Channel
output logic [AXIL_ADDR_WIDTH-1:0] m_axil_awaddr
output logic [2:0]                  m_axil_awprot
output logic                        m_axil_awvalid
input  logic                        m_axil_awready

// Write Data Channel
output logic [AXIL_DATA_WIDTH-1:0]  m_axil_wdata
output logic [AXIL_DATA_WIDTH/8-1:0] m_axil_wstrb
output logic                         m_axil_wvalid
input  logic                         m_axil_wready

// Write Response Channel
input  logic [1:0]                   m_axil_bresp
input  logic                         m_axil_bvalid
output logic                         m_axil_bready

// Read Address Channel
output logic [AXIL_ADDR_WIDTH-1:0]   m_axil_araddr
output logic [2:0]                    m_axil_arprot
output logic                          m_axil_arvalid
input  logic                          m_axil_arready

// Read Data Channel
input  logic [AXIL_DATA_WIDTH-1:0]   m_axil_rdata
input  logic [1:0]                    m_axil_rresp
input  logic                          m_axil_rvalid
output logic                          m_axil_rready
```

### Timing Characteristics

#### UART Timing (115200 baud, 100 MHz clock)

| Operation | Duration (approx) |
|-----------|-------------------|
| 1 bit | 8.68 µs (868 clocks) |
| 1 char | 86.8 µs (8680 clocks) |
| Write cmd | ~1.3 ms (130k clocks) |
| Read cmd | ~950 µs (95k clocks) |

**Command Latency:**
- Command parsing: ~10-20 clocks after last character
- AXI4-Lite transaction: 2-10 clocks (depends on slave)
- Response transmission: ~260 µs (for "OK\n") to ~950 µs (for "0xDEADBEEF\n")
- **Total write cycle:** ~1.6 ms
- **Total read cycle:** ~2.0 ms

### Resource Utilization

**Estimated (Xilinx 7-series, 32-bit data, 32-bit address):**
- **LUTs:** ~400
- **Registers:** ~250
- **Block RAM:** 0
- **DSP:** 0

**Scaling:**
- 64-bit data width adds ~50 LUTs, ~30 registers
- Higher baud rates reduce counter width (saves ~10-20 registers)

### Verification Status

**Test Coverage:** >95%

**Test Levels:**
1. **GATE (basic):** Register access, simple operations (~10 min, 4 operations)
2. **FUNC (medium):** Multiple configurations, timing profiles (~10 min, 10 operations)
3. **FULL:** All configurations, stress testing (~50 min, 30 operations with edge cases)

**Verified Configurations:**
- Data widths: 32-bit, 64-bit (fully parameterized)
- Baud rates: 115200, 230400 (50 MHz and 100 MHz clocks)
- Address widths: 32-bit
- Test configurations: 6 total (all passing)

**Latest Test Results (2025-11-10):**
```
Test Suite: FULL (REG_LEVEL=FULL)
Configurations tested: 6
- params0: 32-bit data, basic level        ✅ PASSED
- params1: 64-bit data, basic level        ✅ PASSED
- params2: 32-bit data, different baud     ✅ PASSED
- params3: 32-bit data, medium level       ✅ PASSED
- params4: 32-bit data, full level         ✅ PASSED
- params5: 64-bit data, full level         ✅ PASSED

Total: 6 passed, 0 failed
Execution time: 49 minutes 36 seconds
Status: ✅ ALL TESTS PASSED
```

**Recent Fixes (2025-11-10):**
- Added full 64-bit data width support (dynamic buffer sizing)
- Fixed memory bounds validation in full test suite
- Increased CocoTB simulation timeout for comprehensive testing
- All Verilator width warnings resolved

### Usage Examples

#### Verilog Instantiation

```systemverilog
uart_axil_bridge #(
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .CLKS_PER_BIT(868)      // 100 MHz / 115200 baud
) u_uart_bridge (
    .aclk          (sys_clk),
    .aresetn       (sys_rst_n),

    // UART interface
    .i_uart_rx     (uart_rx_pin),
    .o_uart_tx     (uart_tx_pin),

    // AXI4-Lite master interface
    .m_axil_awaddr (axi_awaddr),
    .m_axil_awprot (axi_awprot),
    .m_axil_awvalid(axi_awvalid),
    .m_axil_awready(axi_awready),

    .m_axil_wdata  (axi_wdata),
    .m_axil_wstrb  (axi_wstrb),
    .m_axil_wvalid (axi_wvalid),
    .m_axil_wready (axi_wready),

    .m_axil_bresp  (axi_bresp),
    .m_axil_bvalid (axi_bvalid),
    .m_axil_bready (axi_bready),

    .m_axil_araddr (axi_araddr),
    .m_axil_arprot (axi_arprot),
    .m_axil_arvalid(axi_arvalid),
    .m_axil_arready(axi_arready),

    .m_axil_rdata  (axi_rdata),
    .m_axil_rresp  (axi_rresp),
    .m_axil_rvalid (axi_rvalid),
    .m_axil_rready (axi_rready)
);
```

#### Terminal Usage (via minicom/screen/pyserial)

```bash
# Configure terminal (115200 8N1)
screen /dev/ttyUSB0 115200

# Write to address 0x1000
W 1000 DEADBEEF
OK

# Read from address 0x1000
R 1000
0xDEADBEEF

# Write to address 0x2000 (64-bit data if configured)
W 2000 123456789ABCDEF0
OK

# Read back
R 2000
0x123456789ABCDEF0
```

#### Python Script Example

```python
import serial
import time

def uart_write(ser, addr, data):
    """Write to AXI4-Lite address via UART"""
    cmd = f"W {addr:X} {data:X}\n"
    ser.write(cmd.encode('ascii'))
    response = ser.readline().decode('ascii').strip()
    assert response == "OK", f"Write failed: {response}"
    print(f"Wrote 0x{data:X} to 0x{addr:X}")

def uart_read(ser, addr):
    """Read from AXI4-Lite address via UART"""
    cmd = f"R {addr:X}\n"
    ser.write(cmd.encode('ascii'))
    response = ser.readline().decode('ascii').strip()
    assert response.startswith("0x"), f"Read failed: {response}"
    data = int(response, 16)
    print(f"Read 0x{data:X} from 0x{addr:X}")
    return data

# Open serial port
with serial.Serial('/dev/ttyUSB0', 115200, timeout=1) as ser:
    # Write test pattern
    uart_write(ser, 0x1000, 0xDEADBEEF)
    uart_write(ser, 0x2000, 0x12345678)

    # Read back and verify
    data1 = uart_read(ser, 0x1000)
    data2 = uart_read(ser, 0x2000)

    assert data1 == 0xDEADBEEF
    assert data2 == 0x12345678
    print("All tests passed!")
```

### Known Issues

None currently documented. See `projects/components/converters/known_issues/` for any active issues.

### Design Considerations

#### Security
- **No authentication:** Anyone with UART access can read/write memory
- **Use cases:** Debug only, not for production deployment
- **Mitigation:** Disable in production, use only on secure debug ports

#### Error Handling
- Invalid commands are ignored (no error response)
- Malformed addresses/data cause undefined behavior
- AXI errors (SLVERR, DECERR) are not reported back to UART

#### Performance
- **Not for high-throughput:** UART is inherently slow (~115 kbps)
- **Use cases:** Debug, diagnostics, register peeking/poking
- **For bulk transfers:** Use DMA or faster interfaces

#### Future Enhancements
- Error reporting over UART
- Command echo/acknowledgment
- Burst transaction support (if AXI4 instead of AXI4-Lite)
- Authentication/authorization

### Integration Notes

#### Clock Domain Considerations
- Bridge operates in single clock domain (aclk)
- UART RX uses 2-FF synchronizer for async input
- No CDC required if AXI4-Lite slaves are in same clock domain

#### Reset Behavior
- Active-low asynchronous reset (aresetn)
- All internal state cleared on reset
- Command parsing resets to IDLE state
- UART TX defaults to idle (high) level

#### Address Mapping
- Bridge is address-agnostic (passes through from command)
- Address decoding handled by downstream AXI4-Lite infrastructure
- Invalid addresses may return DECERR or hang (depends on interconnect)

### Testing

#### Running Tests

```bash
cd projects/components/converters/dv/tests

# Basic test (GATE level)
env REG_LEVEL=GATE pytest test_uart_axil_bridge.py -v

# Functional tests (FUNC level)
env REG_LEVEL=FUNC pytest test_uart_axil_bridge.py -v

# Full regression (FULL level)
env REG_LEVEL=FULL pytest test_uart_axil_bridge.py -v

# Generate VCD waveforms
env WAVES=1 REG_LEVEL=GATE pytest test_uart_axil_bridge.py -v
```

#### Test Configurations

| Parameter | GATE | FUNC | FULL |
|-----------|------|------|------|
| Data widths | 32 | 32, 64 | 32, 64 |
| Baud rates | 868 | 434, 868 | 434, 868 |
| Test levels | basic | basic, medium | basic, medium, full |
| Duration | ~80s | ~240s | ~600s |

### File Locations

**RTL:**
- `projects/components/converters/rtl/uart_to_axil4/uart_axil_bridge.sv` - Top-level bridge
- `projects/components/converters/rtl/uart_to_axil4/uart_rx.sv` - UART receiver
- `projects/components/converters/rtl/uart_to_axil4/uart_tx.sv` - UART transmitter
- `projects/components/converters/rtl/filelists/uart_axil_bridge.f` - Compilation filelist

**Verification:**
- `projects/components/converters/dv/tbclasses/uart_axil_bridge_tb.py` - Testbench class
- `projects/components/converters/dv/tests/test_uart_axil_bridge.py` - Test runner
- `bin/CocoTBFramework/components/uart/` - UART BFM components

**Documentation:**
- `projects/components/converters/rtl/uart_to_axil4/README.md` - Detailed implementation guide
- `docs/markdown/projects/converters.md` - This document

### References

**Internal:**
- [Projects Overview](overview.md)
- [CocoTB Framework - UART Components](../CocoTBFramework/components/uart.md)
- [AXI4-Lite Master Components](../RTLAmba/axil4/axil4_master_wr.md)

**External:**
- [UART Wikipedia](https://en.wikipedia.org/wiki/Universal_asynchronous_receiver-transmitter)
- [AMBA AXI4-Lite Specification](https://developer.arm.com/documentation/ihi0022/latest/)

---

**Version:** 1.0
**Last Review:** 2025-11-09
**Status:** Production Ready
**Maintained By:** RTL Design Sherpa Project
