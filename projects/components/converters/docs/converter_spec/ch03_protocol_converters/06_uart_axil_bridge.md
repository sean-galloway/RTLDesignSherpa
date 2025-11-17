# 3.6 UART to AXI4-Lite Bridge

**Module:** `uart_axil_bridge.sv`  
**Supporting Modules:** `uart_rx.sv`, `uart_tx.sv`  
**Status:** Planned (Infrastructure exists, implementation pending)  
**Version:** 1.0 (Specification)

---

## Overview

### Purpose

The UART-to-AXI4-Lite bridge provides human-readable ASCII command-line control of AXI4-Lite peripherals via UART serial interface. This enables:

- **Debug Interface:** Direct register access for system debugging
- **Configuration:** Setup and control peripherals without full firmware
- **Testing:** Manual or scripted validation of hardware functionality
- **Monitoring:** Read status registers and observe system state

### Key Features

- **Human-Readable Protocol:** ASCII text commands (e.g., "W 0x1000 0xDEADBEEF")
- **Standard Baud Rates:** 115200 baud default, configurable
- **Timing Isolation:** Uses AXI4-Lite skid buffers to decouple UART timing from bus
- **Simple Integration:** Drop-in component for any AXI4-Lite system
- **Bidirectional:** Supports both read and write transactions
- **Error Reporting:** ASCII responses indicate success/failure

---

## Architecture

### Module Hierarchy

```
uart_axil_bridge (top-level)
├── uart_rx          - UART receiver (serial → parallel)
├── uart_tx          - UART transmitter (parallel → serial)
├── cmd_parser       - ASCII command decoder
├── axi_master_wr    - AXI4-Lite write transaction generator
├── axi_master_rd    - AXI4-Lite read transaction generator
└── response_encoder - Format read data as ASCII response
```

### Data Flow

**Write Command Flow:**
```
UART RX → ASCII Parser → Address/Data Decode → AXI4-Lite Write → Response → UART TX
   "W 0x1000 0xABCD"              ↓
                            AW: addr=0x1000
                            W:  data=0xABCD, strb=0xF
                            B:  resp → "OK" or "ERR"
```

**Read Command Flow:**
```
UART RX → ASCII Parser → Address Decode → AXI4-Lite Read → Format Data → UART TX
   "R 0x2000"                  ↓
                         AR: addr=0x2000
                         R:  data → "0x12345678"
```

---

## Command Protocol (Planned)

### Write Command

**Format:** `W <address> <data>`

**Example:**
```
TX: W 0x1000 0xDEADBEEF<CR><LF>
RX: OK<CR><LF>
```

**Parameters:**
- `<address>` - Hexadecimal address (0x prefix optional)
- `<data>` - Hexadecimal data value
- Whitespace between tokens (space or tab)
- Command terminated by CR, LF, or CR+LF

### Read Command

**Format:** `R <address>`

**Example:**
```
TX: R 0x1000<CR><LF>
RX: 0xDEADBEEF<CR><LF>
```

### Error Responses

```
TX: W 0xFFFFFFFF 0x1234<CR><LF>
RX: ERR: SLVERR<CR><LF>
```

Errors reported:
- `ERR: SLVERR` - AXI4-Lite slave error response
- `ERR: DECERR` - AXI4-Lite decode error
- `ERR: SYNTAX` - Malformed command

---

## Parameters

### uart_axil_bridge.sv

| Parameter | Default | Description |
|-----------|---------|-------------|
| `AXI_ADDR_WIDTH` | 32 | AXI4-Lite address bus width |
| `AXI_DATA_WIDTH` | 32 | AXI4-Lite data bus width |
| `UART_BAUD_RATE` | 115200 | UART baud rate (bits per second) |
| `CLK_FREQ_HZ` | 100000000 | System clock frequency (for baud rate generation) |
| `CMD_BUFFER_DEPTH` | 256 | Command buffer size (bytes) |
| `RESP_BUFFER_DEPTH` | 256 | Response buffer size (bytes) |

---

## Interfaces

### UART Interface

```systemverilog
// UART pins
input  logic uart_rx,           // Serial receive input
output logic uart_tx            // Serial transmit output
```

### AXI4-Lite Master Interface

```systemverilog
// Write address channel
output logic [AXI_ADDR_WIDTH-1:0]    m_axil_awaddr,
output logic                         m_axil_awvalid,
input  logic                         m_axil_awready,

// Write data channel
output logic [AXI_DATA_WIDTH-1:0]    m_axil_wdata,
output logic [(AXI_DATA_WIDTH/8)-1:0] m_axil_wstrb,
output logic                         m_axil_wvalid,
input  logic                         m_axil_wready,

// Write response channel
input  logic [1:0]                   m_axil_bresp,
input  logic                         m_axil_bvalid,
output logic                         m_axil_bready,

// Read address channel
output logic [AXI_ADDR_WIDTH-1:0]    m_axil_araddr,
output logic                         m_axil_arvalid,
input  logic                         m_axil_arready,

// Read data channel
input  logic [AXI_DATA_WIDTH-1:0]    m_axil_rdata,
input  logic [1:0]                   m_axil_rresp,
input  logic                         m_axil_rvalid,
output logic                         m_axil_rready
```

---

## Timing Isolation

### Challenge

UART operates at very low data rates (115200 baud ≈ 11.52 kB/s) compared to AXI4-Lite bus speeds (typically 100+ MHz). Direct connection would create:
- Long combinational paths
- Timing closure difficulties
- Metastability risks

### Solution

The bridge uses **AXI4-Lite skid buffers** (`gaxi_skid_buffer.sv`) to decouple UART timing from bus timing:

```
UART Domain            Timing Isolation         AXI4-Lite Bus
─────────────          ───────────────          ──────────────
  cmd_parser    →    Command FIFO    →    axil4_master_wr
                     ↓                ↓
              Skid Buffer        Skid Buffer
                     ↑                ↑
  resp_encoder  ←   Response FIFO   ←    axil4_master_rd
```

**Benefits:**
- Clean timing domains
- No timing paths between UART and AXI bus
- Predictable bus behavior
- Easy to meet timing at any clock frequency

---

## Use Cases

### 1. System Debug Interface

**Scenario:** Debug hardware during bring-up

```
# Read device ID register
> R 0x0000
0x12345678

# Write configuration register
> W 0x0010 0x00000001
OK

# Read status
> R 0x0020
0x00000003
```

### 2. Automated Testing

**Scenario:** Scripted register tests via UART

```bash
# test_script.txt
W 0x1000 0xAAAAAAAA
R 0x1000
W 0x1004 0x55555555
R 0x1004
```

```python
# Send via Python
from serial import Serial
uart = Serial('/dev/ttyUSB0', 115200)
for line in open('test_script.txt'):
    uart.write(line.encode())
    response = uart.readline()
    print(response.decode())
```

### 3. Manufacturing Test

**Scenario:** Production test fixture

- UART commands sent from test jig
- Verify peripheral functionality
- Read back calibration data
- Simple pass/fail via UART responses

---

## Integration Example

```systemverilog
uart_axil_bridge #(
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32),
    .UART_BAUD_RATE(115200),
    .CLK_FREQ_HZ(100_000_000)
) u_uart_debug (
    .aclk           (sys_clk),
    .aresetn        (sys_rst_n),
    
    // UART pins (connect to FPGA package pins)
    .uart_rx        (uart_rxd),
    .uart_tx        (uart_txd),
    
    // AXI4-Lite master (connect to peripherals)
    .m_axil_awaddr  (debug_awaddr),
    .m_axil_awvalid (debug_awvalid),
    .m_axil_awready (debug_awready),
    // ... other AXI4-Lite signals
);
```

---

## Design Considerations

### Address Width

**Standard:** 32-bit addresses sufficient for most peripherals

**Extended:** Can configure up to 64-bit for large address spaces

### Data Width

**Standard:** 32-bit data matches most peripheral registers

**Supported:** 8, 16, 32, 64-bit data widths

**Note:** ASCII hex representation becomes verbose for wide data

### Command Buffer Sizing

**Minimum:** 64 bytes (holds ~8 commands)

**Recommended:** 256 bytes  (holds ~32 commands)

**Large Systems:** 1024+ bytes for scripted test sequences

---

## Implementation Status

**Current Status:** Infrastructure and specification complete

**Existing:**
- ✅ Filelist defined (`rtl/filelists/uart_axil_bridge.f`)
- ✅ Test infrastructure (`dv/tests/test_uart_axil_bridge.py`)
- ✅ Testbench class (`dv/tbclasses/uart_axil_bridge_tb.py`)
- ✅ Python host tools (`bin/uart_axi_bridge.py`)

**Pending:**
- ⏳ RTL implementation (`rtl/uart_to_axil4/*.sv` files)
- ⏳ Dedicated module README
- ⏳ Block diagram

**Priority:** Medium (useful for debug, not critical for core functionality)

---

## Future Enhancements

1. **Batch Commands:** Support multiple commands in single UART packet
2. **Binary Protocol:** Optional binary mode for higher throughput
3. **Burst Support:** Extend to support AXI4 bursts (not just single beats)
4. **Register Macros:** Named register access ("READ CONFIG" vs "R 0x1000")
5. **Status Polling:** Automatic periodic register monitoring

---

## Related Modules

- `axil4_master_wr.sv` - Used for AXI4-Lite write transactions
- `axil4_master_rd.sv` - Used for AXI4-Lite read transactions
- `gaxi_skid_buffer.sv` - Timing isolation buffers

---

## References

- **UART Protocol:** RS-232 serial communication standard
- **AXI4-Lite:** ARM AMBA AXI4-Lite specification
- **Python Tools:** `bin/uart_axi_bridge.py` - Host-side UART interface

---

**Author:** RTL Design Sherpa Project  
**Status:** Specification Complete, Implementation Pending  
**Last Updated:** 2025-11-14
