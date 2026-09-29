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

# UART to AXI4-Lite Bridge

**Purpose:** Convert UART ASCII commands to AXI4-Lite memory transactions

**Status:** Functional - ready for integration and testing

---

## Overview

This bridge allows simple UART command-line control of AXI4-Lite memory-mapped peripherals. It parses ASCII commands received via UART and executes the corresponding AXI4-Lite read or write transactions.

**Key Features:**
- Simple ASCII command protocol (human-readable)
- AXI4-Lite master interface with timing isolation
- Configurable baud rate (default: 115200)
- Single-transaction operation (no bursts)
- Minimal resource usage

**Use Cases:**
- Debug access to memory-mapped registers
- Low-speed peripheral control via UART
- FPGA board bring-up and testing
- Embedded system debugging

---

## Modules

### uart_axil_bridge.sv

**Main bridge** - Command parser + AXI4-Lite master with timing isolation

**Parameters:**
- `AXIL_ADDR_WIDTH` - Address width (default: 32)
- `AXIL_DATA_WIDTH` - Data width (default: 32)
- `CLKS_PER_BIT` - Clock cycles per UART bit (default: 868 for 100MHz/115200 baud)
- `SKID_DEPTH_AR/R/AW/W/B` - Timing isolation FIFO depths

**Interfaces:**
- UART: `i_uart_rx`, `o_uart_tx`
- AXI4-Lite Master: Standard AXI4-Lite interface (`m_axil_*`)

### uart_rx.sv

**UART receiver** - 8N1 protocol with ready/valid handshaking

### uart_tx.sv

**UART transmitter** - 8N1 protocol with ready/valid handshaking

---

## Command Protocol

### Write Command

**Format:** `W <addr_hex> <data_hex>\n`

**Example:**
```
W 1000 DEADBEEF\n
```

**Response:** `OK\n`

**Description:** Writes `0xDEADBEEF` to address `0x1000`

### Read Command

**Format:** `R <addr_hex>\n`

**Example:**
```
R 1000\n
```

**Response:** `0xDEADBEEF\n`

**Description:** Reads from address `0x1000`, returns data in hex format

### Command Details

- **Case insensitive:** `W` or `w`, `R` or `r`
- **Hex addresses/data:** No `0x` prefix required
- **Whitespace:** Space separates address and data
- **Terminator:** Newline (`\n`) or carriage return (`\r`)
- **Leading zeros:** Optional (e.g., `1000` same as `00001000`)

---

## Integration Example

```systemverilog
uart_axil_bridge #(
    .AXIL_ADDR_WIDTH (32),
    .AXIL_DATA_WIDTH (32),
    .CLKS_PER_BIT    (868)  // 100MHz / 115200 baud
) u_uart_bridge (
    .aclk    (clk),
    .aresetn (rst_n),

    // UART interface
    .i_uart_rx (uart_rx_pin),
    .o_uart_tx (uart_tx_pin),

    // AXI4-Lite Master
    .m_axil_awaddr  (axil_awaddr),
    .m_axil_awprot  (axil_awprot),
    .m_axil_awvalid (axil_awvalid),
    .m_axil_awready (axil_awready),

    .m_axil_wdata  (axil_wdata),
    .m_axil_wstrb  (axil_wstrb),
    .m_axil_wvalid (axil_wvalid),
    .m_axil_wready (axil_wready),

    .m_axil_bresp  (axil_bresp),
    .m_axil_bvalid (axil_bvalid),
    .m_axil_bready (axil_bready),

    .m_axil_araddr  (axil_araddr),
    .m_axil_arprot  (axil_arprot),
    .m_axil_arvalid (axil_arvalid),
    .m_axil_arready (axil_arready),

    .m_axil_rdata  (axil_rdata),
    .m_axil_rresp  (axil_rresp),
    .m_axil_rvalid (axil_rvalid),
    .m_axil_rready (axil_rready)
);
```

---

## Baud Rate Configuration

**Formula:** `CLKS_PER_BIT = clock_freq_hz / baud_rate`

**Common Configurations:**

| Clock Freq | Baud Rate | CLKS_PER_BIT |
|------------|-----------|--------------|
| 100 MHz    | 115200    | 868          |
| 100 MHz    | 9600      | 10417        |
| 50 MHz     | 115200    | 434          |
| 50 MHz     | 9600      | 5208         |

**Example:**
```systemverilog
uart_axil_bridge #(
    .CLKS_PER_BIT(10417)  // 100MHz / 9600 baud
) u_uart_bridge ( ... );
```

---

## Timing Isolation

The bridge includes **AXI4-Lite timing isolation modules** (`axil4_master_wr` and `axil4_master_rd`) to:
- Break timing paths between slow command parser and fast AXI4-Lite bus
- Provide buffering via configurable skid buffers
- Improve timing closure in high-speed designs

**Skid Buffer Depths:**
- `SKID_DEPTH_AR/AW` - Address channel buffering (default: 2)
- `SKID_DEPTH_R/W` - Data channel buffering (default: 4)
- `SKID_DEPTH_B` - Response channel buffering (default: 2)

**Increase depths if:**
- Timing closure difficult
- High-frequency AXI4-Lite bus (>200MHz)
- Long routing paths

---

## Design Notes

### Why AXI4-Lite (Not Full AXI4)?

1. **UART is slow** - 115200 baud = ~11.5 KB/s, no benefit from burst support
2. **Simpler** - Fewer signals, easier integration, lower resource usage
3. **Perfect match** - UART command protocol is single-transaction (read/write one address at a time)
4. **Peripheral compatible** - Most peripherals use AXI4-Lite

### Command Parser Architecture

- **State Machine:** 11-state FSM for command parsing
- **Hex Parsing:** Nibble-by-nibble accumulation
- **Response Generation:** On-the-fly hex conversion for read responses
- **Error Handling:** Invalid commands ignored, state machine returns to IDLE

### Signal Naming Convention

- **Inputs:** `i_*` prefix (e.g., `i_uart_rx`)
- **Outputs:** `o_*` prefix (e.g., `o_uart_tx`)
- **Wires (comb):** `w_*` prefix (e.g., `w_fub_awaddr`)
- **Registers:** `r_*` prefix (e.g., `r_cmd_state`)

### Reset Handling

Uses **reset macros** from `reset_defs.svh`:
- `ALWAYS_FF_RST(clk, rst_n, ...)` - Standard flip-flop with reset
- `RST_ASSERTED(rst_n)` - Reset condition check

**Note:** `aresetn` is active-low asynchronous reset (AMBA standard)

---

## Testing

**Testbench:** TBD

**Test Using UART Terminal:**

```bash
# Connect via serial port
screen /dev/ttyUSB0 115200

# Write to address 0x1000
W 1000 12345678

# Expected response:
OK

# Read from address 0x1000
R 1000

# Expected response:
0x12345678
```

**Python Test Script Example:**

```python
import serial

uart = serial.Serial('/dev/ttyUSB0', 115200, timeout=1)

# Write command
uart.write(b'W 1000 DEADBEEF\n')
response = uart.readline()
assert response == b'OK\n'

# Read command
uart.write(b'R 1000\n')
response = uart.readline()
assert response == b'0xDEADBEEF\n'

uart.close()
```

---

## Resource Usage

**Estimated (Xilinx 7-Series):**

| Resource | Utilization |
|----------|-------------|
| LUTs     | ~300        |
| FFs      | ~200        |
| BRAMs    | 0           |
| DSPs     | 0           |

**Notes:**
- Very small footprint
- Most resources in command parser FSM
- Timing isolation adds ~50 FFs per channel

---

## Known Limitations

1. **Single transaction only** - No burst support (use AXI4 full if needed)
2. **No pipelining** - One command at a time (UART is bottleneck anyway)
3. **Fixed data width** - Command protocol assumes 32-bit data
4. **No error reporting** - AXI4-Lite BRESP/RRESP not returned to UART (future enhancement)
5. **ASCII only** - Binary protocols would be more efficient but less human-readable

---

## Future Enhancements

- Error response reporting (SLVERR, DECERR)
- Status register read (bridge busy, error flags)
- Burst support for faster block transfers
- Configurable data width in command protocol
- Binary command mode for efficiency

---

**Version:** 1.0
**Created:** 2025-11-09
**Author:** RTL Design Sherpa Project
