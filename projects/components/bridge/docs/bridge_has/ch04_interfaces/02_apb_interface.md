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

# APB Interface Overview

## APB Protocol Summary

### Signal Definition

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| PSEL | 1 | Output | Slave select |
| PENABLE | 1 | Output | Transaction phase |
| PADDR | ADDR_WIDTH | Output | Address |
| PWRITE | 1 | Output | Write enable |
| PWDATA | DATA_WIDTH | Output | Write data |
| PSTRB | DATA_WIDTH/8 | Output | Byte strobes |
| PPROT | 3 | Output | Protection |
| PRDATA | DATA_WIDTH | Input | Read data |
| PSLVERR | 1 | Input | Slave error |
| PREADY | 1 | Input | Slave ready |

: Table 4.1: APB Signal Definitions

## APB Slave Interface

### Signal Naming

APB slave ports use custom prefixes:

```systemverilog
// Example: APB slave with prefix "uart_apb_"
output logic        uart_apb_psel,
output logic        uart_apb_penable,
output logic [31:0] uart_apb_paddr,
output logic        uart_apb_pwrite,
output logic [31:0] uart_apb_pwdata,
output logic [3:0]  uart_apb_pstrb,
output logic [2:0]  uart_apb_pprot,
input  logic [31:0] uart_apb_prdata,
input  logic        uart_apb_pslverr,
input  logic        uart_apb_pready
```

## APB Transaction Timing

### Write Transaction

```
        ___     ___     ___     ___
PCLK   |   |___|   |___|   |___|   |___
            _________
PSEL   ____|         |________________
                _____
PENABLE ________|    |________________
            _________
PWRITE  ____|        |________________
       xxxxxx|  ADDR |xxxxxxxxxxxxxxxx
PADDR  xxxxxx|_______|xxxxxxxxxxxxxxxx
       xxxxxx| WDATA |xxxxxxxxxxxxxxxx
PWDATA xxxxxx|_______|xxxxxxxxxxxxxxxx
                _____
PREADY  ________|    |________________
```

### Read Transaction

```
        ___     ___     ___     ___
PCLK   |   |___|   |___|   |___|   |___
            _________
PSEL   ____|         |________________
                _____
PENABLE ________|    |________________
PWRITE  ______________________________
       xxxxxx|  ADDR |xxxxxxxxxxxxxxxx
PADDR  xxxxxx|_______|xxxxxxxxxxxxxxxx
                _____
PREADY  ________|    |________________
       xxxxxxxx|RDATA|xxxxxxxxxxxxxxxx
PRDATA xxxxxxxx|_____|xxxxxxxxxxxxxxxx
```

## AXI4 to APB Conversion

### Conversion Requirements

When an AXI4 master accesses an APB slave, Bridge performs:

1. **Burst splitting** - AXI4 bursts become multiple APB transfers
2. **Channel mapping** - AW+W combined into PADDR+PWDATA
3. **Response generation** - APB PSLVERR maps to AXI4 BRESP/RRESP
4. **Timing adaptation** - Insert wait states as needed

### Burst Handling

| AXI4 AWLEN | APB Transfers |
|------------|---------------|
| 0 (1 beat) | 1 transfer |
| 1 (2 beats) | 2 transfers |
| N (N+1 beats) | N+1 transfers |

: Table 4.2: AXI4 to APB Burst Conversion

### Error Mapping

| APB PSLVERR | AXI4 BRESP/RRESP |
|-------------|------------------|
| 0 (OK) | 2'b00 (OKAY) |
| 1 (Error) | 2'b10 (SLVERR) |

: Table 4.3: APB to AXI4 Error Mapping

## Performance Implications

### APB Limitations

- **Minimum 2 cycles per transfer** (setup + access phase)
- **No pipelining** (sequential transfers only)
- **No bursts** (each beat requires full handshake)

### Design Recommendations

- Use APB only for slow peripherals (UART, GPIO, config registers)
- Group APB slaves behind dedicated sub-crossbar
- Use AXI4/AXI4-Lite for higher-bandwidth slaves
