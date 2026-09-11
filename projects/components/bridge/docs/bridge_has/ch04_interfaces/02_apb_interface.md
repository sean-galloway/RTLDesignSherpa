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

# APB Interface

## Overview

APB is where the slow things live: UARTs, GPIO, configuration registers. This page covers the bridge's APB surface — the signal set, the port-naming convention, transaction timing, and what the AXI4-to-APB conversion actually does.

## Ports

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

## Functional Description

### AXI4 to APB Conversion

When an AXI4 master accesses an APB slave, the bridge:

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

## Timing

Every APB transfer pays for a setup phase plus an access phase, so the floor is two cycles per transfer. There is no pipelining — transfers run sequentially — and no bursts: each beat requires the full handshake.

## Waveforms

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

## APB Requester Ports

Since BRIDGE-014 an APB port can also be a *master*: `protocol = "apb"` or
`"apb5"` in `[[bridge.masters]]`. The signal set is the same ten (fifteen
for APB5) with the directions of the slave table reversed -- the bridge is
the completer, so `PSEL`, `PENABLE`, `PADDR[31:0]`, `PWRITE`, `PWDATA`,
`PSTRB`, `PPROT` are inputs and `PREADY`, `PRDATA`, `PSLVERR` outputs.
`PADDR` is the full 32-bit fabric address (the validator insists on
`addr_width = 32`); each transfer becomes one single-beat AXI4 transaction
through `apb4_to_axi4` / `apb5_to_axi4`, and both `SLVERR` and `DECERR`
come back as `PSLVERR`. The requester is one-outstanding by nature of APB,
so throughput is one transfer per fabric round trip.

## Design Notes

- Use APB only for slow peripherals (UART, GPIO, config registers)
- Group APB slaves behind dedicated sub-crossbar
- Use AXI4/AXI4-Lite for higher-bandwidth slaves
