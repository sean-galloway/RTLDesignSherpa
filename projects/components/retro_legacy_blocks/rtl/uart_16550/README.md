# APB UART 16550 Controller

NS16550-compatible UART controller with APB interface.

## Features

- 16-byte TX and RX FIFOs
- Programmable baud rate via 16-bit divisor
- 5/6/7/8 data bits
- 1/1.5/2 stop bits
- None/Odd/Even/Mark/Space parity
- Modem control signals (DTR, RTS, CTS, DSR, RI, DCD)
- Internal loopback mode
- Interrupt support with priority
- Optional CDC for asynchronous clock domains

## Architecture

```
APB -> apb_slave[_cdc] -> CMD/RSP -> peakrdl_to_cmdrsp ->
    -> uart_16550_regs (PeakRDL) -> hwif -> uart_16550_core
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| FIFO_DEPTH | 16 | FIFO depth (16 for 16550 compatibility) |
| SYNC_STAGES | 2 | Input synchronizer stages |
| APB_ADDR_WIDTH | 16 | APB address width |
| APB_DATA_WIDTH | 16 | APB data width |
| CDC_ENABLE | 0 | 1=async clocks, 0=same clock |
| SKID_DEPTH | 2 | CDC skid buffer depth |

## Register Map

| Offset | Register | DLAB | Access | Description |
|--------|----------|------|--------|-------------|
| 0x000 | UART_DATA | - | RW | TX/RX data (tx=lower 8, rx=upper 8) |
| 0x002 | UART_IER | 0 | RW | Interrupt Enable |
| 0x004 | UART_IIR | - | RO | Interrupt Identification |
| 0x006 | UART_FCR | - | WO | FIFO Control |
| 0x008 | UART_LCR | - | RW | Line Control |
| 0x00A | UART_MCR | - | RW | Modem Control |
| 0x00C | UART_LSR | - | RO* | Line Status (*errors W1C) |
| 0x00E | UART_MSR | - | RO* | Modem Status (*deltas W1C) |
| 0x010 | UART_SCR | - | RW | Scratch Register |
| 0x012 | UART_DLL | 1 | RW | Divisor Latch Low |
| 0x014 | UART_DLM | 1 | RW | Divisor Latch High |

Note: Unlike the original 16550, this implementation uses fixed addresses.
DLAB (LCR bit 7) is still present for software compatibility but register
aliasing is not implemented.

## Interrupt Priority

| Priority | ID | Source | Clearing |
|----------|-----|--------|----------|
| 1 (High) | 11b | RX Line Error | Read LSR |
| 2 | 10b | RX Data Available | Read RBR |
| 3 | 01b | TX Holding Empty | Read IIR or Write THR |
| 4 (Low) | 00b | Modem Status | Read MSR |

## Baud Rate Calculation

```
Divisor = Clock_Frequency / (16 * Baud_Rate)

Example: 100 MHz clock, 115200 baud
Divisor = 100,000,000 / (16 * 115200) = 54 (0x0036)
```

## Modem Signals

Active-low physical signals:
- cts_n, dsr_n, ri_n, dcd_n (inputs)
- dtr_n, rts_n, out1_n, out2_n (outputs)

The registers show inverted (active-high) values.

## Loopback Mode

When MCR[4] = 1:
- TX data internally looped to RX
- DTR -> DSR, RTS -> CTS, OUT1 -> RI, OUT2 -> DCD
- TX pin held high, RX pin ignored

## File Structure

```
uart_16550/
|-- peakrdl/
|   `-- uart_16550_regs.rdl     # PeakRDL register definitions
|-- filelists/
|   `-- apb_uart_16550.f        # Simulation/synthesis filelist
|-- uart_16550_regs_pkg.sv      # PeakRDL generated package
|-- uart_16550_regs.sv          # PeakRDL generated registers
|-- uart_16550_core.sv          # UART core (TX/RX/FIFOs)
|-- uart_16550_config_regs.sv   # Register-to-core adapter
|-- apb_uart_16550.sv           # APB wrapper (top level)
`-- README.md                   # This file
```

## Dependencies

- apb_slave.sv / apb_slave_cdc.sv
- peakrdl_to_cmdrsp.sv
- gaxi_skid_buffer.sv (for CDC)
- cdc_handshake.sv (for CDC)

## Test Plan

Tests located in: `projects/components/retro_legacy_blocks/dv/tests/test_apb_uart_16550.py`

| Test Level | Description |
|------------|-------------|
| basic | Register access, simple TX/RX, baud rate |
| medium | FIFOs, interrupts, modem signals, loopback |
| full | Error injection, stress testing, CDC |

## Implementation Notes

1. **FIFO Mode**: The 16550 starts with FIFOs disabled. Write FCR[0]=1 to enable.
2. **Interrupt Gating**: OUT2 (MCR[3]) gates the interrupt output.
3. **Character Timeout**: Implemented when FIFO enabled - interrupt after 4 character times of RX idle.
4. **Break Detection**: Detected when all data bits and stop bit are 0.
