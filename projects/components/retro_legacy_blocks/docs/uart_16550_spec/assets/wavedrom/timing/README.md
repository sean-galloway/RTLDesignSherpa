# UART 16550 Timing Diagrams - WaveDrom JSON Files

This directory contains WaveDrom timing diagrams for UART 16550 operational scenarios.

## Files

| File | Scenario | Description |
|------|----------|-------------|
| `uart_tx_byte.json` | TX Transmission | APB write to THR, FIFO, shift register, serial output |
| `uart_rx_byte.json` | RX Reception | Serial input, start detect, sampling, FIFO write |
| `uart_fifo_threshold.json` | FIFO Trigger | RX FIFO fills to threshold, interrupt assertion |
| `uart_line_status.json` | Line Status | Framing error detection and LSR interrupt |
| `uart_modem_status.json` | Modem Status | CTS change detection and MSR interrupt |
| `uart_baud_generator.json` | Baud Generator | Divisor-based baud rate with 16x oversampling |
| `uart_loopback.json` | Loopback Mode | Internal TX to RX loopback for diagnostics |

## Signal Hierarchy

### APB Interface (External)
- `s_apb_PSEL`, `s_apb_PENABLE`, `s_apb_PREADY` - Control signals
- `s_apb_PWRITE`, `s_apb_PADDR`, `s_apb_PWDATA`, `s_apb_PRDATA` - Data signals

### Serial Interface (External)
- `uart_tx` - Serial transmit output
- `uart_rx` - Serial receive input
- `cts_n`, `dsr_n`, `dcd_n`, `ri_n` - Modem input signals
- `rts_n`, `dtr_n` - Modem output signals

### UART Core (Internal)
- **TX Path:** `tx_fifo_wr`, `tx_fifo_empty`, `tx_shift_load`, `r_tx_shift`, `baud_tick`
- **RX Path:** `rx_sync`, `start_detect`, `rx_sample`, `r_rx_shift`, `rx_done`, `rx_fifo_wr`
- **FIFO:** `tx_fifo_count`, `rx_fifo_count`, `cfg_rx_trigger`
- **Baud:** `cfg_divisor`, `r_baud_counter`, `r_sample_counter`
- **Status:** `r_framing_error`, `r_parity_error`, `r_overrun_error`, `r_delta_cts`

## Rendering to SVG

```bash
# Render all files
for f in *.json; do
    wavedrom-cli -i "$f" > "${f%.json}.svg"
done
```

## Scenarios Explained

### 1. TX Byte Transmission
Shows complete TX path: APB write to THR (Transmit Holding Register) pushes data to TX FIFO. When TX shift register is empty, data loads from FIFO. Baud tick shifts out bits in 8N1 format (start bit, 8 data bits LSB-first, stop bit).

### 2. RX Byte Reception
Shows complete RX path: Start bit (falling edge) detected on synchronized input. 16x oversampling locates bit center. Data sampled at mid-bit on each baud tick. After stop bit, byte written to RX FIFO.

### 3. FIFO Trigger Threshold
Shows RX FIFO fill level reaching configured trigger threshold (1, 4, 8, or 14 bytes). When threshold reached, RX Data Available interrupt asserts. CPU reads RBR to retrieve data.

### 4. Line Status Error
Shows framing error detection when stop bit samples as 0 instead of 1. Error flag set in LSR (Line Status Register), triggering Line Status interrupt for CPU error handling.

### 5. Modem Status Change
Shows CTS# input change detection. Async input synchronized, then edge-detected against previous state. Delta flag latched in MSR (Modem Status Register), triggering interrupt.

### 6. Baud Rate Generator
Shows divisor-based baud rate generation. Main baud counter divides clock by divisor value. 16x oversample counter provides fine timing for RX mid-bit sampling. TX uses baud_tick directly.

### 7. Loopback Mode
Shows diagnostic loopback mode (MCR[4]=1). TX shift output internally routes to RX input. External uart_tx held high. Allows software self-test without external loopback connection.

## Register Reference

| Register | Offset | Description |
|----------|--------|-------------|
| RBR/THR | 0x00 | Receive Buffer / Transmit Holding (DLAB=0) |
| IER | 0x04 | Interrupt Enable Register (DLAB=0) |
| IIR/FCR | 0x08 | Interrupt ID / FIFO Control |
| LCR | 0x0C | Line Control Register |
| MCR | 0x10 | Modem Control Register |
| LSR | 0x14 | Line Status Register |
| MSR | 0x18 | Modem Status Register |
| SCR | 0x1C | Scratch Register |
| DLL | 0x00 | Divisor Latch Low (DLAB=1) |
| DLM | 0x04 | Divisor Latch High (DLAB=1) |

## References

- **UART RTL:** `rtl/uart/apb_uart_16550.sv`
- **UART Testbench:** `dv/tbclasses/uart/uart_tb.py`
- **Constraint Class:** `bin/CocoTBFramework/tbclasses/wavedrom_user/uart.py`
