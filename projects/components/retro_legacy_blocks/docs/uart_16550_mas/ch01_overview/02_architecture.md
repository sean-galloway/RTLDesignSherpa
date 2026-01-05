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

# APB UART 16550 - Architecture

## High-Level Block Diagram

![UART Architecture](../assets/svg/uart_top.svg)

## Module Hierarchy

```
apb_uart_16550 (Top Level)
+-- apb_slave
|   +-- APB protocol handling
|   +-- CMD/RSP interface conversion
|
+-- uart_16550_config_regs (Register Wrapper)
|   +-- uart_16550_regs (PeakRDL Generated)
|   |   +-- RBR/THR/DLL register
|   |   +-- IER/DLM register
|   |   +-- IIR/FCR registers
|   |   +-- LCR/MCR/LSR/MSR/SCR
|   |
|   +-- Baud Rate Generator
|   |   +-- Divisor latch
|   |   +-- 16x clock generation
|   |
|   +-- TX Engine
|   |   +-- TX FIFO (16 bytes)
|   |   +-- Serializer
|   |   +-- Start/Stop/Parity generation
|   |
|   +-- RX Engine
|       +-- RX FIFO (16 bytes)
|       +-- Deserializer
|       +-- Start detection
|       +-- Error detection
```

## Data Flow

### Transmit Path

```
1. Software Write to THR
   |
   v
2. Data enters TX FIFO
   |
   v
3. TX Engine reads from FIFO
   |
   v
4. Serializer generates:
   - Start bit (1 bit, low)
   - Data bits (5-8 bits, LSB first)
   - Parity bit (optional)
   - Stop bit(s) (1, 1.5, or 2 bits, high)
   |
   v
5. TXD output to external device
```

### Receive Path

```
1. RXD input from external device
   |
   v
2. Start bit detection
   - Sample at 16x baud rate
   - Validate mid-bit
   |
   v
3. Deserializer captures:
   - Data bits (5-8 bits)
   - Parity bit (if enabled)
   - Stop bit(s)
   |
   v
4. Error detection:
   - Parity error
   - Framing error
   - Break detection
   - Overrun error
   |
   v
5. Data enters RX FIFO
   |
   v
6. Software reads from RBR
```

### Interrupt Flow

```
1. Event Detection
   |
   +-- RX FIFO reaches trigger level
   +-- TX FIFO empty
   +-- Line status error
   +-- Modem status change
   |
   v
2. IIR Updated (priority encoded)
   |
   v
3. IRQ Asserted (if enabled in IER)
   |
   v
4. Software reads IIR
   - Highest priority interrupt identified
   - Some sources auto-clear on read
```

## Baud Rate Generation

### Divisor Calculation

```
Divisor = Input Clock / (16 x Desired Baud Rate)

Examples (48 MHz input):
  9600 baud:   Divisor = 48000000 / (16 x 9600)   = 312.5  -> 312 or 313
  115200 baud: Divisor = 48000000 / (16 x 115200) = 26.04  -> 26
  3000000 baud: Divisor = 48000000 / (16 x 3000000) = 1    -> 1
```

### Clock Generation

```
input_clk (48 MHz)
      |
      v
  +--------+
  | /DIV   |---> 16x_clk (baud x 16)
  +--------+
      |
      v
  +--------+
  | /16    |---> bit_clk (actual baud rate)
  +--------+
```

## FIFO Organization

### TX FIFO

| Feature | Value |
|---------|-------|
| Depth | 16 bytes |
| Width | 8 bits |
| Write | THR writes |
| Read | TX serializer |
| Status | THRE, TEMT in LSR |

### RX FIFO

| Feature | Value |
|---------|-------|
| Depth | 16 bytes |
| Width | 11 bits (8 data + 3 error) |
| Write | RX deserializer |
| Read | RBR reads |
| Trigger | 1, 4, 8, or 14 bytes |

## Resource Estimates

| Component | Flip-Flops | LUTs |
|-----------|-----------|------|
| apb_slave | ~20 | ~50 |
| uart_regs | ~150 | ~100 |
| baud_gen | ~20 | ~30 |
| tx_engine + FIFO | ~200 | ~150 |
| rx_engine + FIFO | ~250 | ~200 |
| **Total** | ~640 | ~530 |

---

**Next:** [03_clocks_and_reset.md](03_clocks_and_reset.md) - Clock and reset behavior
