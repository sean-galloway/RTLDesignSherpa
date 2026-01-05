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

### Figure 1.2: UART Architecture

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

```mermaid
flowchart TD
    A["1. Software Write to THR"] --> B["2. Data enters TX FIFO"]
    B --> C["3. TX Engine reads from FIFO"]
    C --> D["4. Serializer generates:<br/>- Start bit (1 bit, low)<br/>- Data bits (5-8 bits, LSB first)<br/>- Parity bit (optional)<br/>- Stop bit(s) (1, 1.5, or 2 bits, high)"]
    D --> E["5. TXD output to external device"]
```

### Receive Path

```mermaid
flowchart TD
    A["1. RXD input from external device"] --> B["2. Start bit detection<br/>- Sample at 16x baud rate<br/>- Validate mid-bit"]
    B --> C["3. Deserializer captures:<br/>- Data bits (5-8 bits)<br/>- Parity bit (if enabled)<br/>- Stop bit(s)"]
    C --> D["4. Error detection:<br/>- Parity error<br/>- Framing error<br/>- Break detection<br/>- Overrun error"]
    D --> E["5. Data enters RX FIFO"]
    E --> F["6. Software reads from RBR"]
```

### Interrupt Flow

```mermaid
flowchart TD
    A["1. Event Detection"] --> B["RX FIFO reaches trigger level"]
    A --> C["TX FIFO empty"]
    A --> D["Line status error"]
    A --> E["Modem status change"]
    B --> F["2. IIR Updated<br/>(priority encoded)"]
    C --> F
    D --> F
    E --> F
    F --> G["3. IRQ Asserted<br/>(if enabled in IER)"]
    G --> H["4. Software reads IIR<br/>- Highest priority interrupt identified<br/>- Some sources auto-clear on read"]
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

```mermaid
flowchart TD
    A["input_clk<br/>(48 MHz)"] --> B["/DIV"]
    B -->|"16x_clk<br/>(baud x 16)"| C["/16"]
    C --> D["bit_clk<br/>(actual baud rate)"]
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
