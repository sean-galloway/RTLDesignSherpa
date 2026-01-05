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

# APB UART 16550 - Baud Generator Block

## Overview

The baud generator creates the 16x oversampled clock used by TX and RX engines from a programmable divisor.

## Block Diagram

![Baud Generator Block](../assets/svg/uart_baud_gen.svg)

## Operation

### Clock Division

```
                         +-------------+
input_clk (pclk) ------->| 16-bit      |-----> 16x_baud_clk
                         | Divider     |
                         +-------------+
                               ^
                               |
                         +-----+-----+
                         | {DLM,DLL} |
                         +-----------+
```

### Formula

```
16x_baud_clk = input_clk / divisor

where divisor = (DLM << 8) | DLL

Actual baud rate = 16x_baud_clk / 16 = input_clk / (16 * divisor)
```

## Divisor Calculation

### Standard Formula

```
Divisor = Input_Clock / (16 * Desired_Baud_Rate)
```

### Rounding

For best accuracy, round to nearest integer:
```
Divisor = (Input_Clock + 8 * Baud_Rate) / (16 * Baud_Rate)
```

### Example Tables

**48 MHz Input Clock:**

| Baud Rate | Divisor | DLM | DLL | Actual Rate | Error |
|-----------|---------|-----|-----|-------------|-------|
| 9600 | 312 | 0x01 | 0x38 | 9615.4 | +0.16% |
| 19200 | 156 | 0x00 | 0x9C | 19230.8 | +0.16% |
| 38400 | 78 | 0x00 | 0x4E | 38461.5 | +0.16% |
| 57600 | 52 | 0x00 | 0x34 | 57692.3 | +0.16% |
| 115200 | 26 | 0x00 | 0x1A | 115384.6 | +0.16% |

**50 MHz Input Clock:**

| Baud Rate | Divisor | DLM | DLL | Actual Rate | Error |
|-----------|---------|-----|-----|-------------|-------|
| 9600 | 326 | 0x01 | 0x46 | 9585.9 | -0.15% |
| 19200 | 163 | 0x00 | 0xA3 | 19171.8 | -0.15% |
| 38400 | 81 | 0x00 | 0x51 | 38580.2 | +0.47% |
| 57600 | 54 | 0x00 | 0x36 | 57870.4 | +0.47% |
| 115200 | 27 | 0x00 | 0x1B | 115740.7 | +0.47% |

## Divisor Latch Registers

### DLL (Divisor Latch LSB)

| Address | 0x00 (DLAB=1) |
|---------|---------------|
| Bits | [7:0] |
| Access | RW |
| Reset | 0x00 |

### DLM (Divisor Latch MSB)

| Address | 0x04 (DLAB=1) |
|---------|---------------|
| Bits | [7:0] |
| Access | RW |
| Reset | 0x00 |

## Programming Sequence

1. Set LCR.DLAB = 1 (access divisor latches)
2. Write DLL (divisor low byte)
3. Write DLM (divisor high byte)
4. Clear LCR.DLAB = 0 (normal operation)

```c
void set_baud_rate(uint16_t divisor) {
    uint8_t lcr = LCR;        // Save LCR
    LCR = lcr | 0x80;         // Set DLAB
    DLL = divisor & 0xFF;     // Low byte
    DLM = divisor >> 8;       // High byte
    LCR = lcr;                // Restore LCR (clear DLAB)
}
```

## Special Cases

### Divisor = 0

- Invalid configuration
- Behavior undefined
- Should be avoided

### Divisor = 1

- Maximum baud rate
- Rate = input_clk / 16
- 48 MHz -> 3 Mbps

## Clock Enable

Baud clock generation enabled when:
- Divisor != 0
- TX or RX engine active

---

**Next:** [06_fifo.md](06_fifo.md) - FIFO Subsystem
