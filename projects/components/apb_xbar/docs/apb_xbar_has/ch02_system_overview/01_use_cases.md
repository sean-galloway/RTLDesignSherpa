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

# Use Cases

## Primary Use Cases

### UC-1: Simple Peripheral Interconnect (1x4)

**Scenario:** Single CPU accessing multiple peripherals

A microcontroller needs to access UART, GPIO, Timer, and SPI peripherals through a single APB master interface.

**Configuration:**
- 1 Master (CPU)
- 4 Slaves (UART, GPIO, Timer, SPI)
- Variant: `apb_xbar_1to4`

**Address Map:**
```
0x1000_0000 - 0x1000_FFFF : UART  (64KB)
0x1001_0000 - 0x1001_FFFF : GPIO  (64KB)
0x1002_0000 - 0x1002_FFFF : Timer (64KB)
0x1003_0000 - 0x1003_FFFF : SPI   (64KB)
```

### UC-2: Multi-Master System (2x4)

**Scenario:** CPU and DMA both accessing peripherals

An SoC where both CPU and DMA controller need access to shared peripherals.

**Configuration:**
- 2 Masters (CPU, DMA)
- 4 Slaves (peripherals)
- Variant: `apb_xbar_2to4`

**Key Behavior:**
- Round-robin arbitration when both masters access same peripheral
- No master starvation guaranteed
- Zero-bubble throughput on uncontended access

### UC-3: Protocol Conversion (1x1)

**Scenario:** APB timing boundary or clock domain preparation

Insert APB crossbar as a timing stage or preparation for clock domain crossing.

**Configuration:**
- 1 Master
- 1 Slave
- Variant: `apb_xbar_1to1` or `apb_xbar_thin`

**Benefits:**
- Isolates master from slave timing
- Provides consistent transaction buffering
- Minimal resource overhead (thin variant)

## Variant Selection Guide

| Use Case | Recommended Variant | Rationale |
|----------|---------------------|-----------|
| Simple peripheral bus | `apb_xbar_1to4` | Most common SoC configuration |
| CPU + DMA system | `apb_xbar_2to4` | Fair access for both masters |
| Timing isolation | `apb_xbar_thin` | Minimal overhead passthrough |
| Multi-master arbitration | `apb_xbar_2to1` | Focus on arbitration only |
| Custom topology | Generator | Any MxN configuration |

: Variant Selection Guide

---

**Next:** [Key Features](02_key_features.md)
