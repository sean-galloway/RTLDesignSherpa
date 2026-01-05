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

# APB UART 16550 - References

## Internal Documentation

### RTL Source Files
- `rtl/uart_16550/apb_uart_16550.sv` - Main UART module
- `rtl/uart_16550/uart_16550_config_regs.sv` - Register wrapper
- `rtl/uart_16550/uart_16550_regs.sv` - PeakRDL-generated registers
- `rtl/uart_16550/uart_16550.rdl` - Register description source

### Related Specifications
- APB Protocol Specification (AMBA 3)
- RLB Integration Guide

## External References

### Original 16550 Documentation
- **PC16550D Data Sheet**
  - National Semiconductor
  - Defines original 16550 behavior and registers
  - Industry standard reference

- **TL16C550C Data Sheet**
  - Texas Instruments
  - Pin-compatible 16550 implementation
  - Enhanced features

### Serial Communication Standards
- **EIA/TIA-232-F**
  - Serial interface electrical specification
  - Signal levels and connector pinouts

- **EIA/TIA-562**
  - Low-voltage version of RS-232
  - 3.3V compatible signaling

### ARM AMBA Specifications
- **AMBA 3 APB Protocol Specification**
  - ARM IHI 0024E
  - Defines APB interface timing and protocol

## Design References

### UART Implementation
- Asynchronous serial communication theory
- Baud rate generation techniques
- FIFO design for serial interfaces

### Clock Domain Crossing
- Dual flip-flop synchronizer methodology
- Handshake protocols for CDC

### Error Detection
- Parity generation and checking
- Framing error detection
- Break condition detection

---

**Next:** [Chapter 2: Block Descriptions](../ch02_blocks/00_overview.md)
