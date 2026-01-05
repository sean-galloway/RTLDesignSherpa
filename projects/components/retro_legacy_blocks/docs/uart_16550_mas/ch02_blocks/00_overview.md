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

# APB UART 16550 - Block Descriptions Overview

## Module Hierarchy

```
apb_uart_16550
|-- APB Interface
|-- Register File
|-- Baud Rate Generator
|-- TX Engine
|   |-- TX FIFO
|   |-- TX Serializer
|-- RX Engine
|   |-- RX Synchronizer
|   |-- RX Deserializer
|   |-- RX FIFO
|-- Interrupt Controller
|-- Modem Control
```

## Block Summary

| Block | Description |
|-------|-------------|
| APB Interface | APB slave protocol handling |
| Register File | 16550-compatible register set |
| Baud Generator | Programmable clock divider |
| TX Engine | Transmit data path with FIFO |
| RX Engine | Receive data path with FIFO |
| Interrupt Controller | Prioritized interrupt generation |
| Modem Control | CTS/RTS and modem signals |

## Detailed Block Descriptions

### 1. APB Interface
Handles APB protocol conversion and register access.

**See:** [01_apb_interface.md](01_apb_interface.md)

### 2. Register File
16550-compatible registers with DLAB addressing.

**See:** [02_register_file.md](02_register_file.md)

### 3. TX Engine
Transmit FIFO and serializer for data output.

**See:** [03_tx_engine.md](03_tx_engine.md)

### 4. RX Engine
Receive deserializer and FIFO for data input.

**See:** [04_rx_engine.md](04_rx_engine.md)

### 5. Baud Generator
Programmable divider for baud rate generation.

**See:** [05_baud_generator.md](05_baud_generator.md)

### 6. FIFO Subsystem
TX and RX FIFO implementation details.

**See:** [06_fifo.md](06_fifo.md)

---

**Next:** [01_apb_interface.md](01_apb_interface.md) - APB Interface details
