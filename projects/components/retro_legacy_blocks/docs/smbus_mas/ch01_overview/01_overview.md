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

# APB SMBus - Overview

## Introduction

The APB SMBus controller provides System Management Bus communication with APB interface. It supports host controller functionality for accessing SMBus devices.

## Key Features

- SMBus 2.0 compatible
- Host controller mode
- Quick Command, Send/Receive Byte
- Read/Write Byte/Word
- Block Read/Write (up to 32 bytes)
- PEC (Packet Error Checking) support
- Programmable clock divider
- Interrupt-driven operation
- Timeout detection

> **Implementation status:** Several protocol features described in this chapter are not
> fully realized in the current RTL. Timeout detection, PEC generation/verification,
> multi-master arbitration, clock stretching, and slave mode are present in the register
> interface but not functional in `smbus_core` today. The timing diagrams below
> (Waveforms 1.3-1.5 in particular) illustrate SMBus protocol intent, not current hardware
> behavior. See the Implementation Limitations section of
> [Chapter 5: Register Map](../ch05_registers/01_register_map.md) and
> `rtl/smbus/IMPLEMENTATION_STATUS.md` for the tracked status.

## Applications

- Temperature monitoring
- Voltage monitoring
- Fan control
- EEPROM access
- Power management
- System health monitoring

## Block Diagram

### Figure 1.1: SMBus Block Diagram

![SMBus Block Diagram](../assets/svg/smbus_top.png)

## Timing Diagrams

### Waveform 1.1: Byte Write (Start + Address)

Shows the START condition and 7-bit address transmission.

![SMBus Byte Write](../assets/wavedrom/timing/smbus_byte_write.png)

START condition is SDA falling while SCL is high. The 7-bit slave address plus R/W bit is clocked out, followed by slave ACK (SDA low during 9th clock).

### Waveform 1.2: Byte Read

Shows slave-to-master data transfer.

![SMBus Byte Read](../assets/wavedrom/timing/smbus_byte_read.png)

Slave drives 8 data bits while master clocks SCL. Master samples each bit on SCL rising edge, then provides ACK (more data) or NACK (last byte).

### Waveform 1.3: Clock Stretching

Slave flow control by holding SCL low.

![SMBus Clock Stretch](../assets/wavedrom/timing/smbus_clock_stretch.png)

When the slave needs processing time, it holds SCL low after the master releases it. Master waits for SCL to rise before continuing. This provides backpressure without data loss.

### Waveform 1.4: Multi-Master Arbitration

Collision detection when multiple masters start simultaneously.

![SMBus Arbitration](../assets/wavedrom/timing/smbus_arbitration.png)

Both masters monitor SDA while transmitting. If a master drives 1 but reads 0 (wired-AND bus), it loses arbitration and backs off. The winner continues the transaction.

### Waveform 1.5: Packet Error Check (PEC)

CRC-8 error detection for data integrity.

![SMBus PEC](../assets/wavedrom/timing/smbus_pec.png)

PEC is calculated over address, command, and data bytes using CRC-8. The PEC byte is transmitted after data and verified by the receiver to detect transmission errors.

## Register Summary

| Offset | Name | Access | Description |
|--------|------|--------|-------------|
| 0x00 | SMBUS_CONTROL | RW | Global control (enable, mode, PEC, resets) |
| 0x04 | SMBUS_STATUS | RO | Status flags and FSM state |
| 0x08 | SMBUS_COMMAND | RW | Transaction type, command byte, start/stop |
| 0x0C | SMBUS_SLAVE_ADDR | RW | Target slave address |
| 0x10 | SMBUS_DATA | RW | Single data byte |
| 0x14 | SMBUS_TX_FIFO | WO | Transmit FIFO write port |
| 0x18 | SMBUS_RX_FIFO | RO | Receive FIFO read port |
| 0x1C | SMBUS_FIFO_STATUS | RO | TX/RX FIFO levels and flags |
| 0x20 | SMBUS_CLK_DIV | RW | SCL clock divider |
| 0x24 | SMBUS_TIMEOUT | RW | Timeout threshold |
| 0x28 | SMBUS_OWN_ADDR | RW | Own slave address (slave mode) |
| 0x2C | SMBUS_INT_ENABLE | RW | Interrupt enable mask |
| 0x30 | SMBUS_INT_STATUS | W1C | Interrupt status |
| 0x34 | SMBUS_PEC | RW | PEC value (CRC-8) |
| 0x38 | SMBUS_BLOCK_COUNT | RW | Block transfer byte count |

See [Chapter 5: Register Map](../ch05_registers/01_register_map.md) for full field
definitions, reset values, and implementation limitations.

---

**Next:** [02_architecture.md](02_architecture.md)
