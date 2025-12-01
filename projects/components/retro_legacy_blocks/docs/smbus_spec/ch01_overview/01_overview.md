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

## Applications

- Temperature monitoring
- Voltage monitoring
- Fan control
- EEPROM access
- Power management
- System health monitoring

## Block Diagram

![SMBus Block Diagram](../assets/svg/smbus_top.svg)

## Register Summary

| Offset | Name | Description |
|--------|------|-------------|
| 0x00 | SMBUS_STATUS | Status register |
| 0x04 | SMBUS_CONTROL | Control register |
| 0x08 | SMBUS_COMMAND | Command type |
| 0x0C | SMBUS_ADDRESS | Target address |
| 0x10 | SMBUS_DATA0 | Data byte 0 |
| 0x14 | SMBUS_DATA1 | Data byte 1 |
| 0x18 | SMBUS_BLOCK | Block data count |
| 0x1C | SMBUS_PEC | PEC value |
| 0x20 | SMBUS_AUXCTL | Auxiliary control |
| 0x80-0x9F | SMBUS_BLOCKDATA | Block data buffer |

---

**Next:** [02_architecture.md](02_architecture.md)
