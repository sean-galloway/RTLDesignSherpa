# APB SMBus - Register Map

## Register Summary

| Offset | Name | Access | Description |
|--------|------|--------|-------------|
| 0x00 | SMBUS_STATUS | RO/W1C | Status |
| 0x04 | SMBUS_CONTROL | RW | Control |
| 0x08 | SMBUS_COMMAND | RW | Command byte |
| 0x0C | SMBUS_ADDRESS | RW | Slave address |
| 0x10 | SMBUS_DATA0 | RW | Data byte 0 |
| 0x14 | SMBUS_DATA1 | RW | Data byte 1 |
| 0x18 | SMBUS_BLOCK_CNT | RW | Block count |
| 0x1C | SMBUS_PEC | RO | PEC value |
| 0x20 | SMBUS_AUXCTL | RW | Auxiliary control |
| 0x80-0x9F | SMBUS_BLOCK_DATA | RW | Block buffer (32 bytes) |

---

## SMBUS_STATUS (0x00)

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | BUSY | RO | Transaction in progress |
| 1 | INTR | W1C | Interrupt pending |
| 2 | DEV_ERR | W1C | Device error |
| 3 | BUS_ERR | W1C | Bus error |
| 4 | FAILED | W1C | Transaction failed |
| 5 | ALERT | W1C | SMBus alert received |
| 6 | TIMEOUT | W1C | Timeout occurred |
| 7 | PEC_ERR | W1C | PEC error |

---

## SMBUS_CONTROL (0x04)

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 2:0 | CMD_TYPE | RW | Command type |
| 3 | START | RW | Start transaction |
| 4 | PEC_EN | RW | Enable PEC |
| 5 | INTREN | RW | Enable interrupt |
| 6 | KILL | RW | Abort transaction |
| 7 | RESET | RW | Soft reset |

### Command Types

| CMD_TYPE | Description |
|----------|-------------|
| 000 | Quick Command |
| 001 | Send Byte |
| 010 | Receive Byte |
| 011 | Write Byte |
| 100 | Read Byte |
| 101 | Write Word |
| 110 | Read Word |
| 111 | Block Read/Write |

---

## SMBUS_ADDRESS (0x0C)

| Bits | Name | Description |
|------|------|-------------|
| 6:0 | ADDR | 7-bit slave address |
| 7 | RW | 0=Write, 1=Read |

---

**Back to:** [SMBus Specification Index](../smbus_index.md)
