# SMBus 2.0 PeakRDL Register Specification

This directory contains the SystemRDL specification for the SMBus 2.0 controller configuration registers.

## Files

- `smbus_regs.rdl` - SystemRDL register specification

## Generated Files

The following files are generated from the RDL specification using PeakRDL tools and are placed in the parent directory:

- `../smbus_regs.sv` - SystemVerilog register implementation
- `../smbus_regs_pkg.sv` - SystemVerilog package with register addresses and field definitions

## Generation Command

To generate the SystemVerilog files from the RDL specification:

```bash
cd $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/smbus
peakrdl regblock peakrdl/smbus_regs.rdl -o smbus_regs.sv --cpuif apb4-flat
```

## Register Map Overview

| Offset | Register | Access | Description |
|--------|----------|--------|-------------|
| 0x000  | SMBUS_CONTROL | RW | Global control (master/slave/PEC enable) |
| 0x004  | SMBUS_STATUS | R | Status flags (busy, errors, FSM state) |
| 0x008  | SMBUS_COMMAND | RW | Transaction command and trigger |
| 0x00C  | SMBUS_SLAVE_ADDR | RW | Target slave address |
| 0x010  | SMBUS_DATA | RW | Single byte data register |
| 0x014  | SMBUS_TX_FIFO | W | Transmit FIFO write port |
| 0x018  | SMBUS_RX_FIFO | R | Receive FIFO read port |
| 0x01C  | SMBUS_FIFO_STATUS | R | TX/RX FIFO levels and flags |
| 0x020  | SMBUS_CLK_DIV | RW | Clock divider configuration |
| 0x024  | SMBUS_TIMEOUT | RW | Timeout threshold (25-35ms) |
| 0x028  | SMBUS_OWN_ADDR | RW | Own slave address (slave mode) |
| 0x02C  | SMBUS_INT_ENABLE | RW | Interrupt enable mask |
| 0x030  | SMBUS_INT_STATUS | RW | Interrupt status (W1C) |
| 0x034  | SMBUS_PEC | RW | PEC value (CRC-8) |
| 0x038  | SMBUS_BLOCK_COUNT | RW | Block transfer byte count |

## SMBus 2.0 Features

- **Transaction Types**: Quick, Send/Receive Byte, Read/Write Byte/Word, Block Read/Write
- **Master Mode**: Full master operation with all transaction types
- **Slave Mode**: Address recognition and response
- **PEC**: Packet Error Checking using CRC-8 (polynomial 0x07)
- **FIFOs**: 32-byte TX and RX FIFOs for block transfers
- **Clock Speeds**: Standard (100kHz) and Fast (400kHz) modes
- **Timeout**: Configurable timeout detection (25-35ms per spec)
- **Interrupts**: Transaction complete, errors, FIFO thresholds, slave addressed

## Transaction Types (COMMAND.trans_type)

| Value | Transaction Type | Description |
|-------|-----------------|-------------|
| 0 | Quick Command | 0 bytes, command only |
| 1 | Send Byte | 1 byte, no command code |
| 2 | Receive Byte | 1 byte read, no command code |
| 3 | Write Byte | 1 command + 1 data byte |
| 4 | Read Byte | 1 command + 1 data byte read |
| 5 | Write Word | 1 command + 2 data bytes |
| 6 | Read Word | 1 command + 2 data bytes read |
| 7 | Block Write | 1 command + count + data block |
| 8 | Block Read | 1 command + count + data block read |
| 9 | Block Process Call | Block write + block read |

## Usage Notes

### Master Mode Transaction Sequence:
1. Configure clock divider (SMBUS_CLK_DIV)
2. Enable master mode (SMBUS_CONTROL.master_en)
3. Set target slave address (SMBUS_SLAVE_ADDR)
4. For block transfers: Load TX FIFO, set block count
5. Set transaction type (SMBUS_COMMAND.trans_type)
6. Set command code if needed (SMBUS_COMMAND.cmd_code)
7. Start transaction (SMBUS_COMMAND.start = 1)
8. Wait for complete or error interrupt
9. For reads: Read RX FIFO or DATA register

### Slave Mode Configuration:
1. Set own address (SMBUS_OWN_ADDR.own_addr)
2. Enable own address (SMBUS_OWN_ADDR.addr_en)
3. Enable slave mode (SMBUS_CONTROL.slave_en)
4. Enable slave addressed interrupt (SMBUS_INT_ENABLE.slave_addr_en)
5. Respond to address match events

### PEC (Packet Error Checking):
1. Enable PEC (SMBUS_CONTROL.pec_en)
2. PEC automatically calculated during transaction
3. Check SMBUS_STATUS.pec_error after transaction
4. Read calculated PEC from SMBUS_PEC if needed

### Clock Configuration:
- Standard mode (100kHz): `clk_div = (sys_clk_hz / 400000) - 1`
  - Example @ 100MHz: clk_div = 249
- Fast mode (400kHz): `clk_div = (sys_clk_hz / 1600000) - 1`
  - Example @ 100MHz: clk_div = 61

## Integration Pattern

This SMBus controller follows the standard 3-layer architecture:

```
Layer 1: apb_smbus.sv           (APB4 interface)
         ↓
Layer 2: smbus_config_regs.sv   (Register wrapper + FIFOs)
         ↓
Layer 3: smbus_core.sv          (Protocol engine)
         ├─ smbus_master.sv     (Master FSM)
         ├─ smbus_slave.sv      (Slave FSM)
         ├─ smbus_phy.sv        (SCL/SDA physical layer)
         └─ smbus_pec.sv        (CRC-8 calculator)
```

The generated PeakRDL files are instantiated in `smbus_config_regs.sv`.

## SMBus 2.0 Timing Requirements

### Standard Mode (100 kHz):
- SCL low time (tLOW): min 4.7 µs
- SCL high time (tHIGH): min 4.0 µs
- Data setup time (tSU:DAT): min 250 ns
- Data hold time (tHD:DAT): min 300 ns
- Bus free time (tBUF): min 4.7 µs
- Timeout: 25-35 ms

### Fast Mode (400 kHz):
- SCL low time (tLOW): min 1.3 µs
- SCL high time (tHIGH): min 0.6 µs
- Data setup time (tSU:DAT): min 100 ns
- Data hold time (tHD:DAT): min 300 ns
