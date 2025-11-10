# SMBus Controller

**Status:** 📋 Planned - Structure Created
**Priority:** Medium
**Address:** `0x4000_4000 - 0x4000_4FFF` (4KB window)

---

## Overview

SMBus 2.0 compliant System Management Bus Controller with APB interface.

## Planned Features

- SMBus 2.0 compliance
- Master and slave modes
- Clock stretching support
- Packet Error Checking (PEC)
- Alert response address
- Configurable clock speed (10 kHz - 100 kHz)
- APB register interface
- FIFO buffers for TX/RX

## Applications

- System management bus communication
- Sensor interfaces (temperature, voltage)
- EEPROM access
- Battery management
- Fan control
- Platform management

## Files (To Be Created)

- `apb_smbus.sv` - Top-level wrapper with APB interface
- `smbus_core.sv` - Core SMBus protocol logic
- `smbus_master.sv` - Master mode logic
- `smbus_slave.sv` - Slave mode logic
- `smbus_config_regs.sv` - Register wrapper
- `smbus_regs.sv` - PeakRDL generated registers
- `smbus_regs_pkg.sv` - PeakRDL generated package

## Development Status

- [ ] SystemRDL register specification
- [ ] SMBus protocol implementation
- [ ] Master mode logic
- [ ] Slave mode logic (optional)
- [ ] Core SMBus logic implementation
- [ ] APB wrapper
- [ ] Basic testbench
- [ ] Medium testbench
- [ ] Full testbench
- [ ] Documentation

---

**Last Updated:** 2025-10-29
