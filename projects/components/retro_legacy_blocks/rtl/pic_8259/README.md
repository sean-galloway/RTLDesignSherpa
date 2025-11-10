# 8259 Programmable Interrupt Controller (PIC)

**Status:** 📋 Planned - Structure Created
**Priority:** High
**Address:** `0x4000_1000 - 0x4000_1FFF` (4KB window)

---

## Overview

Intel 8259A-compatible Programmable Interrupt Controller with APB interface.

## Planned Features

- Intel 8259A-compatible register interface
- 8 interrupt request (IRQ) inputs
- Cascadable (master/slave configuration)
- Priority resolver (fixed and rotating priority)
- Edge and level triggered modes
- Interrupt mask register
- End-of-Interrupt (EOI) handling
- APB register interface

## Applications

- Legacy interrupt management
- PC-compatible systems
- Hardware interrupt aggregation
- Priority-based interrupt handling
- Cascaded multi-level interrupt systems

## Files (To Be Created)

- `apb_pic_8259.sv` - Top-level wrapper with APB interface
- `pic_8259_core.sv` - Core PIC logic
- `pic_8259_config_regs.sv` - Register wrapper
- `pic_8259_regs.sv` - PeakRDL generated registers
- `pic_8259_regs_pkg.sv` - PeakRDL generated package

## Development Status

- [ ] SystemRDL register specification
- [ ] Core PIC logic implementation
- [ ] APB wrapper
- [ ] Basic testbench
- [ ] Medium testbench
- [ ] Full testbench
- [ ] Documentation

---

**Last Updated:** 2025-10-29
