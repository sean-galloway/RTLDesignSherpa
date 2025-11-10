# I/O Advanced Programmable Interrupt Controller (IOAPIC)

**Status:** 📋 Planned - Structure Created
**Priority:** Medium
**Address:** `0x4000_6000 - 0x4000_6FFF` (4KB window)

---

## Overview

I/O APIC CSR model (register-based interface) for advanced interrupt routing.

## Planned Features

- I/O APIC CSR model (register-based interface)
- Multiple interrupt inputs (24+)
- Programmable interrupt routing
- Edge and level triggered modes
- Priority-based arbitration
- Interrupt masking per input
- APB register interface for configuration
- Redirection table entries

## Applications

- Advanced interrupt routing
- Multi-processor interrupt distribution
- Flexible interrupt mapping
- Legacy IRQ redirection
- PC-compatible systems
- System interrupt aggregation

## Files (To Be Created)

- `apb_ioapic.sv` - Top-level wrapper with APB interface
- `ioapic_core.sv` - Core IOAPIC logic
- `ioapic_routing.sv` - Interrupt routing logic
- `ioapic_arbiter.sv` - Priority arbitration logic
- `ioapic_config_regs.sv` - Register wrapper
- `ioapic_regs.sv` - PeakRDL generated registers
- `ioapic_regs_pkg.sv` - PeakRDL generated package

## Development Status

- [ ] SystemRDL register specification
- [ ] Interrupt routing logic implementation
- [ ] Priority arbitration logic
- [ ] Redirection table implementation
- [ ] Core IOAPIC logic implementation
- [ ] APB wrapper
- [ ] Basic testbench
- [ ] Medium testbench
- [ ] Full testbench
- [ ] Documentation

---

**Last Updated:** 2025-10-29
