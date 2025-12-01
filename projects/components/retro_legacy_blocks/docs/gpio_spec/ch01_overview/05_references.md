# APB GPIO - References

## Internal Documentation

### RTL Source Files
- `rtl/gpio/apb_gpio.sv` - Main GPIO module
- `rtl/gpio/apb_gpio_regs.sv` - PeakRDL-generated register file
- `rtl/gpio/apb_gpio.rdl` - Register description source

### Related Specifications
- APB Protocol Specification (AMBA 3)
- RLB Integration Guide

## External References

### ARM AMBA Specifications
- **AMBA 3 APB Protocol Specification**
  - ARM IHI 0024E
  - Defines APB interface timing and protocol

### Industry Standards
- **GPIO Best Practices**
  - Synchronization for external inputs
  - Interrupt handling patterns
  - Tri-state buffer management

## Design References

### Clock Domain Crossing
- Dual flip-flop synchronizer methodology
- Skid buffer for data path CDC
- Reset synchronization techniques

### Interrupt Handling
- Edge detection circuits
- Interrupt aggregation patterns
- Software interrupt acknowledge flows

---

**Next:** [Chapter 2: Block Descriptions](../ch02_blocks/00_overview.md)
