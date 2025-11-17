# Chapter 3: External Interfaces

This chapter documents the external interfaces of the STREAM DMA engine.

## Planned Contents

### 01_apb_interface.md
- APB slave configuration interface
- Register access protocol
- Timing diagrams
- Example transactions

### 02_axi_descriptor_interface.md
- Descriptor fetch AXI master
- 256-bit read-only interface
- Burst patterns
- Error handling

### 03_axi_data_read_interface.md
- Data read AXI master
- Parameterizable width (512-bit typical)
- Multi-channel arbitration
- Performance modes

### 04_axi_data_write_interface.md
- Data write AXI master
- Parameterizable width (512-bit typical)
- Multi-channel arbitration
- Backpressure handling

### 05_monbus_interface.md
- MonBus output protocol
- Event packet format
- Agent ID assignment
- Integration guidelines

### 06_interrupt_interface.md
- IRQ output signals
- Interrupt conditions
- Masking and clearing
- Software handling

---

**Status:** TBD - To be created during detailed documentation phase

**Dependencies:**
- APB specification (AMBA APB Protocol v2.0)
- AXI4 specification (AMBA AXI Protocol v4.0)
- MonBus specification (internal monitoring protocol)
