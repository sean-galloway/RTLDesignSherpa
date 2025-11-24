# Chapter 3: External Interfaces

This chapter documents the external interfaces of the STREAM DMA engine.

## Interface Specifications

STREAM has five primary external interfaces:

### 01_axi4_interface_spec.md
- **AXI4 Master Interfaces (3 total)**
  - Descriptor fetch (256-bit, read-only)
  - Data read (parameterizable, default 512-bit)
  - Data write (parameterizable, default 512-bit)
- Protocol specifications and assumptions
- Transfer modes and alignment requirements
- Timing and performance characteristics

### 02_axil4_interface_spec.md
- **AXI4-Lite Master Interface (Future)**
- Used for MonBus packet logging to memory
- 32-bit data width
- Part of monbus_axil_group integration

### 03_apb_interface_spec.md
- **APB Programming Interface**
- Simplified per-channel descriptor kick-off
- Valid/ready handshake protocol
- Not a full APB slave (no PSEL/PENABLE)

### 05_monbus_interface_spec.md
- **MonBus Output Protocol**
- Unified 64-bit monitoring bus
- Event packet format and encoding
- Agent ID assignments for STREAM components
- Integration with downstream consumers

---

## STREAM Interface Summary

| Interface | Type | Direction | Width | Purpose |
|-----------|------|-----------|-------|---------|
| APB Programming | Custom | Input | 64-bit addr × 8 ch | Descriptor kick-off |
| AXI4 Descriptor | Master Read | Output | 256-bit | Descriptor fetch |
| AXI4 Data Read | Master Read | Output | 512-bit (param) | Source data read |
| AXI4 Data Write | Master Write | Output | 512-bit (param) | Destination data write |
| MonBus | Monitor Bus | Output | 64-bit | Event reporting |

**Note:** AXIL4 interface is part of the optional monbus_axil_group and not directly exposed at the STREAM Core level.

---

**Last Updated:** 2025-11-22

**Dependencies:**
- AMBA AXI4 Protocol Specification v4.0
- AMBA Monitor Bus Protocol (internal spec)
- STREAM Architecture Overview
