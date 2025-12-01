# Chapter 3: External Interfaces

This chapter documents the external interfaces of the STREAM DMA engine (stream_top_ch8.sv).

## Interface Specifications

STREAM has seven primary external interfaces:

### 01_axi4_interface_spec.md
- **AXI4 Master Interfaces (3 total)**
  - Descriptor fetch (256-bit, read-only)
  - Data read (parameterizable, default 512-bit)
  - Data write (parameterizable, default 512-bit)
- Protocol specifications and assumptions
- Transfer modes and alignment requirements
- Timing and performance characteristics

### 02_axil4_interface_spec.md
- **AXI4-Lite Interfaces (2 total, in monbus_axil_group)**
  - Error FIFO slave read (s_axil_err_*): 32-bit, read-only
  - Monitor data master write (m_axil_mon_*): 32-bit, write-only
- Used for monitor bus packet access and logging
- Part of monbus_axil_group integration (USE_AXI_MONITORS=1)

### 03_apb_interface_spec.md
- **APB4 Slave Interface**
- Full APB4 protocol with PSEL/PENABLE
- Optional CDC for asynchronous clock domains (CDC_ENABLE parameter)
- Address map: 0x000-0x03F kick-off, 0x100-0x3FF registers

### 05_monbus_interface_spec.md
- **MonBus Internal Protocol**
- Unified 64-bit monitoring bus (stream_core → monbus_axil_group)
- Event packet format and encoding
- Agent ID assignments for STREAM components
- Converted to AXI-Lite at top level

---

## STREAM Interface Summary (stream_top_ch8.sv)

| Interface | Type | Direction | Width | Purpose |
|-----------|------|-----------|-------|---------|
| APB4 | Slave | Input | 32-bit data, 12-bit addr | Configuration and kick-off |
| AXI4 Descriptor | Master Read | Output | 256-bit | Descriptor fetch |
| AXI4 Data Read | Master Read | Output | 512-bit (param) | Source data read |
| AXI4 Data Write | Master Write | Output | 512-bit (param) | Destination data write |
| AXIL Error FIFO | Slave Read | Input | 32-bit | Monitor error/interrupt FIFO |
| AXIL Monitor Write | Master Write | Output | 32-bit | Monitor data to memory |
| IRQ | Output | Output | 1-bit | Interrupt (error FIFO not empty) |

**Note:** AXIL interfaces are active when USE_AXI_MONITORS=1. MonBus is internal (stream_core → monbus_axil_group).

---

**Last Updated:** 2025-12-01

**Dependencies:**
- AMBA AXI4 Protocol Specification v4.0
- AMBA Monitor Bus Protocol (internal spec)
- STREAM Architecture Overview
