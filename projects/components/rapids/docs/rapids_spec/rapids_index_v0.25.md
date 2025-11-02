# RAPIDS (Rapid AXI Programmable In-band Descriptor System) Specification

**Version:** 0.25
**Date:** 2025-10-18
**Status:** AXIS Migration Complete

---

## Chapter 1: Block Descriptions

- [Overview](ch02_blocks/00_overview.md)

### Scheduler Group

- [Scheduler Group](ch02_blocks/01_00_scheduler_group.md)
- [Scheduler](ch02_blocks/01_01_scheduler.md)
- [Descriptor Engine](ch02_blocks/01_02_descriptor_engine.md)
- [Control Write Engine](ch02_blocks/01_03_ctrlwr_engine.md)
- [Control Read Engine](ch02_blocks/01_04_ctrlrd_engine.md)
- [Scheduler Group Array](ch02_blocks/01_05_scheduler_group_array.md)

### Sink Data Path (Network -> Memory)

- [Sink Data Path Overview](ch02_blocks/02_00_sink_data_path.md)
- [AXIS Slave Interface](ch02_blocks/02_01_axis_slave.md)
- [Sink SRAM Controller](ch02_blocks/02_02_sink_sram_control.md)
- [Sink AXI4 Write Engine](ch02_blocks/02_03_sink_axi_write_engine.md)

### Source Data Path (Memory -> Network)

- [Source Data Path Overview](ch02_blocks/03_00_source_data_path.md)
- [AXIS Master Interface](ch02_blocks/03_01_axis_master.md)
- [Source SRAM Controller](ch02_blocks/03_02_source_sram_control.md)
- [Source AXI4 Read Engine](ch02_blocks/03_03_source_axi_read_engine.md)

### MonBus AXIL Group

- [MonBus AXIL Group](ch02_blocks/04_monbus_axil_group.md)

### FSM Summary

- [FSM Summary Table](ch02_blocks/05_fsm_summary_table.md)

---

## Chapter 2: Interfaces and Busses

### Top-Level Ports

- [RAPIDS Top-Level Interface](ch03_interfaces/01_top_level.md)

### Bus Specifications

- [AXI4-Lite (AXIL4) Control Interface](ch03_interfaces/02_axil4_interface_spec.md)
- [AXI4 Memory Interface](ch03_interfaces/03_axi4_interface_spec.md)
- [AXI4-Stream (AXIS4) Network Interface](ch03_interfaces/04_axis4_interface_spec.md)
- [Monitor Bus (MONBUS)](ch03_interfaces/05_monbus_interface_spec.md)

---

## Chapter 3: Programming Model

- [RAPIDS Programming Model and Registers](ch04_programming_models/01_programming.md)

---

## Chapter 4: Register Definitions

- [Register Map and Descriptions](ch05_registers/01_registers.md)

---

## Appendices

### Migration Notes

**Version 0.25 Changes:**
- [PASS] Migrated from custom network protocol to AXI4-Stream (AXIS)
- [PASS] Removed credit return logic (AXIS native backpressure)
- [PASS] Optimized SRAM storage format (EOS handling, TSTRB conversion)
- [PASS] Updated monitor event codes for AXIS protocol
- [PASS] Renamed network_slave/master to axis_slave/master

### Legacy Documentation (Deprecated)

The following files reference the old network protocol and are retained for historical reference only:
- [Network Slave (Legacy)](ch02_blocks/02_01_network_slave.md)
- [Network Master (Legacy)](ch02_blocks/03_01_network_master.md)
- [APB Interface (Replaced by AXIL4)](ch03_interfaces/apb_interface_spec.md)

---

**Document Generated:** 2025-10-18
**Generator:** `md_to_docx.py`
**Source:** `projects/components/rapids/docs/rapids_spec/`
