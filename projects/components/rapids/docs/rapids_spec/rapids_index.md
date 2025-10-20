# Memory IO Processor (RAPIDS) Specification

## Chapter 1: Overview

- [Overview](ch01_overview/01_overview.md)
- [Architecture Requirements](ch01_overview/02_architectural_requirements.md)
- [Clocking and Reset](ch01_overview/03_clocks_and_reset.md)
- [Acronyms and Abbreviations](ch01_overview/04_acronyms.md)
- [References](ch01_overview/05_references.md)

## Chapter 2: Blocks

- [Overview](ch02_blocks/00_overview.md)

### Scheduler Group 

- [Scheduler Group](ch02_blocks/01_00_scheduler_group.md)
- [Scheduler](ch02_blocks/01_01_scheduler.md)
- [Descriptor Engine](ch02_blocks/01_02_descriptor_engine.md)
- [Program Write Engine](ch02_blocks/01_03_program_write_engine.md)

### Sink Data Path

- [Sink Data Path](ch02_blocks/02_00_sink_data_path.md)
- [Network Slave](ch02_blocks/02_01_network_slave.md)
- [Sink SRAM Controller](ch02_blocks/02_02_sink_sram_control.md)
- [Sink AXI4 Write Engine](ch02_blocks/02_03_sink_axi_write_engine.md)

### Source Data Path

- [Source Data Path](ch02_blocks/03_00_source_data_path.md)
- [Network Master](ch02_blocks/05_source_data_path.md)
- [Source SRAM Controller](ch02_blocks/05_source_data_path.md)
- [Source AXI4 Read Engine](ch02_blocks/05_source_data_path.md)

### MonBus AXIL Group

- [MonBus AXIL Group](ch02_blocks/04_monbus_axil_group.md)

### FSM Summary

- [FSM Summary](ch02_blocks/05_fsm_summary_table.md)

## Chapter 3: Interfaces and Busses

### Top-Level Ports

- [RAPIDS Ports](ch03_interfaces/01_top_level.md)

### Bus Definitions

- [AXIL4](ch03_interfaces/02_axil4_interface_spec.md)
- [AXI4](ch03_interfaces/03_axi4_interface_spec.md)
- [AXIS4 (AXI4-Stream)](ch03_interfaces/04_axis4_interface_spec.md)
- [MONBUS](ch03_interfaces/05_monbus_interface_spec.md)

## Chapter 4: Programming Models

- [RAPIDS Registers](ch04_programming_models/01_programming.md)

## Chapter 5: Registers

- [RAPIDS Registers](ch05_registers/registers.md)
