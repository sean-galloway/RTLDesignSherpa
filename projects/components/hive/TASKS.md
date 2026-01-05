<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# HIVE Component - Task List

**Component:** HIVE (Hierarchical Integrated VexRiscv Environment)
**Last Updated:** 2025-10-19
**Version:** 0.25

---

## Task Status Legend

- 🔴 **Blocked** - Cannot proceed due to dependencies or issues
- 🟠 **In Progress** - Currently being worked on
- 🟡 **Planned** - Scheduled for upcoming work
- 🟢 **Complete** - Finished and verified

## Priority Levels

- **P0** - Critical path, blocks other work
- **P1** - High priority, needed for v0.25
- **P2** - Medium priority, nice to have
- **P3** - Low priority, future enhancement

---

## Active Tasks

### TASK-001: Complete Specification Chapter 2 (SERV Core)
**Status:** 🟠 In Progress
**Priority:** P0
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Complete detailed specification of the SERV bit-serial RISC-V core integration, including instruction fetch, decode, execute, and memory access.

**Acceptance Criteria:**
- [ ] Document SERV architecture and bit-serial execution
- [ ] Define instruction memory interface (ROM/RAM)
- [ ] Specify data memory interface (shared SRAM)
- [ ] Add SERV timing diagrams (bit-serial operation)
- [ ] Document CSR (Control and Status Register) access
- [ ] Include example instruction sequences

**Dependencies:**
- Chapter 1 (Overview) complete

**Related Files:**
- `docs/hive_spec/ch02_blocks/01_serv_core.md`

---

### TASK-002: Complete Specification Chapter 2 (VexRiscv Core)
**Status:** 🟠 In Progress
**Priority:** P0
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Complete detailed specification of the VexRiscv supervisor core, including pipeline stages, branch prediction, and interrupt handling.

**Acceptance Criteria:**
- [ ] Document VexRiscv 5-stage pipeline
- [ ] Define instruction and data cache configuration
- [ ] Specify interrupt controller interface
- [ ] Add pipeline timing diagrams
- [ ] Document supervisor mode capabilities
- [ ] Define SERV coordination mechanism

**Dependencies:**
- Chapter 1 (Overview) complete

**Related Files:**
- `docs/hive_spec/ch02_blocks/02_vexriscv_core.md`

---

### TASK-003: Complete Specification Chapter 3 (Memory Subsystem)
**Status:** 🟡 Planned
**Priority:** P0
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Document the shared memory subsystem including SRAM, ROM, and memory arbitration.

**Acceptance Criteria:**
- [ ] Define shared SRAM architecture (1 VexRiscv + 16 SERV access)
- [ ] Specify memory arbiter design (round-robin, priority)
- [ ] Document ROM configuration and initialization
- [ ] Add memory map and address decoding
- [ ] Include memory timing diagrams

**Dependencies:**
- TASK-001 (SERV spec)
- TASK-002 (VexRiscv spec)

**Related Files:**
- `docs/hive_spec/ch03_memory/01_memory_subsystem.md`

---

### TASK-004: Complete Specification Chapter 4 (Interconnect)
**Status:** 🟡 Planned
**Priority:** P0
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Document the interconnect fabric connecting VexRiscv, SERV cores, and peripherals.

**Acceptance Criteria:**
- [ ] Define AXI4-Lite crossbar topology
- [ ] Specify address routing and decoding
- [ ] Document arbitration policy
- [ ] Add interconnect block diagram
- [ ] Define peripheral address map

**Dependencies:**
- TASK-003 (Memory subsystem spec)

**Related Files:**
- `docs/hive_spec/ch04_interconnect/01_interconnect.md`

---

### TASK-005: Complete Specification Chapter 5 (System Integration)
**Status:** 🟡 Planned
**Priority:** P0
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Document top-level system integration, clocking, reset, and boot sequence.

**Acceptance Criteria:**
- [ ] Define boot sequence (VexRiscv → SERV initialization)
- [ ] Specify reset distribution
- [ ] Document clock domains and CDC (if any)
- [ ] Add system-level block diagram
- [ ] Define debug and trace interfaces

**Dependencies:**
- TASK-004 (Interconnect spec)

**Related Files:**
- `docs/hive_spec/ch05_integration/01_system_integration.md`

---

### TASK-006: SERV Core Integration
**Status:** 🟡 Planned
**Priority:** P0
**Effort:** 1 week
**Owner:** Unassigned

**Description:**
Integrate SERV bit-serial RISC-V core as submodule and create wrapper with AXI4-Lite interface.

**Acceptance Criteria:**
- [ ] Add SERV repository as git submodule
- [ ] Create serv_wrapper.sv with AXI4-Lite conversion
- [ ] Implement instruction memory interface
- [ ] Implement data memory interface
- [ ] Add configuration registers for SERV control
- [ ] Verify synthesizability with Verilator
- [ ] Document SERV integration in CLAUDE.md

**Dependencies:**
- TASK-001 (SERV spec)

**Related Files:**
- `rtl/hive/serv_wrapper.sv`
- `rtl/hive/serv/` (submodule)

---

### TASK-007: VexRiscv Core Integration
**Status:** 🟡 Planned
**Priority:** P0
**Effort:** 1 week
**Owner:** Unassigned

**Description:**
Integrate VexRiscv supervisor core and configure for HIVE system requirements.

**Acceptance Criteria:**
- [ ] Add VexRiscv repository as git submodule
- [ ] Create vexriscv_wrapper.sv with AXI4 interface
- [ ] Configure VexRiscv with appropriate plugins (interrupts, caches)
- [ ] Implement supervisor mode features
- [ ] Add SERV coordination logic
- [ ] Verify synthesizability
- [ ] Document VexRiscv configuration

**Dependencies:**
- TASK-002 (VexRiscv spec)

**Related Files:**
- `rtl/hive/vexriscv_wrapper.sv`
- `rtl/hive/VexRiscv/` (submodule)

---

### TASK-008: Shared Memory Subsystem RTL
**Status:** 🟡 Planned
**Priority:** P0
**Effort:** 4 days
**Owner:** Unassigned

**Description:**
Implement shared SRAM with multi-port arbiter for 1 VexRiscv + 16 SERV cores.

**Acceptance Criteria:**
- [ ] Implement hive_sram.sv (dual-port or banked SRAM)
- [ ] Implement hive_mem_arbiter.sv (17-to-1 arbiter)
- [ ] Add priority arbitration (VexRiscv > SERV)
- [ ] Implement round-robin among SERV cores
- [ ] Verify memory arbitration correctness
- [ ] Measure arbitration latency

**Dependencies:**
- TASK-003 (Memory subsystem spec)
- TASK-006 (SERV integration)
- TASK-007 (VexRiscv integration)

**Related Files:**
- `rtl/hive/hive_sram.sv`
- `rtl/hive/hive_mem_arbiter.sv`

---

### TASK-009: AXI4-Lite Interconnect RTL
**Status:** 🟡 Planned
**Priority:** P0
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Implement AXI4-Lite crossbar connecting VexRiscv, SERV cores, and peripherals.

**Acceptance Criteria:**
- [ ] Implement hive_interconnect.sv (AXI4-Lite crossbar)
- [ ] Add address decoder for peripheral routing
- [ ] Implement multi-master arbitration
- [ ] Support 1 VexRiscv + 16 SERV masters
- [ ] Support 4+ slave devices (SRAM, ROM, UART, GPIO)
- [ ] Verify interconnect with CocoTB

**Dependencies:**
- TASK-004 (Interconnect spec)

**Related Files:**
- `rtl/hive/hive_interconnect.sv`

---

### TASK-010: HIVE Top-Level Integration
**Status:** 🟡 Planned
**Priority:** P0
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Implement top-level HIVE module integrating all components.

**Acceptance Criteria:**
- [ ] Implement hive_top.sv with all core instantiations
- [ ] Add clock and reset distribution
- [ ] Implement boot ROM interface
- [ ] Add debug interface (JTAG or custom)
- [ ] Verify module hierarchy
- [ ] Create block diagram for documentation

**Dependencies:**
- TASK-006 (SERV integration)
- TASK-007 (VexRiscv integration)
- TASK-008 (Memory subsystem)
- TASK-009 (Interconnect)

**Related Files:**
- `rtl/hive/hive_top.sv`

---

### TASK-011: CocoTB SERV Core Testbench
**Status:** 🟡 Planned
**Priority:** P1
**Effort:** 4 days
**Owner:** Unassigned

**Description:**
Create comprehensive CocoTB testbench for SERV wrapper testing.

**Acceptance Criteria:**
- [ ] Create ServWrapperTB class in bin/CocoTBFramework/tbclasses/hive/
- [ ] Implement instruction memory loader
- [ ] Run basic RISC-V ISA tests (ADD, SUB, LOAD, STORE)
- [ ] Verify bit-serial execution timing
- [ ] Test CSR access
- [ ] Create test_serv_wrapper.py with >85% coverage

**Dependencies:**
- TASK-006 (SERV integration)

**Related Files:**
- `val/hive/test_serv_wrapper.py`
- `bin/CocoTBFramework/tbclasses/hive/serv_wrapper_tb.py`

---

### TASK-012: CocoTB VexRiscv Core Testbench
**Status:** 🟡 Planned
**Priority:** P1
**Effort:** 4 days
**Owner:** Unassigned

**Description:**
Create comprehensive CocoTB testbench for VexRiscv wrapper testing.

**Acceptance Criteria:**
- [ ] Create VexRiscvWrapperTB class
- [ ] Implement instruction/data cache BFMs
- [ ] Run RISC-V compliance tests
- [ ] Test interrupt handling
- [ ] Verify supervisor mode operations
- [ ] Create test_vexriscv_wrapper.py with >85% coverage

**Dependencies:**
- TASK-007 (VexRiscv integration)

**Related Files:**
- `val/hive/test_vexriscv_wrapper.py`
- `bin/CocoTBFramework/tbclasses/hive/vexriscv_wrapper_tb.py`

---

### TASK-013: CocoTB Memory Arbiter Testbench
**Status:** 🟡 Planned
**Priority:** P1
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Create testbench for shared memory arbiter with multiple master stimuli.

**Acceptance Criteria:**
- [ ] Create MemoryArbiterTB class
- [ ] Implement 17 AXI master BFMs
- [ ] Test priority arbitration (VexRiscv > SERV)
- [ ] Test round-robin among SERV cores
- [ ] Measure arbitration latency and fairness
- [ ] Create test_hive_mem_arbiter.py

**Dependencies:**
- TASK-008 (Memory arbiter implementation)

**Related Files:**
- `val/hive/test_hive_mem_arbiter.py`
- `bin/CocoTBFramework/tbclasses/hive/mem_arbiter_tb.py`

---

### TASK-014: CocoTB System Integration Testbench
**Status:** 🟡 Planned
**Priority:** P1
**Effort:** 1 week
**Owner:** Unassigned

**Description:**
Create end-to-end HIVE system testbench with VexRiscv supervising 16 SERV cores.

**Acceptance Criteria:**
- [ ] Create HiveSystemTB class
- [ ] Load boot ROM with VexRiscv supervisor code
- [ ] Load SERV programs (parallel tasks)
- [ ] Test VexRiscv → SERV task dispatch
- [ ] Verify shared memory access coordination
- [ ] Measure system throughput
- [ ] Create test_hive_system_integration.py

**Dependencies:**
- TASK-010 (HIVE top-level)
- TASK-011 (SERV testbench)
- TASK-012 (VexRiscv testbench)
- TASK-013 (Arbiter testbench)

**Related Files:**
- `val/hive/test_hive_system_integration.py`
- `bin/CocoTBFramework/tbclasses/hive/hive_system_tb.py`

---

### TASK-015: Software Toolchain Setup
**Status:** 🟡 Planned
**Priority:** P1
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Set up RISC-V GCC toolchain and example programs for HIVE testing.

**Acceptance Criteria:**
- [ ] Install RISC-V GCC (riscv32-unknown-elf)
- [ ] Create linker script for HIVE memory map
- [ ] Write simple test programs (hello world, task dispatch)
- [ ] Create Makefile for building SERV and VexRiscv binaries
- [ ] Document toolchain setup in CLAUDE.md

**Dependencies:**
- TASK-010 (HIVE top-level) - for memory map

**Related Files:**
- `sw/hive/linker.ld`
- `sw/hive/Makefile`
- `sw/hive/examples/hello_world.c`

---

### TASK-016: Wavedrom Timing Diagrams
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Create wavedrom JSON files illustrating key HIVE operations.

**Acceptance Criteria:**
- [ ] Create serv_bit_serial_execution.json (SERV bit-serial ADD)
- [ ] Create vexriscv_pipeline.json (VexRiscv 5-stage pipeline)
- [ ] Create mem_arbiter_priority.json (VexRiscv priority access)
- [ ] Create mem_arbiter_round_robin.json (SERV round-robin)
- [ ] Create boot_sequence.json (VexRiscv boot → SERV init)
- [ ] Generate SVG/PNG from all JSON files
- [ ] Place in docs/hive_spec/assets/waves/

**Dependencies:**
- None (can start anytime)

**Related Files:**
- `docs/hive_spec/assets/waves/*.json`

---

### TASK-017: PlantUML FSM Diagrams
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Create PlantUML state machine diagrams for HIVE FSMs.

**Acceptance Criteria:**
- [ ] Create mem_arbiter_fsm.puml
- [ ] Create boot_controller_fsm.puml
- [ ] Create serv_state_machine.puml (if applicable)
- [ ] Generate PNG/SVG from all PUML files
- [ ] Place in docs/hive_spec/assets/puml/

**Dependencies:**
- TASK-008 (Memory arbiter) - for accurate FSMs

**Related Files:**
- `docs/hive_spec/assets/puml/*.puml`

---

### TASK-018: Block Diagrams and Architecture Images
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Create block diagrams and architecture illustrations for specification.

**Acceptance Criteria:**
- [ ] Create hive_system_architecture.svg (top-level block diagram)
- [ ] Create serv_core_architecture.svg (SERV internals)
- [ ] Create vexriscv_pipeline_diagram.svg (pipeline stages)
- [ ] Create memory_hierarchy.svg (memory subsystem)
- [ ] Create interconnect_topology.svg (AXI crossbar)
- [ ] Place in docs/hive_spec/assets/images/

**Dependencies:**
- None (can use draw.io or similar tools)

**Related Files:**
- `docs/hive_spec/assets/images/*.svg`

---

## Recently Completed Tasks

### ✅ TASK-000: Initial Specification Structure (Complete - 2025-10-15)
- Created specification chapter outline (Ch1-5)
- Completed Chapter 1 (Overview, Architectural Requirements, Clocks/Reset, Acronyms, References)
- Created initial PRD.md and CLAUDE.md
- Established documentation infrastructure
- Added documentation generation support (md_to_docx.py)

---

## Future Enhancements (Backlog)

### TASK-019: Performance Monitoring
**Priority:** P3
**Description:** Add performance counters for instruction throughput, memory access latency, and arbitration statistics.

### TASK-020: Hardware Task Scheduler
**Priority:** P3
**Description:** Implement hardware task queue and dispatcher to reduce VexRiscv overhead in task management.

### TASK-021: DMA Support
**Priority:** P3
**Description:** Add DMA controller for efficient memory transfers without CPU intervention.

### TASK-022: Peripheral Integration
**Priority:** P3
**Description:** Add standard peripherals (UART, GPIO, SPI, I2C) connected via AXI4-Lite.

### TASK-023: Debugging Infrastructure
**Priority:** P3
**Description:** Implement JTAG debug interface and trace buffer for development support.

### TASK-024: Power Management
**Priority:** P3
**Description:** Add clock gating and power domains for idle SERV cores.

---

## Task Dependencies

```
TASK-001 (Ch2 SERV Spec)
    └─> TASK-006 (SERV Integration)
            └─> TASK-008 (Memory Subsystem)
            └─> TASK-011 (SERV Testbench)

TASK-002 (Ch2 VexRiscv Spec)
    └─> TASK-007 (VexRiscv Integration)
            └─> TASK-008 (Memory Subsystem)
            └─> TASK-012 (VexRiscv Testbench)

TASK-003 (Ch3 Memory Spec)
    └─> TASK-008 (Memory Subsystem)
            └─> TASK-013 (Arbiter Testbench)

TASK-004 (Ch4 Interconnect Spec)
    └─> TASK-009 (Interconnect RTL)

TASK-005 (Ch5 Integration Spec)
    └─> TASK-010 (HIVE Top-Level)
            └─> TASK-014 (System Integration Test)
            └─> TASK-015 (Software Toolchain)

TASK-016 (Wavedrom) - Independent
TASK-017 (PlantUML) - Independent
TASK-018 (Block Diagrams) - Independent
```

---

## Quick Commands

### Run Specification to PDF
```bash
python bin/md_to_docx.py \
    projects/components/hive/docs/hive_spec/hive_index.md \
    -o projects/components/hive/docs/HIVE_Specification_v0.25.docx \
    --toc --title-page --pdf
```

### Run SERV Tests (when available)
```bash
pytest val/hive/test_serv_wrapper.py -v
```

### Run System Integration Tests (when available)
```bash
pytest val/hive/test_hive_system_integration.py -v
```

### Build RISC-V Test Programs (when available)
```bash
cd sw/hive
make all
```

### Lint HIVE RTL (when available)
```bash
verilator --lint-only rtl/hive/hive_top.sv
```

### Generate Wavedrom SVG
```bash
wavedrom-cli -i docs/hive_spec/assets/waves/serv_bit_serial_execution.json \
             -s docs/hive_spec/assets/waves/serv_bit_serial_execution.svg
```

### Generate PlantUML PNG
```bash
plantuml docs/hive_spec/assets/puml/mem_arbiter_fsm.puml
```

---

**Last Review:** 2025-10-19
**Next Review:** Weekly during active development
