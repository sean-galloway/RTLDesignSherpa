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

# Product Requirements Document (PRD)
## RAPIDS - Rapid AXI Programmable In-band Descriptor System

**Version:** 1.0
**Date:** 2025-09-30
**Status:** Active Development - Validation in Progress
**Owner:** RTL Design Sherpa Project
**Parent Document:** `/PRD.md`

---

## 1. Executive Summary

The Rapid AXI Programmable In-band Descriptor System (RAPIDS) is a custom hardware accelerator designed for efficient memory-to-memory data movement with network interface integration. It demonstrates complex FSM coordination, descriptor-based DMA operations, and comprehensive monitoring capabilities.

> **Status (2026-07-22):** RAPIDS was rearchitected to the "beats" design. Current RTL is in
> `rtl/fub_beats/`, `rtl/macro_beats/`, `rtl/top_beats/` (control engines in `rtl/fub/`);
> current specs are `docs/rapids_beats_has/` and `docs/rapids_beats_mas/`. The old
> `rapids_fub/`/`rapids_macro/` RTL, the `docs/rapids_spec/` tree, and the program engine /
> network master / network slave blocks described in parts of this PRD were retired
> (network interfaces are now AXIS; control is APB). Sections describing the pre-beats
> design are kept as history and marked where practical.

### 1.1 Quick Stats

- **Modules:** ~20 SystemVerilog files (beats architecture)
- **Architecture:** 3 major groups (Scheduler group, Sink path, Source path)
- **Interfaces:** AXI4 (memory), AXIS (network), APB (control), MonBus (monitoring)
- **Test Coverage:** see `dv/tests/` beats suites (fub_beats/macro_beats/top_beats)
- **Status:** Active validation, known issues documented

### 1.2 Subsystem Goals

- **Primary:** Demonstrate complex accelerator design patterns
- **Secondary:** Provide DMA-style memory transfer capability
- **Tertiary:** Educational reference for descriptor-based engines

---

## 2. Documentation Structure

This PRD provides a high-level overview. **Detailed specifications are maintained separately:**

### 📚 Complete RAPIDS Specification

> **Status (2026-07-22):** The old `docs/rapids_spec/` tree was replaced by two beats spec trees.

**Architecture Spec (HAS):** `docs/rapids_beats_has/`

- **[HAS Index](docs/rapids_beats_has/rapids_beats_has_index.md)** - Complete HAS structure
- [Product Overview](docs/rapids_beats_has/ch01_overview/01_product_overview.md)
- [Block Diagram](docs/rapids_beats_has/ch02_architecture/01_block_diagram.md) / [Data Flow](docs/rapids_beats_has/ch02_architecture/02_data_flow.md) / [Channel Architecture](docs/rapids_beats_has/ch02_architecture/03_channel_architecture.md)
- Interfaces: [Summary](docs/rapids_beats_has/ch03_interfaces/01_interface_summary.md), [AXI4](docs/rapids_beats_has/ch03_interfaces/02_axi4_interface.md), [AXIS](docs/rapids_beats_has/ch03_interfaces/03_axis_interface.md), [APB](docs/rapids_beats_has/ch03_interfaces/04_apb_interface.md), [MonBus](docs/rapids_beats_has/ch03_interfaces/05_monbus_interface.md)
- Use cases: `docs/rapids_beats_has/ch04_use_cases/`
- Programming: [Descriptor Format](docs/rapids_beats_has/ch05_programming/01_descriptor_format.md), [Register Map](docs/rapids_beats_has/ch05_programming/02_register_map.md), [Initialization](docs/rapids_beats_has/ch05_programming/03_initialization.md), [Error Handling](docs/rapids_beats_has/ch05_programming/04_error_handling.md)
- Performance: `docs/rapids_beats_has/ch06_performance/`

**Micro-Architecture Spec (MAS):** `docs/rapids_beats_mas/`

- **[MAS Index](docs/rapids_beats_mas/rapids_beats_mas_index.md)** - Complete MAS structure
- Overview: [Architecture](docs/rapids_beats_mas/ch01_overview/01_architecture.md), [Port List](docs/rapids_beats_mas/ch01_overview/02_port_list.md), [Clocks and Reset](docs/rapids_beats_mas/ch01_overview/03_clocks_and_reset.md)

**FUB blocks (`docs/rapids_beats_mas/ch02_fub_blocks/`):**
- [Scheduler](docs/rapids_beats_mas/ch02_fub_blocks/01_scheduler.md) - Per-channel scheduler FSM
- [Descriptor Engine](docs/rapids_beats_mas/ch02_fub_blocks/02_descriptor_engine.md) - Descriptor fetch/parsing
- [AXI Read Engine](docs/rapids_beats_mas/ch02_fub_blocks/03_axi_read_engine.md) / [AXI Write Engine](docs/rapids_beats_mas/ch02_fub_blocks/04_axi_write_engine.md)
- [Alloc Ctrl](docs/rapids_beats_mas/ch02_fub_blocks/05_beats_alloc_ctrl.md) / [Drain Ctrl](docs/rapids_beats_mas/ch02_fub_blocks/06_beats_drain_ctrl.md) / [Latency Bridge](docs/rapids_beats_mas/ch02_fub_blocks/07_beats_latency_bridge.md)
- [CtrlRd Engine](docs/rapids_beats_mas/ch02_fub_blocks/08_ctrlrd_engine.md) / [CtrlWr Engine](docs/rapids_beats_mas/ch02_fub_blocks/09_ctrlwr_engine.md)

**Macro blocks (`docs/rapids_beats_mas/ch03_macro_blocks/`):**
- [Scheduler Group](docs/rapids_beats_mas/ch03_macro_blocks/01_beats_scheduler_group.md) / [Scheduler Group Array](docs/rapids_beats_mas/ch03_macro_blocks/02_beats_scheduler_group_array.md)
- [Sink Data Path](docs/rapids_beats_mas/ch03_macro_blocks/03_sink_data_path.md) + AXIS wrapper, SRAM controllers
- [Source Data Path](docs/rapids_beats_mas/ch03_macro_blocks/07_source_data_path.md) + AXIS wrapper, SRAM controllers
- [RAPIDS Core](docs/rapids_beats_mas/ch03_macro_blocks/11_rapids_core_beats.md) / [Registers](docs/rapids_beats_mas/ch03_macro_blocks/12_rapids_regs.md) / [Top](docs/rapids_beats_mas/ch03_macro_blocks/14_rapids_beats_top.md)

**Interfaces (`docs/rapids_beats_mas/ch04_interfaces/`):**
- [AXI4 Interface](docs/rapids_beats_mas/ch04_interfaces/01_axi4_interface_spec.md)
- [AXIS Interface](docs/rapids_beats_mas/ch04_interfaces/02_axis_interface_spec.md)
- [MonBus Interface](docs/rapids_beats_mas/ch04_interfaces/03_monbus_interface_spec.md)

### 🐛 Known Issues
**Location:** `projects/components/dmas/rapids/known_issues/`

- **[Index](known_issues/README.md)** - Issue tracking overview (the old scheduler.md credit-counter write-up was retired with the pre-beats RTL)
- **[Sink Data Path](known_issues/active/sink_data_path.md)** - Minor issues
- **[Sink SRAM Control](known_issues/active/sink_sram_control.md)** - Edge cases
- Plus `known_issues/active/` for current beats issues

### 📖 Other Documentation
- **[CLAUDE](CLAUDE.md)** - AI assistance guide for this subsystem
- **[TASKS](TASKS.md)** - Work items (largely pre-beats history)
- **[Validation Report](docs/RAPIDS_Validation_Status_Report.md)** - Test results (pre-beats snapshot)

---

## 2.4 Organizational Standards - RAPIDS Code Location

**⚠️ MANDATORY: All RAPIDS-specific code must be in the project area ⚠️**

### Code Organization Principle

**"All RAPIDS-specific verification code MUST reside in `projects/components/dmas/rapids/dv/` for easy discovery."**

This subsystem follows the repository-wide organizational standard (see `/PRD.md` Section 2.3) requiring all project-specific code to be located in the project area, NOT the framework area.

### RAPIDS Directory Structure

```
projects/components/dmas/rapids/
├── rtl/                          # RTL source code
│   ├── includes/                 # RAPIDS packages
│   ├── fub/                      # Control engines (ctrlrd/ctrlwr)
│   ├── fub_beats/                # Beats functional unit blocks
│   ├── macro_beats/              # Beats assemblies + registers
│   ├── macro/                    # MonBus group
│   └── top_beats/                # rapids_beats_top.sv
│
└── dv/                           # Design verification (all RAPIDS-specific)
    ├── tbclasses/                # ★ RAPIDS TB classes HERE (not framework!)
    │   ├── scheduler_tb.py       # Scheduler testbench class
    │   ├── descriptor_engine_tb.py
    │   └── rapids_core_beats_tb.py
    │
    ├── components/               # ★ RAPIDS-specific BFMs
    │   └── data_mover_bfm.py
    │
    └── tests/                    # Test runners (import TB classes)
        ├── fub/                  # Control engine tests
        ├── fub_beats/            # Beats FUB tests (test_scheduler_beats.py, ...)
        ├── macro/                # MonBus group test
        ├── macro_beats/          # Multi-block scenarios
        └── top_beats/            # Full RAPIDS operation
```

### What Goes Where?

| Code Type | ✅ CORRECT Location | ❌ WRONG Location |
|-----------|---------------------|-------------------|
| **RAPIDS TB Classes** | `projects/components/dmas/rapids/dv/tbclasses/` | `bin/TBClasses/` (framework area) |
| **RAPIDS-Specific BFMs** | `projects/components/dmas/rapids/dv/components/` | `bin/TBClasses/` (framework area) |
| **RAPIDS Scoreboards** | `projects/components/dmas/rapids/dv/` (project area) | `bin/TBClasses/scoreboards/` |
| **Test Runners** | `projects/components/dmas/rapids/dv/tests/` | Anywhere else |
| **Shared AXI4/APB BFMs** | `bin/TBClasses/{protocol}/` | Project area |

### Import Pattern for RAPIDS Tests

**✅ CORRECT - Import from Project Area:**
```python
# Import framework utilities (PYTHONPATH includes bin/)
import os, sys
from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import RAPIDS TB classes from PROJECT AREA
from projects.components.dmas.rapids.dv.tbclasses.scheduler_tb import SchedulerTB
from projects.components.dmas.rapids.dv.tbclasses.descriptor_engine_tb import DescriptorEngineTB

# Shared framework components
from CocoTBFramework.components.axi4.axi4_master import AXI4Master
```

**❌ WRONG - Don't Import from Framework:**
```python
# DON'T DO THIS!
from TBClasses.rapids.scheduler_tb import SchedulerTB  # ❌ WRONG!
```

### Benefits of This Organization

1. **Easy Discovery** - All RAPIDS code in ONE place: `projects/components/dmas/rapids/`
2. **Clear Ownership** - RAPIDS team owns their `dv/` area completely
3. **No Confusion** - Never wonder "where does this TB class live?"
4. **Maintainability** - Changes isolated to RAPIDS area don't affect other projects
5. **Framework Stays Clean** - Only truly shared cross-project code in framework

### Compliance Status

✅ **RAPIDS is now compliant** - All TB classes moved to project area as of 2025-10-18

**Migration History:**
- **Before:** TB classes incorrectly in `bin/TBClasses/rapids/`
- **After:** TB classes correctly in `projects/components/dmas/rapids/dv/tbclasses/`
- **Test Imports:** Updated to import from project area

**📖 Complete Documentation:** See `/PRD.md` Section 2.3 for repository-wide organizational standards.

---

## 3. Architecture Overview

### 3.1 Top-Level Block Diagram

```
RAPIDS Beats (Rapid AXI Programmable In-band Descriptor System)
├── Scheduler Group (scheduler_group_beats / scheduler_group_array_beats)
│   ├── Scheduler          (Per-channel FSM, scheduler_beats.sv)
│   ├── Descriptor Engine  (Descriptor fetch/parsing, descriptor_engine_beats.sv)
│   └── Control Engines    (ctrlrd_engine.sv / ctrlwr_engine.sv)
│
├── Sink Data Path (AXIS Network → SRAM → System Memory)
│   ├── AXIS Slave ingress   (snk_data_path_axis_beats.sv)
│   ├── Sink SRAM Controller (snk_sram_controller_beats.sv + alloc/drain ctrl)
│   └── AXI Write Engine     (axi_write_engine_beats.sv)
│
├── Source Data Path (System Memory → SRAM → AXIS Network)
│   ├── AXI Read Engine        (axi_read_engine_beats.sv)
│   ├── Source SRAM Controller (src_sram_controller_beats.sv + alloc/drain ctrl)
│   └── AXIS Master egress     (src_data_path_axis_beats.sv)
│
└── Control and Monitoring
    ├── APB CSRs           (rapids_config_block.sv, PeakRDL rapids_regs.rdl)
    └── MonBus Group       (macro/monbus_axil_group_2in.sv)
```

**📖 See:** `docs/rapids_beats_mas/ch01_overview/01_architecture.md` for detailed architecture

### 3.2 Data Flow

**Sink Path (Receive):**
1. Network packets arrive via Network Slave
2. Buffered in Sink SRAM
3. DMA'd to system memory via AXI4 Write Engine
4. Completion reported via MonBus

**Source Path (Transmit):**
1. Descriptor specifies data location in system memory
2. Source AXI Reader fetches data to Source SRAM
3. Network Master transmits to network
4. Completion reported via MonBus

**Scheduler Coordination:**
- Parses descriptors from Descriptor Engine
- Manages credit-based flow control
- Sequences program engine operations
- Coordinates sink/source data paths

---

## 4. Key Features

### 4.1 Descriptor-Based Operation

| Feature | Status | Description |
|---------|--------|-------------|
| Descriptor FIFO | ✅ | Queued descriptor processing |
| Multi-field parsing | ✅ | Address, length, control fields |
| Chained descriptors | ⏳ | Future enhancement |
| Completion reporting | ✅ | Via MonBus packets |

### 4.2 Data Path Features

| Feature | Status | Description |
|---------|--------|-------------|
| SRAM buffering | ✅ | Decouple network from memory |
| AXI4 burst support | ✅ | Efficient memory transfers |
| Backpressure handling | ✅ | Flow control on all interfaces |
| Data alignment | ✅ | Handle unaligned transfers |

### 4.3 Scheduler Features

| Feature | Status | Description |
|---------|--------|-------------|
| Task FSM | ✅ | Multi-state coordination |
| Credit management | ⏳ | Pre-beats scheduler had exponential encoding (0→1, 1→2, ..., 15→∞); scheduler_beats.sv has no credit management yet (planned later phase) |
| Program sequencing | ✅ | Coordinated operations |
| Error detection | ✅ | Timeout, overflow detection |

**Credit Management Details (pre-beats, historical):**
- Uses **exponential credit encoding** for compact configuration
- 4-bit `cfg_initial_credit` decodes to actual credit counts:
  - `0` → 1 credit (2^0), `4` → 16 credits (2^4), `8` → 256 credits (2^8)
  - `15` → ∞ (unlimited credits, 0xFFFFFFFF)
- Encoding applied at initialization; runtime operations are linear (increment/decrement by 1)
- Provides wide range (1 to 16384) with minimal configuration overhead

**📖 See:** `docs/rapids_beats_mas/ch02_fub_blocks/01_scheduler.md` for the current scheduler specification

### 4.4 Monitoring Integration

| Feature | Status | Description |
|---------|--------|-------------|
| MonBus packets | ✅ | StandardAMBA 64-bit format |
| Descriptor events | ✅ | Start/complete reporting |
| Error events | ✅ | Timeout, overflow, underflow |
| Performance metrics | ⏳ | Future enhancement |

---

## 5. Interfaces

### 5.1 External Interfaces

| Interface | Type | Width | Purpose |
|-----------|------|-------|---------|
| **APB** | Slave | 32-bit | Control/status registers |
| **AXI4 (Sink)** | Master | Configurable | Write to system memory |
| **AXI4 (Source)** | Master | Configurable | Read from system memory |
| **AXIS (Sink)** | Slave | Configurable | Network ingress (tid = channel) |
| **AXIS (Source)** | Master | Configurable | Network egress (tid = channel) |
| **MonBus** | Master | 64-bit | Monitor packet output |

**📖 See:** `docs/rapids_beats_mas/ch04_interfaces/` and `docs/rapids_beats_has/ch03_interfaces/` for complete interface specs

### 5.2 Configuration Parameters

```systemverilog
// Example RAPIDS instantiation sketch (see rtl/top_beats/rapids_beats_top.sv for the
// full parameter/port list)
rapids_beats_top #(
    .ADDR_WIDTH(64),
    .DATA_WIDTH(512),
    .NUM_CHANNELS(8)
) u_rapids (
    .clk                (clk),
    .rst_n              (rst_n),
    // APB control interface
    .s_apb_*            (...),
    // AXI4 memory interfaces (read + write masters)
    .m_axi_*            (...),
    // AXIS network interfaces (tid = channel)
    .s_axis_*           (...),
    .m_axis_*           (...),
    // MonBus / monitor group egress
    .mon_*              (...)
);
```

---

## 6. Use Cases

### 6.1 DMA-Style Transfers

**Scenario:** Move data from network to system memory

**Flow:**
1. Software writes descriptor to Descriptor Engine
2. Scheduler parses descriptor, activates Sink path
3. Network packets arrive via Network Slave
4. Data buffered in Sink SRAM
5. AXI4 Write Engine DMAs to system memory
6. Completion packet on MonBus

### 6.2 Network Packet Processing

**Scenario:** Read data from memory, transmit to network

**Flow:**
1. Descriptor specifies source address, length
2. Source AXI Reader fetches data to SRAM
3. Network Master transmits to network
4. Completion/error reporting via MonBus

### 6.3 Custom Data Path Acceleration

**Educational value:** Shows how to build custom accelerators
- Descriptor-based control
- Multi-block FSM coordination
- Buffering strategies
- Error handling
- Performance monitoring

---

## 7. Test Coverage

### 7.1 Current Status

> **Status (2026-07-22):** The numbers below are a pre-beats snapshot (they include the retired
> program engine). Current beats regression: fub 232+ and macro 182 tests passing; run the
> beats suites for live numbers.

**Overall (pre-beats snapshot):** ~85% functional coverage (basic scenarios validated, descriptor engine complete)

| Component | Test Coverage | Status |
|-----------|--------------|--------|
| Scheduler | ~95% | Credit encoding fixed and verified (43/43 tests passing) |
| Descriptor Engine | ✅ 100% | **All tests passing** (14/14 tests, 100% success rate) |
| Program Engine | ~85% | Alignment tested |
| Sink Data Path | ~75% | Basic flows working |
| Source Data Path | ~70% | Basic flows working |
| SRAM Controllers | ~80% | Buffer management tested |
| Integration | ~60% | More stress testing needed |

**Test Location:** `projects/components/dmas/rapids/dv/tests/fub_beats/` and `projects/components/dmas/rapids/dv/tests/macro_beats/` (plus `fub/`, `macro/`, `top_beats/`)

**Recent Achievements:**
- ✅ **Descriptor Engine (2025-10-13):** Achieved 100% test pass rate using continuous background monitoring pattern
  - 14/14 tests passing across all test levels (basic, medium, full)
  - All test classes passing (APB_ONLY, MIXED)
  - All delay profiles passing (fast_producer, fast_consumer, fixed_delay, minimal_delay)
  - Applied continuous monitoring methodology for asynchronous output capture

**📖 See:** `docs/RAPIDS_Validation_Status_Report.md` for detailed results

### 7.2 Test Strategy

**FUB (Functional Unit Block) Tests:**
- Individual block testing
- Located in `projects/components/dmas/rapids/dv/tests/fub_beats/` (+ `fub/` for control engines)
- Focus on module-level functionality

**Macro Tests:**
- Multi-block scenarios
- Located in `projects/components/dmas/rapids/dv/tests/macro_beats/` (+ `macro/` for the monbus group)
- End-to-end data flow validation

**Top Tests:**
- Full RAPIDS operation
- Located in `projects/components/dmas/rapids/dv/tests/top_beats/`
- Realistic traffic patterns

---

## 8. Known Issues Summary

### 8.1 Critical Issues

**✅ Scheduler Credit Counter Initialization - FIXED (2025-10-11, pre-beats)**
- **File:** the retired pre-beats scheduler.sv (replaced by `rtl/fub_beats/scheduler_beats.sv`,
  which currently has no credit management - planned for a later phase)
- **Issue:** Credit counter was initializing to 0 instead of using exponential encoding
- **Fix Applied:** Implemented exponential credit encoding
- **Status:** Fixed and verified pre-beats; the known_issues/scheduler.md write-up was retired
  with that RTL (see `known_issues/README.md`)

**Fix Details:**
```systemverilog
// Previous (wrong):
r_descriptor_credit_counter <= 32'h0;

// Fixed - Exponential encoding:
// 0→1, 1→2, 2→4, 3→8, ..., 14→16384, 15→∞
r_descriptor_credit_counter <= (cfg_initial_credit == 4'hF) ? 32'hFFFFFFFF :
                              (cfg_initial_credit == 4'h0) ? 32'h00000001 :
                              (32'h1 << cfg_initial_credit);
```

**Encoding Rationale:**
- Compact 4-bit configuration covers 1 to 16384 credits
- Fine-grained control for low traffic (1, 2, 4, 8)
- High-throughput support (256, 1024, 16384)
- Special unlimited mode (15 → ∞)
- Exponential encoding applied at initialization only; runtime operations are linear

### 8.2 Medium Priority Issues

**Descriptor Engine Edge Cases:**
- Some stress test failures under high load
- Edge case handling needs improvement
- **Priority:** P2

**SRAM Control Timing:**
- Rare timing issues in back-to-back operations
- **Priority:** P2

**📖 See:** `known_issues/` directory for complete issue tracking

---

## 9. Integration Guidelines

### 9.1 Quick Start

```systemverilog
rapids_beats_top #(
    .ADDR_WIDTH(64),
    .DATA_WIDTH(512),
    .NUM_CHANNELS(8)
) u_rapids (
    // Clocking & Reset
    .clk                (system_clk),
    .rst_n              (system_rst_n),

    // APB Control (connect to control fabric)
    .s_apb_paddr        (ctrl_paddr),
    .s_apb_psel         (ctrl_psel),
    .s_apb_penable      (ctrl_penable),
    // ... other APB signals

    // AXI4 Memory (connect to memory controller)
    // ... AXI write channels (sink), AXI read channels (source)

    // AXIS Network (connect to network fabric; tid = channel)
    .s_axis_tdata       (net_rx_data),
    .s_axis_tvalid      (net_rx_valid),
    // ... AXIS slave (receive), AXIS master (transmit)

    // Monitor group egress (AXI-Lite drain / IRQ)
    // ... mon_* signals
);
```

See `rtl/top_beats/rapids_beats_top.sv` for the complete, authoritative port list.

### 9.2 Configuration Steps

1. **Initialize via APB registers** (use the generated regmap, access registers by name):
   - Configure channel enables and thresholds
   - Set timeout thresholds

2. **Load Descriptors:**
   - Write descriptors to Descriptor Engine FIFO
   - Each descriptor specifies: address, length, control bits

3. **Enable Operation:**
   - Set enable bits via APB registers
   - Monitor MonBus for completion/error packets

**📖 See:** `docs/rapids_beats_has/ch05_programming/` for register and programming details

---

## 10. Development Status

### 10.1 Current Phase

**Phase: Validation and Bug Fixing** (In Progress)

- ✅ Core architecture implemented
- ✅ Basic functionality verified
- ✅ Scheduler credit counter bug fixed (exponential encoding implemented)
- ⏳ Credit management tests need verification (remove workarounds)
- ⏳ Stress testing ongoing
- ⏳ Edge case refinement

**📖 See:** `TASKS.md` for detailed work items

### 10.2 Roadmap

**Near-Term (Q4 2025):**
- ✅ Fix scheduler credit counter bug (completed 2025-10-11)
- ⏳ Verify credit management tests (remove workarounds)
- ⏳ Complete descriptor engine stress testing
- ⏳ Integration test suite expansion
- ⏳ Performance benchmarking

**Long-Term (2026+):**
- Chained descriptor support
- Advanced error recovery
- Performance optimizations
- Multi-channel support

---

## 11. Performance Characteristics

### 11.1 Throughput

**Target:** Match network/memory interface bandwidth

**Bottlenecks:**
- SRAM buffer size
- AXI4 burst efficiency
- Scheduler overhead

**Optimization:**
- Increase SRAM depth for larger packets
- Tune AXI4 burst parameters
- Pipeline scheduler operations

### 11.2 Latency

**Components:**
- Descriptor parsing: ~10 cycles
- SRAM buffering: Configurable depth
- AXI4 memory access: System dependent
- End-to-end: Typically <100 cycles for small packets

### 11.3 Resource Utilization

**Area:**
- Scheduler: ~2K LUTs
- Each data path: ~3K LUTs
- SRAM buffers: Configurable (dominant area)
- Total: ~10K LUTs + SRAM

**Power:**
- Clock gating opportunities in idle blocks
- SRAM power depends on depth/width

---

## 12. Verification Infrastructure

### 12.1 Test Organization

**Location:** `projects/components/dmas/rapids/dv/tests/`

**Structure:**
```
projects/components/dmas/rapids/dv/tests/
├── fub/                    # Control engine tests (ctrlrd/ctrlwr)
├── fub_beats/              # Beats FUB tests (scheduler, descriptor engine,
│                           #   alloc/drain ctrl, latency bridge)
├── macro/                  # MonBus group test
├── macro_beats/            # Multi-block scenarios (scheduler group, data paths,
│                           #   SRAM controllers)
└── top_beats/              # Full RAPIDS operation
```

### 12.2 CocoTB Framework

**Location:** `projects/components/dmas/rapids/dv/tbclasses/` (RAPIDS-specific) plus shared BFMs in `bin/TBClasses/`

**Components:**
- RAPIDS-specific drivers
- Descriptor generators
- Traffic patterns
- Monitor checkers

**📖 See:** `docs/markdown/TBClasses/` for shared framework docs

### 12.2.1 MANDATORY: BFM Usage for FUB Tests

**⚠️ CRITICAL DESIGN REQUIREMENT ⚠️**

**All RAPIDS FUB (Functional Unit Block) level tests MUST use CocoTB Framework BFMs. Manual handshake driving is NOT allowed.**

**Required BFM Components:**

| Interface Type | Framework Location | BFM Component |
|----------------|-------------------|---------------|
| **Custom valid/ready** | `bin/TBClasses/gaxi/` | GAXI Master/Slave |
| **AXI4** | `bin/TBClasses/axi4/` | AXI4 Master/Slave |
| **AXI4-Lite (AXIL)** | `bin/TBClasses/axil4/` | AXIL Master/Slave |
| **APB** | `bin/TBClasses/apb/` | APB Master/Slave |
| **AXI-Stream (AXIS)** | `bin/TBClasses/axis4/` | AXIS Master/Slave (RAPIDS network interfaces are AXIS) |
| **MonBus** | `bin/TBClasses/monbus/` | MonBus drivers |

**Rationale:**
1. **Consistency**: All tests use standardized handshake protocols
2. **Correctness**: BFMs handle complex timing scenarios (backpressure, randomization)
3. **Reusability**: Same BFM across all RAPIDS tests
4. **Maintainability**: Fix once in BFM, all tests benefit
5. **Coverage**: BFMs include comprehensive timing profiles

**Example - Program Engine:**

```python
# ❌ WRONG: Manual handshake (violates design requirement)
async def send_request(self, addr, data):
    self.dut.program_valid.value = 1
    self.dut.program_pkt_addr.value = addr
    # ... manual handshaking logic ...

# ✅ CORRECT: Use GAXI Master BFM
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster

class ProgramEngineTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.program_master = GAXIMaster(
            dut=dut,
            clock=dut.clk,
            valid_signal='program_valid',
            ready_signal='program_ready',
            data_signals=['program_pkt_addr', 'program_pkt_data'],
            data_widths=[64, 32]
        )

    async def send_request(self, addr, data):
        await self.program_master.write({'program_pkt_addr': addr, 'program_pkt_data': data})
```

**📖 See:**
- `projects/components/dmas/rapids/CLAUDE.md` - Rule #1 for complete BFM usage guidelines
- `docs/markdown/TBClasses/gaxi/` - GAXI BFM documentation
- `bin/TBClasses/axi4/` - AXI4 BFM sources (full framework docs in the RTLDesignSherpa-DV repo)

### 12.3 Test File Structure (Standard Pattern)

**⚠️ MANDATORY: All RAPIDS tests must follow this structure ⚠️**

RAPIDS tests follow the same pattern as AMBA tests for consistency across the repository:

```python
# Example: projects/components/dmas/rapids/dv/tests/fub_beats/test_scheduler_beats.py

import os
import pytest
import cocotb
from cocotb_test.simulator import run

# Import REUSABLE testbench class (NOT defined in this file!)
from projects.components.dmas.rapids.dv.tbclasses.scheduler_tb import SchedulerTB
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.tbbase import TBBase

# ===========================================================================
# COCOTB TEST FUNCTIONS - prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic_flow(dut):
    """Test basic descriptor flow."""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()  # Mandatory init method
    await tb.initialize_test()
    result = await tb.test_basic_descriptor_flow()
    assert result, "Basic descriptor flow test failed"

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_credit_encoding(dut):
    """Test exponential credit encoding."""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()  # Mandatory init method
    await tb.initialize_test()
    result = await tb.test_exponential_encoding_all_values()
    assert result, "Credit encoding test failed"

# ===========================================================================
# PARAMETER GENERATION - at bottom of file
# ===========================================================================

def generate_scheduler_test_params():
    """Generate test parameters for scheduler tests."""
    return [
        # (channel_id, num_channels, data_width, credit_width)
        (0, 8, 512, 8),  # Standard configuration
        # Add more parameter sets as needed
    ]

scheduler_params = generate_scheduler_test_params()

# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - at bottom of file
# ===========================================================================

@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_basic_flow(request, channel_id, num_channels, data_width, credit_width):
    """
    Scheduler basic flow test.

    Run with: pytest projects/components/dmas/rapids/dv/tests/fub_beats/test_scheduler_beats.py::test_basic_flow -v
    """
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub_beats': '../../rtl/fub_beats'
    })

    dut_name = "scheduler_beats"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(repo_root, 'rtl', 'amba', 'includes', 'monitor_pkg.sv'),
        # RAPIDS package(s) from the project includes area
        # (prefer get_sources_from_filelist() with rtl/filelists/ in real tests)
        os.path.join(rtl_dict['rtl_fub_beats'], '..', 'includes', 'rapids_pkg.sv'),
        os.path.join(rtl_dict['rtl_fub_beats'], f'{dut_name}.sv'),
    ]

    # Format parameters for unique test name
    cid_str = TBBase.format_dec(channel_id, 2)
    nc_str = TBBase.format_dec(num_channels, 2)
    dw_str = TBBase.format_dec(data_width, 4)
    cw_str = TBBase.format_dec(credit_width, 2)
    test_name_plus_params = f"test_{dut_name}_cid{cid_str}_nc{nc_str}_dw{dw_str}_cw{cw_str}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'CHANNEL_ID': channel_id,
        'NUM_CHANNELS': num_channels,
        'DATA_WIDTH': data_width,
        'CREDIT_WIDTH': credit_width,
        # Add other RTL parameters as needed
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TEST_CHANNEL_ID': str(channel_id),
        'TEST_NUM_CHANNELS': str(num_channels),
        'TEST_DATA_WIDTH': str(data_width),
    }

    compile_args = ["-Wno-TIMESCALEMOD"]
    sim_args = []
    plusargs = []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[
                os.path.join(repo_root, 'projects', 'components', 'dmas', 'rapids', 'rtl', 'includes'),
                os.path.join(repo_root, 'rtl', 'amba', 'includes'),
            ],
            toplevel=toplevel,
            module=module,
            testcase="cocotb_test_basic_flow",  # ← cocotb test function name
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        print(f"✓ Scheduler basic flow test completed!")
        print(f"Logs: {log_path}")

    except Exception as e:
        print(f"❌ Scheduler basic flow test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        raise
```

**Key Structure Requirements:**

1. **Testbench Class Location:**
   - ALWAYS in `projects/components/dmas/rapids/dv/tbclasses/`
   - NEVER inline in test file
   - Reusable across multiple test files

2. **CocoTB Test Functions:**
   - Prefix with `cocotb_` to prevent pytest collection
   - Located at top of test file
   - Use `@cocotb.test()` decorator
   - Call testbench methods

3. **Parameter Generation:**
   - Function returns list of parameter tuples
   - Located near bottom of file (before pytest wrappers)
   - Stored in variable (e.g., `scheduler_params`)

4. **Pytest Wrapper Functions:**
   - Located at bottom of file
   - Use `@pytest.mark.parametrize()` with parameter variable
   - Build unique test names with `TBBase.format_dec()`
   - Call `run()` with `testcase="cocotb_test_function_name"`
   - Handle parallel execution (`PYTEST_XDIST_WORKER`)

5. **Mandatory TB Methods:**
   - `async def setup_clocks_and_reset(self)` - Complete initialization
   - `async def assert_reset(self)` - Assert reset signal(s)
   - `async def deassert_reset(self)` - Deassert reset signal(s)

**📖 See:**
- `val/amba/test_apb4_slave.py` - Reference example
- `projects/components/dmas/rapids/CLAUDE.md` - Detailed TB requirements

---

## 13. Quick Reference

### 13.1 Key Files

| File | Purpose |
|------|---------|
| `projects/components/dmas/rapids/PRD.md` | This document (overview) |
| `projects/components/dmas/rapids/CLAUDE.md` | AI assistance guide |
| `projects/components/dmas/rapids/TASKS.md` | Work items (largely pre-beats history) |
| `projects/components/dmas/rapids/docs/rapids_beats_has/` | **Architecture specification** |
| `projects/components/dmas/rapids/docs/rapids_beats_mas/` | **Micro-architecture specification** |
| `projects/components/dmas/rapids/known_issues/` | Bug tracking |
| `docs/RAPIDS_Validation_Status_Report.md` | Test results (pre-beats snapshot) |

### 13.2 Commands

```bash
# Run RAPIDS tests
pytest projects/components/dmas/rapids/dv/tests/fub_beats/ -v     # Individual blocks
pytest projects/components/dmas/rapids/dv/tests/macro_beats/ -v   # Multi-block
pytest projects/components/dmas/rapids/dv/tests/top_beats/ -v     # Full system

# Run specific FUB test
pytest projects/components/dmas/rapids/dv/tests/fub_beats/test_scheduler_beats.py -v

# Lint RAPIDS RTL
verilator --lint-only projects/components/dmas/rapids/rtl/fub_beats/scheduler_beats.sv

# View specifications
cat projects/components/dmas/rapids/docs/rapids_beats_mas/rapids_beats_mas_index.md
cat projects/components/dmas/rapids/docs/rapids_beats_mas/ch02_fub_blocks/01_scheduler.md
```

---

## 14. Success Criteria

### 14.1 Functional

- ✅ All major blocks implemented
- ✅ Basic data flows working
- ✅ Scheduler credit bug fixed (exponential encoding implemented)
- ⏳ Credit management tests verified (remove workarounds, run full suite)
- ⏳ 100% descriptor test pass rate (currently ~80%)
- ⏳ Stress tests passing

### 14.2 Quality

- ⏳ >90% functional coverage (currently ~80%)
- ⏳ >85% code coverage
- ✅ All FSMs documented
- ⏳ Integration guide complete

### 14.3 Documentation

- ✅ Complete specification in docs/rapids_beats_has/ + docs/rapids_beats_mas/
- ✅ Known issues documented
- ⏳ Integration examples
- ⏳ Performance characterization

---

## 15. Educational Value

RAPIDS demonstrates:
- ✅ Complex FSM coordination (scheduler ↔ data paths)
- ✅ Descriptor-based DMA design patterns
- ✅ Buffer management strategies
- ✅ Credit-based flow control with exponential encoding
- ✅ Multi-interface integration
- ✅ Comprehensive monitoring
- ✅ Error detection and reporting
- ✅ Compact configuration encoding strategies

**Target Audience:**
- Advanced RTL designers
- Accelerator architects
- DMA engine developers
- System integration engineers

---

## 15. Attribution and Contribution Guidelines

### 15.1 Git Commit Attribution

When creating git commits for RAPIDS documentation or implementation:

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Rationale:** RAPIDS documentation and organization receives AI assistance for structure and clarity, while design concepts and architectural decisions remain human-authored.

---

## 16. Documentation Generation

### 16.1 Generating PDF/DOCX from Specification

**Tool:** `bin/md_to_docx.py` (driven by the wrapper scripts in `docs/` - preferred)

Use the wrapper scripts to convert the linked HAS/MAS spec indexes into single all-inclusive PDF/DOCX files:

**Basic Usage:**

```bash
# Preferred: wrapper scripts (they call md_to_docx.py with the house style)
cd projects/components/dmas/rapids/docs
./generate_has_pdf.sh --rev 0.8     # builds RAPIDS_Beats_HAS_v0.8.docx/.pdf
./generate_mas_pdf.sh --rev 0.7     # builds RAPIDS_Beats_MAS_v0.7.docx/.pdf

# Direct tool invocation (from repo root), if you need custom options
python bin/md_to_docx.py \
    projects/components/dmas/rapids/docs/rapids_beats_mas/rapids_beats_mas_index.md \
    -o projects/components/dmas/rapids/docs/RAPIDS_Beats_MAS_draft.docx \
    --toc \
    --title-page \
    --pdf
```

**Key Features:**
- **Recursive Collection:** Follows all markdown links in the index file
- **Heading Demotion:** Automatically adjusts heading levels for included files
- **Table of Contents:** `--toc` flag generates automatic ToC
- **Title Page:** `--title-page` flag creates title page from first heading
- **PDF Export:** `--pdf` flag generates both DOCX and PDF
- **Image Support:** Resolves images relative to source directory
- **Template Support:** Optional custom DOCX/DOTX template via `-t` flag

**Common Workflow:**

```bash
# 1. Update spec content under rapids_beats_has/ or rapids_beats_mas/
# 2. Generate documentation with a bumped revision
cd projects/components/dmas/rapids/docs
./generate_mas_pdf.sh --rev 0.8

# 3. Output files created in docs/:
#    - RAPIDS_Beats_MAS_v0.8.docx
#    - RAPIDS_Beats_MAS_v0.8.pdf
```

**Debug Mode:**

```bash
# Generate debug markdown to see combined output
python bin/md_to_docx.py \
    projects/components/dmas/rapids/docs/rapids_beats_mas/rapids_beats_mas_index.md \
    -o output.docx \
    --debug-md

# This creates debug.md showing the complete merged content
```

**Tool Requirements:**
- Python 3.6+
- Pandoc installed and in PATH
- For PDF generation: LaTeX (e.g., texlive) or use Pandoc's built-in PDF writer

**📖 See:** `bin/md_to_docx.py` for complete implementation details

---

## 16.2 PDF Generation Location

**IMPORTANT: PDF files should be generated in the docs directory:**
```
projects/components/dmas/rapids/docs/
```

**Quick Command:** Use the provided shell scripts:
```bash
cd projects/components/dmas/rapids/docs
./generate_has_pdf.sh    # Architecture spec (HAS)
./generate_mas_pdf.sh    # Micro-architecture spec (MAS)
```

The shell scripts will automatically:
1. Use the md_to_docx.py tool from bin/
2. Process the rapids_beats_has / rapids_beats_mas index files
3. Generate both DOCX and PDF files in the docs/ directory
4. Create table of contents and title page

**📖 See:** `bin/md_to_docx.py` for complete implementation details

---

## 17. References

### 16.1 Internal Documentation

- **Complete Spec:** `docs/rapids_beats_has/` + `docs/rapids_beats_mas/` ← **Primary technical reference**
- **Validation:** `docs/RAPIDS_Validation_Status_Report.md` (pre-beats snapshot)
- **Master PRD:** `/PRD.md`
- **Repository Guide:** `/CLAUDE.md`

### 16.2 Related Subsystems

- **AMBA:** `rtl/amba/` - Monitor infrastructure used in RAPIDS (monitors in `rtl/amba/monitor/`)
- **Common:** `rtl/common/` - Building blocks (counters, FIFOs, etc.)
- **CocoTB Framework:** `bin/TBClasses/` (shared) + `projects/components/dmas/rapids/dv/tbclasses/` (RAPIDS)

### 16.3 External References

- AXI4 Specification: ARM IHI0022E
- AXIL4 Specification: ARM IHI0022E (subset)
- Network interface specs (custom Network protocol)

---

**Document Version:** 1.0
**Last Updated:** 2025-09-30
**Review Cycle:** Monthly during active development
**Next Review:** 2025-10-30
**Owner:** RTL Design Sherpa Project

---

## Navigation

- **← Back to Root:** `/PRD.md`
- **Complete Specification:** `docs/rapids_beats_has/rapids_beats_has_index.md` + `docs/rapids_beats_mas/rapids_beats_mas_index.md`
- **AI Guidance:** `CLAUDE.md`
- **Tasks:** `TASKS.md`
- **Issues:** `known_issues/`
