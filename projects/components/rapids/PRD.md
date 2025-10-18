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

### 1.1 Quick Stats

- **Modules:** 17 SystemVerilog files
- **Architecture:** 3 major blocks (Scheduler, Sink, Source)
- **Interfaces:** AXI4 (memory), Network (network), AXIL4 (control), MonBus (monitoring)
- **Test Coverage:** ~80% functional (basic scenarios validated)
- **Status:** Active validation, known issues documented

### 1.2 Subsystem Goals

- **Primary:** Demonstrate complex accelerator design patterns
- **Secondary:** Provide DMA-style memory transfer capability
- **Tertiary:** Educational reference for descriptor-based engines

---

## 2. Documentation Structure

This PRD provides a high-level overview. **Detailed specifications are maintained separately:**

### 📚 Complete RAPIDS Specification
**Location:** `projects/components/rapids/docs/rapids_spec/`

- **[Index](rapids_spec/miop_index.md)** - Complete specification structure

#### Chapter 1: Overview
- [Overview](rapids_spec/ch01_overview/01_overview.md)
- [Architecture Requirements](rapids_spec/ch01_overview/02_architectural_requirements.md)
- [Clocking and Reset](rapids_spec/ch01_overview/03_clocks_and_reset.md)
- [Acronyms](rapids_spec/ch01_overview/04_acronyms.md)
- [References](rapids_spec/ch01_overview/05_references.md)

#### Chapter 2: Block Specifications
- [Blocks Overview](rapids_spec/ch02_blocks/00_overview.md)

**Scheduler Group:**
- [Scheduler Group](rapids_spec/ch02_blocks/01_00_scheduler_group.md)
- [Scheduler](rapids_spec/ch02_blocks/01_01_scheduler.md) - Task management FSM
- [Descriptor Engine](rapids_spec/ch02_blocks/01_02_descriptor_engine.md) - Descriptor parsing
- [Program Engine](rapids_spec/ch02_blocks/01_03_program_engine.md) - Program sequencing

**Sink Data Path (Network → Memory):**
- [Sink Data Path](rapids_spec/ch02_blocks/02_00_sink_data_path.md)
- [Network Slave](rapids_spec/ch02_blocks/02_01_network_slave.md) - Network ingress
- [Sink SRAM Control](rapids_spec/ch02_blocks/02_02_sink_sram_control.md) - Buffer management
- [Sink AXI Write Engine](rapids_spec/ch02_blocks/02_03_sink_axi_write_engine.md) - Memory writes

**Source Data Path (Memory → Network):**
- [Source Data Path](rapids_spec/ch02_blocks/03_00_source_data_path.md)
- [Network Master](rapids_spec/ch02_blocks/03_01_network_master.md) - Network egress
- [Source SRAM Control](rapids_spec/ch02_blocks/03_02_source_sram_control.md) - Buffer management
- [Source AXI Read Engine](rapids_spec/ch02_blocks/03_03_source_axi_read_engine.md) - Memory reads

**Monitoring:**
- [MonBus AXIL Group](rapids_spec/ch02_blocks/04_monbus_axil_group.md) - Control/status
- [FSM Summary](rapids_spec/ch02_blocks/05_fsm_summary_table.md) - State machine overview

#### Chapter 3: Interfaces
- [Top-Level Ports](rapids_spec/ch03_interfaces/01_top_level.md)
- [AXIL4 Interface](rapids_spec/ch03_interfaces/02_axil_interface_spec.md)
- [AXI4 Interface](rapids_spec/ch03_interfaces/03_axi4_interface_spec.md)
- [Network Interface](rapids_spec/ch03_interfaces/04_network_interface_spec.md)
- [MonBus Interface](rapids_spec/ch03_interfaces/05_monbus_interface_spec.md)

#### Chapter 4 & 5: Programming
- [Programming Model](rapids_spec/ch04_programming_models/01_programming.md)
- [Register Definitions](rapids_spec/ch05_registers/01_registers.md)

### 🐛 Known Issues
**Location:** `projects/components/rapids/known_issues/`

- **[Scheduler](known_issues/scheduler.md)** - Credit counter initialization bug
- **[Sink Data Path](known_issues/sink_data_path.md)** - Minor issues
- **[Sink SRAM Control](known_issues/sink_sram_control.md)** - Edge cases

### 📖 Other Documentation
- **[README](README.md)** - Quick start and integration guide
- **[CLAUDE](CLAUDE.md)** - AI assistance guide for this subsystem
- **[TASKS](TASKS.md)** - Current work items (to be created)
- **[Validation Report](../../docs/RAPIDS_Validation_Status_Report.md)** - Test results

---

## 3. Architecture Overview

### 3.1 Top-Level Block Diagram

```
RAPIDS (Rapid AXI Programmable In-band Descriptor System)
├── Scheduler Group
│   ├── Scheduler          (Task FSM, credit management)
│   ├── Descriptor Engine  (Descriptor FIFO, parsing)
│   └── Program Engine     (Program sequencing, alignment)
│
├── Sink Data Path (Network → SRAM → System Memory)
│   ├── Network Slave        (Network ingress interface)
│   ├── Sink SRAM Control (Buffering, flow control)
│   └── Sink AXI Writer   (AXI4 write to system memory)
│
├── Source Data Path (System Memory → SRAM → Network)
│   ├── Source AXI Reader (AXI4 read from system memory)
│   ├── Source SRAM Control (Buffering, flow control)
│   └── Network Master       (Network egress interface)
│
└── MonBus AXIL Group
    ├── AXIL4 Slave       (Control/status registers)
    └── MonBus Reporter   (Monitor packet generation)
```

**📖 See:** `rapids_spec/ch02_blocks/00_overview.md` for detailed architecture

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
| Credit management | ✅ | Exponential encoding (0→1, 1→2, 2→4, ..., 15→∞) |
| Program sequencing | ✅ | Coordinated operations |
| Error detection | ✅ | Timeout, overflow detection |

**Credit Management Details:**
- Uses **exponential credit encoding** for compact configuration
- 4-bit `cfg_initial_credit` decodes to actual credit counts:
  - `0` → 1 credit (2^0), `4` → 16 credits (2^4), `8` → 256 credits (2^8)
  - `15` → ∞ (unlimited credits, 0xFFFFFFFF)
- Encoding applied at initialization; runtime operations are linear (increment/decrement by 1)
- Provides wide range (1 to 16384) with minimal configuration overhead

**📖 See:** `rapids_spec/ch02_blocks/01_01_scheduler.md` for complete encoding table

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
| **AXIL4** | Slave | 32-bit | Control/status registers |
| **AXI4 (Sink)** | Master | Configurable | Write to system memory |
| **AXI4 (Source)** | Master | Configurable | Read from system memory |
| **Network (Sink)** | Slave | Configurable | Network ingress |
| **Network (Source)** | Master | Configurable | Network egress |
| **MonBus** | Master | 64-bit | Monitor packet output |

**📖 See:** `rapids_spec/ch03_interfaces/` for complete interface specs

### 5.2 Configuration Parameters

```systemverilog
// Example RAPIDS instantiation parameters
miop_top #(
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),
    .Network_DATA_WIDTH(64),
    .SRAM_DEPTH(1024),
    .MAX_DESCRIPTORS(16)
) u_miop (
    .aclk               (clk),
    .aresetn            (rst_n),
    // AXIL4 control interface
    .s_axil_*           (...),
    // AXI4 memory interfaces
    .m_axi_sink_*       (...),
    .m_axi_source_*     (...),
    // Network network interfaces
    .s_network_*           (...),
    .m_network_*           (...),
    // MonBus output
    .monbus_pkt_*       (...)
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

**Overall:** ~85% functional coverage (basic scenarios validated, descriptor engine complete)

| Component | Test Coverage | Status |
|-----------|--------------|--------|
| Scheduler | ~95% | Credit encoding fixed and verified (43/43 tests passing) |
| Descriptor Engine | ✅ 100% | **All tests passing** (14/14 tests, 100% success rate) |
| Program Engine | ~85% | Alignment tested |
| Sink Data Path | ~75% | Basic flows working |
| Source Data Path | ~70% | Basic flows working |
| SRAM Controllers | ~80% | Buffer management tested |
| Integration | ~60% | More stress testing needed |

**Test Location:** `projects/components/rapids/dv/tests/fub_tests/` and `projects/components/rapids/dv/tests/integration_tests/`

**Recent Achievements:**
- ✅ **Descriptor Engine (2025-10-13):** Achieved 100% test pass rate using continuous background monitoring pattern
  - 14/14 tests passing across all test levels (basic, medium, full)
  - All test classes passing (APB_ONLY, RDA_ONLY, MIXED)
  - All delay profiles passing (fast_producer, fast_consumer, fixed_delay, minimal_delay)
  - Applied continuous monitoring methodology for asynchronous output capture

**📖 See:** `docs/RAPIDS_Validation_Status_Report.md` for detailed results

### 7.2 Test Strategy

**FUB (Functional Unit Block) Tests:**
- Individual block testing
- Located in `projects/components/rapids/dv/tests/fub_tests/`
- Focus on module-level functionality

**Integration Tests:**
- Multi-block scenarios
- Located in `projects/components/rapids/dv/tests/integration_tests/`
- End-to-end data flow validation

**System Tests:**
- Full RAPIDS operation
- Located in `projects/components/rapids/dv/tests/system_tests/`
- Realistic traffic patterns

---

## 8. Known Issues Summary

### 8.1 Critical Issues

**✅ Scheduler Credit Counter Initialization - FIXED (2025-10-11)**
- **File:** `projects/components/rapids/rtl/rapids_fub/scheduler.sv:567-570`
- **Issue:** Credit counter was initializing to 0 instead of using exponential encoding
- **Fix Applied:** Implemented exponential credit encoding
- **Status:** Fixed, awaiting test verification
- **Documentation:** `known_issues/scheduler.md`

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
miop_top #(
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),
    .Network_DATA_WIDTH(64)
) u_miop (
    // Clocking & Reset
    .aclk               (system_clk),
    .aresetn            (system_rst_n),

    // AXIL4 Control (connect to control fabric)
    .s_axil_awaddr      (ctrl_awaddr),
    .s_axil_awvalid     (ctrl_awvalid),
    .s_axil_awready     (ctrl_awready),
    // ... other AXIL signals

    // AXI4 Memory (connect to memory controller)
    .m_axi_sink_awaddr  (mem_awaddr),
    .m_axi_sink_awvalid (mem_awvalid),
    // ... AXI write channel for sink
    // ... AXI read channel for source

    // Network Network (connect to network fabric)
    .s_network_tdata       (net_rx_data),
    .s_network_tvalid      (net_rx_valid),
    // ... Network slave (receive)
    // ... Network master (transmit)

    // MonBus Output (connect to monitor aggregator)
    .monbus_pkt_valid   (miop_mon_valid),
    .monbus_pkt_ready   (miop_mon_ready),
    .monbus_pkt_data    (miop_mon_data)
);
```

### 9.2 Configuration Steps

1. **Initialize via AXIL4:**
   - Configure SRAM depths
   - Set timeout thresholds
   - Enable credit management (or disable if using workaround)

2. **Load Descriptors:**
   - Write descriptors to Descriptor Engine FIFO
   - Each descriptor specifies: address, length, control bits

3. **Enable Operation:**
   - Set enable bits via AXIL4 registers
   - Monitor MonBus for completion/error packets

**📖 See:** `rapids_spec/ch04_programming_models/01_programming.md` for register details

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

**Location:** `projects/components/rapids/dv/tests/`

**Structure:**
```
projects/components/rapids/dv/tests/
├── fub_tests/              # Functional Unit Block tests
│   ├── scheduler/
│   ├── descriptor_engine/
│   ├── program_engine/
│   ├── network_interfaces/
│   └── simple_sram/
├── integration_tests/      # Multi-block scenarios
└── system_tests/           # Full RAPIDS operation
```

### 12.2 CocoTB Framework

**Location:** `bin/CocoTBFramework/tbclasses/rapids/`

**Components:**
- RAPIDS-specific drivers
- Descriptor generators
- Traffic patterns
- Monitor checkers

**📖 See:** `docs/markdown/CocoTBFramework/` (once created)

### 12.2.1 MANDATORY: BFM Usage for FUB Tests

**⚠️ CRITICAL DESIGN REQUIREMENT ⚠️**

**All RAPIDS FUB (Functional Unit Block) level tests MUST use CocoTB Framework BFMs. Manual handshake driving is NOT allowed.**

**Required BFM Components:**

| Interface Type | Framework Location | BFM Component |
|----------------|-------------------|---------------|
| **Custom valid/ready** | `bin/CocoTBFramework/components/gaxi/` | GAXI Master/Slave |
| **AXI4** | `bin/CocoTBFramework/components/axi4/` | AXI4 Master/Slave |
| **AXI4-Lite (AXIL)** | `bin/CocoTBFramework/components/axil4/` | AXIL Master/Slave |
| **APB** | `bin/CocoTBFramework/components/apb/` | APB Master/Slave |
| **AXI-Stream (AXIS)** | `bin/CocoTBFramework/components/axis4/` | AXIS Master/Slave |
| **Network** | `bin/CocoTBFramework/components/network/` | Network Master/Slave |
| **MonBus** | `bin/CocoTBFramework/components/monbus/` | MonBus drivers |

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
- `projects/components/rapids/CLAUDE.md` - Rule #1 for complete BFM usage guidelines
- `bin/CocoTBFramework/components/gaxi/README.md` - GAXI BFM documentation
- `bin/CocoTBFramework/components/axi4/README.md` - AXI4 BFM documentation

### 12.3 Test File Structure (Standard Pattern)

**⚠️ MANDATORY: All RAPIDS tests must follow this structure ⚠️**

RAPIDS tests follow the same pattern as AMBA tests for consistency across the repository:

```python
# Example: projects/components/rapids/dv/tests/fub_tests/scheduler/test_scheduler.py

import os
import pytest
import cocotb
from cocotb_test.simulator import run

# Import REUSABLE testbench class (NOT defined in this file!)
from CocoTBFramework.tbclasses.rapids.scheduler_tb import SchedulerTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

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

    Run with: pytest projects/components/rapids/dv/tests/fub_tests/scheduler/test_scheduler.py::test_basic_flow -v
    """
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub'
    })

    dut_name = "scheduler"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(repo_root, 'rtl', 'amba', 'includes', 'monitor_pkg.sv'),
        os.path.join(repo_root, 'rtl', 'rapids', 'includes', 'rapids_pkg.sv'),
        os.path.join(rtl_dict['rtl_rapids_fub'], f'{dut_name}.sv'),
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
                os.path.join(repo_root, 'rtl', 'rapids', 'includes'),
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
   - ALWAYS in `bin/CocoTBFramework/tbclasses/rapids/`
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
- `val/amba/test_apb_slave.py` - Reference example
- `projects/components/rapids/CLAUDE.md` - Detailed TB requirements

---

## 13. Quick Reference

### 13.1 Key Files

| File | Purpose |
|------|---------|
| `projects/components/rapids/PRD.md` | This document (overview) |
| `projects/components/rapids/README.md` | Quick start guide |
| `projects/components/rapids/CLAUDE.md` | AI assistance guide |
| `projects/components/rapids/TASKS.md` | Work items (to be created) |
| `projects/components/rapids/docs/rapids_spec/` | **Complete specification** |
| `projects/components/rapids/known_issues/` | Bug tracking |
| `docs/RAPIDS_Validation_Status_Report.md` | Test results |

### 13.2 Commands

```bash
# Run RAPIDS tests
pytest projects/components/rapids/dv/tests/fub_tests/ -v          # Individual blocks
pytest projects/components/rapids/dv/tests/integration_tests/ -v   # Multi-block
pytest projects/components/rapids/dv/tests/system_tests/ -v        # Full system

# Run specific FUB test
pytest projects/components/rapids/dv/tests/fub_tests/scheduler/ -v

# Lint RAPIDS RTL
verilator --lint-only projects/components/rapids/rtl/rapids_fub/scheduler.sv

# View specifications
cat projects/components/rapids/docs/rapids_spec/miop_index.md
cat projects/components/rapids/docs/rapids_spec/ch02_blocks/01_01_scheduler.md
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

- ✅ Complete specification in rapids_spec/
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

## 16. References

### 16.1 Internal Documentation

- **Complete Spec:** `rapids_spec/` ← **Primary technical reference**
- **Validation:** `docs/RAPIDS_Validation_Status_Report.md`
- **Master PRD:** `/PRD.md`
- **Repository Guide:** `/CLAUDE.md`

### 16.2 Related Subsystems

- **AMBA:** `rtl/amba/` - Monitor infrastructure used in RAPIDS
- **Common:** `rtl/common/` - Building blocks (counters, FIFOs, etc.)
- **CocoTB Framework:** `bin/CocoTBFramework/tbclasses/rapids/`

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
- **Complete Specification:** `rapids_spec/miop_index.md`
- **Quick Start:** `README.md`
- **AI Guidance:** `CLAUDE.md`
- **Tasks:** `TASKS.md` (to be created)
- **Issues:** `known_issues/`
