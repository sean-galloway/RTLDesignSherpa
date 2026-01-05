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

# Claude Code Guide: Bridge Subsystem

**Version:** 2.1
**Last Updated:** 2025-11-03
**Purpose:** AI-specific guidance for working with Bridge subsystem

---

## 🚨 CRITICAL: Read Architecture Document First

**Before making ANY changes to bridge generator or understanding signal flow:**

📖 **READ:** `projects/components/bridge/docs/BRIDGE_ARCHITECTURE.md`

This document contains the **definitive bridge architecture** including:
- Correct signal flow (wrappers → decoder → converters → crossbar → slaves)
- Component purposes and placement
- Common misconceptions that previous agents made
- Why there's NO fixed crossbar width

**If you skip this document, you WILL make incorrect assumptions.**

---

## Quick Context

**What:** Bridge - Two complementary AXI4 Crossbar Generators (framework-based and CSV-based)
**Status:** 🟢 Phase 2 Complete - CSV generator with channel-specific masters (wr/rd/rw)
**Your Role:** Help users configure CSV files, generate bridges, understand architecture, and create tests

**📖 Complete Documentation (Read in This Order):**
1. `projects/components/bridge/docs/BRIDGE_ARCHITECTURE.md` ← **START HERE** (architecture reference)
2. `projects/components/bridge/PRD.md` ← Product requirements
3. `projects/components/bridge/BRIDGE_CURRENT_STATE.md` ← Current implementation review
4. `projects/components/bridge/docs/BRIDGE_ARCHITECTURE_DIAGRAMS.md` ← Visual architecture diagrams
5. `projects/components/bridge/CSV_BRIDGE_STATUS.md` ← CSV generator status (Phase 1 & 2)
6. `projects/components/bridge/docs/bridge_spec/bridge_index.md` ← Detailed specification

---

## Target Architecture: Intelligent Width-Aware Routing

**Core Principle:** Direct connections where possible, converters only where needed, no fixed crossbar width.

### Efficient Multi-Width Design

```
Master_A (64b)
  ├─ Direct → Slave_0 (64b)           [0 conversions, minimal latency]
  ├─ Conv(64→128) → Slave_1 (128b)    [1 conversion]
  └─ Conv(64→512) → Slave_2 (512b)    [1 conversion]

Master_B (512b)
  ├─ Conv(512→64) → Slave_0 (64b)     [1 conversion]
  ├─ Conv(512→128) → Slave_1 (128b)   [1 conversion]
  └─ Direct → Slave_2 (512b)          [0 conversions, full bandwidth]
```

**Router Logic:** Address decoder determines target slave, selects correctly-sized path for that master-slave pair.

### Why This Architecture

**❌ Naive Fixed-Width Approach (Don't Do This):**
```
Master (64b) → Upsize(64→256) → Fixed 256b Crossbar → Downsize(256→64) → Slave (64b)
```
- TWO conversions for same-width connections (wasteful!)
- Reduced bandwidth on narrow paths
- Unnecessary logic and area
- Higher latency

**✅ Intelligent Routing (Target):**
```
Master (64b) → Router → Direct Connection → Slave (64b)
```
- ZERO conversions for matching widths
- Full native bandwidth
- Minimal logic
- Lowest latency

### Per-Master Output Paths

Each master has N output paths (one per unique slave width it connects to):

```systemverilog
// Master_A connects to slaves at 64b, 128b, 512b
// Generate 3 output paths:

logic [63:0]  master_a_64b_wdata;   // For 64b slaves (direct)
logic [127:0] master_a_128b_wdata;  // For 128b slaves (via converter)
logic [511:0] master_a_512b_wdata;  // For 512b slaves (via converter)

// Router selects based on address decode:
always_comb begin
    case (decoded_slave_id)
        SLAVE_0: select master_a_64b_wdata;   // Slave_0 is 64b
        SLAVE_1: select master_a_128b_wdata;  // Slave_1 is 128b
        SLAVE_2: select master_a_512b_wdata;  // Slave_2 is 512b
    endcase
end
```

### Benefits

1. **Resource Efficient** - Only instantiate converters actually needed
2. **Maximum Performance** - Direct paths have zero conversion overhead
3. **Optimal Bandwidth** - No artificial width bottlenecks
4. **Lower Latency** - Minimal logic in critical path for matching widths
5. **Scalable** - Works for any combination of master/slave widths

### Implementation Status

**Current State:** Fixed-width crossbar with master-side upsizing (Phase 1 architecture)
**Target State:** Intelligent per-master multi-width routing (your vision)
**Migration:** Requires generator architecture rework (see TASKS.md)

---

## 🚨 CRITICAL RULE #0: RTL Regeneration Requirements

**⚠️ READ THIS FIRST - FAILURE TO FOLLOW CAUSES TEST FAILURES ⚠️**

### The Golden Rule

**ALL generated RTL files MUST be deleted and regenerated together whenever ANY generator code changes.**

### Why This Is Non-Negotiable

Generated RTL files have interdependencies:
- `bridge_axi4_flat_*.sv` may be instantiated by `bridge_ooo_with_arbiter.sv`
- `bridge_wrapper_*.sv` may wrap `bridge_axi4_flat_*.sv`
- Generator changes affect signal names, port widths, interface structure
- **Partial regeneration creates version mismatches that cause silent failures**

### Real Example (This Session)

```bash
# ❌ WHAT WENT WRONG:
1. Updated bridge_address_arbiter.py (address decode logic)
2. Regenerated ONLY bridge_axi4_flat_5x3.sv
3. Did NOT regenerate bridge_ooo_with_arbiter.sv (wrapper)
4. Result: All tests that were passing now FAIL
5. Cause: Version mismatch between wrapper and core bridge

# ✅ WHAT SHOULD HAVE BEEN DONE:
1. Updated bridge_address_arbiter.py
2. Delete ALL generated files:
   rm rtl/bridge_axi4_flat_*.sv
   rm rtl/bridge_ooo_*.sv
   rm rtl/bridge_wrapper_*.sv
3. Regenerate ALL bridges from scratch
4. Run ALL tests to verify
```

### Generator Files That Trigger Full Regeneration

Any change to these files requires regenerating ALL bridges:

- ✅ `bridge_generator.py` - Core bridge generator
- ✅ `bridge_csv_generator.py` - CSV-based generator
- ✅ `bridge_address_arbiter.py` - Address decode logic
- ✅ `bridge_channel_router.py` - Channel routing
- ✅ `bridge_response_router.py` - Response routing
- ✅ `bridge_amba_integrator.py` - AMBA integration
- ✅ `bridge_wrapper_generator.py` - Wrapper generation
- ✅ **ANY** Python file in `projects/components/bridge/bin/`

### The Regeneration Workflow

```bash
# Step 1: Make generator code changes
vim bridge_address_arbiter.py

# Step 2: Delete ALL generated RTL (be aggressive!)
cd projects/components/bridge/rtl
rm bridge_axi4_flat_*.sv
rm bridge_ooo*.sv
rm bridge_wrapper_*.sv
# Verify deletion
ls *.sv  # Should only show manually-written files like bridge_cam.sv

# Step 3: Regenerate everything
cd ../bin
./regenerate_all_bridges.sh  # If script exists
# OR manually regenerate each topology needed

# Step 4: Run ALL tests
cd ../dv/tests
pytest -v  # ALL tests, not just the one you think changed

# Step 5: Verify git diff makes sense
git diff ../rtl/  # Review all changes
```

### Symptoms of Version Mismatch

If you see these symptoms, you probably did partial regeneration:

- ❌ Tests that previously passed now fail
- ❌ "Signal not found" errors in simulation
- ❌ Port width mismatches in instantiation
- ❌ Address decode routing to wrong slaves
- ❌ Missing debug signals (dbg_*)
- ❌ Unexpected compile errors in working code

### Think Like a Compiler Developer

**Generated RTL = Compiled Object Files**

When you update a compiler, you don't selectively recompile - you `make clean && make all`.

When you update a generator, you don't selectively regenerate - you **delete all and regenerate all**.

### Exception: Hand-Written RTL

These files are **never** regenerated:
- `bridge_cam.sv` - CAM module (hand-written)
- Any file in `rtl/` that is NOT generated

Check file headers - generated files say "Generated by: bridge_generator.py"

---

## ⚠️ MANDATORY: Project Organization Pattern

**THIS SUBSYSTEM MUST FOLLOW THE RAPIDS/AMBA ORGANIZATIONAL PATTERN - NO EXCEPTIONS**

### Required Directory Structure

```
projects/components/bridge/
├── bin/                           # Bridge-specific tools (generators, scripts)
│   └── bridge_generator.py       # AXI4 crossbar generator
├── docs/                          # Design documentation
├── dv/                            # Design Verification (MANDATORY structure)
│   ├── tbclasses/                 # Testbench classes (MANDATORY - TB classes here!)
│   │   ├── __init__.py
│   │   └── bridge_axi4_flat_tb.py  # Reusable TB class
│   ├── components/                # Bridge-specific BFMs (if needed)
│   │   └── __init__.py
│   ├── scoreboards/               # Bridge-specific scoreboards (if needed)
│   │   └── __init__.py
│   └── tests/                     # All test files (test runners only)
│       ├── conftest.py            # Pytest configuration (MANDATORY)
│       ├── fub_tests/             # Functional unit block tests
│       │   └── basic/             # Basic bridge tests
│       ├── integration_tests/     # Multi-bridge integration
│       └── system_tests/          # Full system tests
├── rtl/                           # RTL source files
│   └── generated/                 # Generated bridge crossbars
├── CLAUDE.md                      # This file
├── PRD.md                         # Product requirements
└── IMPLEMENTATION_STATUS.md       # Development status
```

### Testbench Class Location (MANDATORY)

**❌ WRONG:** Testbench class in test file
```python
# projects/components/bridge/dv/tests/test_bridge_axi4_2x2.py
class BridgeAXI4FlatTB:  # ❌ WRONG LOCATION!
    """Embedded TB - NOT REUSABLE"""
```

**✅ CORRECT:** Testbench class in PROJECT AREA dv/tbclasses/
```python
# projects/components/bridge/dv/tbclasses/bridge_axi4_flat_tb.py
class BridgeAXI4FlatTB(TBBase):  # ✅ CORRECT LOCATION!
    """Reusable TB class - used across all bridge tests"""
```

**CRITICAL:** TB classes are PROJECT-SPECIFIC and MUST be in the project area (`projects/components/{name}/dv/tbclasses/`), NOT in the framework (`bin/CocoTBFramework/`).

### Test File Pattern (MANDATORY)

Test files MUST follow this structure:

```python
# projects/components/bridge/dv/tests/fub_tests/basic/test_bridge_axi4_2x2.py

import os
import pytest
import cocotb
from cocotb_test.simulator import run

# ✅ IMPORT testbench class from PROJECT AREA
import sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../../..'))
from projects.components.bridge.dv.tbclasses.bridge_axi4_flat_tb import BridgeAXI4FlatTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

# ===========================================================================
# COCOTB TEST FUNCTIONS - Prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit='us')
async def cocotb_test_basic_routing(dut):
    """Test basic address routing"""
    tb = BridgeAXI4FlatTB(dut, num_masters=2, num_slaves=2)  # ✅ Import TB
    await tb.setup_clocks_and_reset()
    result = await tb.test_basic_routing()
    assert result, "Basic routing test failed"

# More cocotb test functions...

# ===========================================================================
# PARAMETER GENERATION - At bottom of file
# ===========================================================================

def generate_bridge_test_params():
    """Generate test parameters for bridge tests"""
    return [
        # (num_masters, num_slaves, data_width, addr_width, id_width)
        (2, 2, 32, 32, 4),
        (4, 4, 32, 32, 4),
    ]

bridge_params = generate_bridge_test_params()

# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - At bottom of file
# ===========================================================================

@pytest.mark.bridge
@pytest.mark.routing
@pytest.mark.parametrize("num_masters, num_slaves, data_width, addr_width, id_width", bridge_params)
def test_basic_routing(request, num_masters, num_slaves, data_width, addr_width, id_width):
    """Pytest wrapper for basic routing test"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../rtl'
    })

    # ... setup verilog_sources, parameters, etc ...

    run(
        verilog_sources=verilog_sources,
        toplevel=f"bridge_axi4_flat_{num_masters}x{num_slaves}",
        module=module,
        testcase="cocotb_test_basic_routing",  # ← cocotb function name
        parameters=rtl_parameters,
        sim_build=sim_build,
        # ...
    )
```

---

## Critical Rules for This Subsystem

### Rule #0: Attribution Format for Git Commits

**IMPORTANT:** When creating git commit messages for Bridge documentation or code:

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Rationale:** Bridge receives AI assistance for structure and clarity, while design concepts and architectural decisions remain human-authored.

### Rule #0.1: Testbench Architecture - MANDATORY SEPARATION

**⚠️ THIS IS A HARD REQUIREMENT - NO EXCEPTIONS ⚠️**

**NEVER embed testbench classes inside test runner files!**

The same testbench logic will be reused across multiple test scenarios. Having testbench code only in test files makes it COMPLETELY WORTHLESS for reuse.

**MANDATORY Structure:**

```
projects/components/bridge/
├── dv/
│   ├── tbclasses/                   # TB classes HERE (not in framework!)
│   │   ├── __init__.py
│   │   └── bridge_axi4_flat_tb.py  ← REUSABLE TB CLASS
│   ├── components/                  # Bridge-specific BFMs (if needed)
│   │   └── __init__.py
│   ├── scoreboards/                 # Bridge-specific scoreboards
│   │   └── __init__.py
│   └── tests/                       # Test runners
│       ├── conftest.py              ← MANDATORY pytest config
│       ├── fub_tests/
│       │   └── basic/
│       │       └── test_bridge_axi4_2x2.py  ← TEST RUNNER ONLY (imports TB)
│       ├── integration_tests/
│       │   └── test_bridge_multiport.py     ← TEST RUNNER ONLY
│       └── system_tests/
│           └── test_bridge_system.py         ← TEST RUNNER ONLY
```

**Why This Matters:**

1. **Reusability**: Same TB class used in:
   - Unit tests (`fub_tests/`)
   - Integration tests (`integration_tests/`)
   - System-level tests (`system_tests/`)
   - User projects (external imports)

2. **Maintainability**: Fix bug once in TB class, all tests benefit

3. **Composition**: TB classes can inherit/compose for complex scenarios

---

### Rule #1: All Testbenches Inherit from TBBase

**Every testbench class MUST inherit from TBBase:**

```python
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class BridgeAXI4FlatTB(TBBase):
    """Testbench for Bridge crossbar - inherits base functionality"""

    def __init__(self, dut, num_masters=2, num_slaves=2, **kwargs):
        super().__init__(dut)
        # Bridge-specific initialization
```

**TBBase Provides:**
- Clock management (`start_clock`, `wait_clocks`)
- Reset utilities (`assert_reset`, `deassert_reset`)
- Logging (`self.log`)
- Progress tracking (`mark_progress`)
- Safety monitoring (timeouts, memory limits)

---

### Rule #2: Mandatory Testbench Methods

**Every testbench class MUST implement these three methods:**

```python
async def setup_clocks_and_reset(self):
    """Complete initialization - starts clocks and performs reset"""
    await self.start_clock('aclk', freq=10, units='ns')

    # Set config signals before reset (if needed)
    # self.dut.cfg_param.value = initial_value

    # Reset sequence
    await self.assert_reset()
    await self.wait_clocks('aclk', 10)
    await self.deassert_reset()
    await self.wait_clocks('aclk', 5)

async def assert_reset(self):
    """Assert reset signal (active-low for AXI4)"""
    self.dut.aresetn.value = 0

async def deassert_reset(self):
    """Deassert reset signal"""
    self.dut.aresetn.value = 1
```

**Why Required:**
- Consistency across all testbenches
- Reusability for mid-test resets
- Clear test structure and intent

---

### Rule #3: Use GAXI Components for Protocol Handling

**For Bridge testing, use GAXI Master/Slave components for AXI4 channel handling:**

```python
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.axi4.axi4_field_configs import AXI4FieldConfigHelper

# ✅ CORRECT: Use GAXI for AXI4 channels
self.aw_master = GAXIMaster(
    dut=dut,
    title="AW_M0",
    prefix="s0_axi4_",
    clock=clock,
    field_config=AXI4FieldConfigHelper.create_aw_field_config(id_width, addr_width, 1),
    pkt_prefix="aw",
    multi_sig=True,
    log=log
)
```

**Never manually drive AXI4 valid/ready handshakes** - Use GAXI components.

---

### Rule #4: Queue-Based Verification

**For simple in-order verification, use direct monitor queue access:**

```python
# ✅ CORRECT: Direct queue access
aw_pkt = self.aw_slave._recvQ.popleft()
w_pkt = self.w_slave._recvQ.popleft()

# Verify
assert aw_pkt.addr == expected_addr
assert w_pkt.data == expected_data

# ❌ WRONG: Memory model for simple test
memory_model = MemoryModel()  # Unnecessary complexity
```

**When to Use Memory Models:**
- ❌ Simple in-order tests → Use queue access
- ❌ Single-master systems → Use queue access
- ✅ Complex out-of-order scenarios → Memory model may help
- ✅ Multi-master with address overlap → Memory model tracks state

---

## TOML/CSV-Based Bridge Generator (Phase 2 Complete)

### Overview

The Bridge generator creates parameterized SystemVerilog crossbars from TOML configuration files with CSV connectivity matrices, eliminating manual RTL editing for complex interconnects.

**Key Benefits:**
- **Human-readable configuration** - TOML for ports, CSV for connectivity
- **Custom signal prefixes** - Each port has unique prefix (rapids_m_axi_, apb0_, etc.)
- **Channel-specific masters** - Write-only (wr), read-only (rd), or full (rw)
- **Interface modules** - Timing isolation via axi4_master/slave wrappers with configurable skid depths
- **Automatic converters** - Width and protocol conversion inserted automatically
- **Resource efficient** - Only generates needed channels and converters

### Quick Start

**1. Create bridge_mybridge.toml:**
```toml
[bridge]
  name = "bridge_mybridge"
  description = "Custom bridge example"

  # Default skid buffer depths (can be overridden per port)
  defaults.skid_depths = {ar = 2, r = 4, aw = 2, w = 4, b = 2}

  masters = [
    {name = "cpu", prefix = "cpu_m_axi", id_width = 4, addr_width = 32, data_width = 64, user_width = 1,
     interface = {type = "axi4_master"}},
    {name = "dma", prefix = "dma_m_axi", id_width = 4, addr_width = 32, data_width = 512, user_width = 1,
     interface = {type = "axi4_master", skid_depths = {ar = 4, r = 8, aw = 4, w = 8, b = 4}}}
  ]

  slaves = [
    {name = "ddr", prefix = "ddr_s_axi", id_width = 4, addr_width = 32, data_width = 512, user_width = 1,
     base_addr = 0x00000000, addr_range = 0x80000000, interface = {type = "axi4_slave"}},
    {name = "sram", prefix = "sram_s_axi", id_width = 4, addr_width = 32, data_width = 256, user_width = 1,
     base_addr = 0x80000000, addr_range = 0x80000000, interface = {type = "axi4_slave"}}
  ]
```

**2. Create bridge_mybridge_connectivity.csv:**
```csv
master\slave,ddr,sram
cpu,1,1
dma,1,1
```

**3. Generate bridge:**
```bash
cd projects/components/bridge/bin
python3 bridge_generator.py --ports test_configs/bridge_mybridge.toml
# Auto-finds bridge_mybridge_connectivity.csv

# Or use bulk generation
python3 bridge_generator.py --bulk bridge_batch.csv
```

**Result:** Complete SystemVerilog module with:
- Custom port prefixes per port
- Timing isolation via interface wrappers
- Only needed AXI4 channels (wr/rd/rw optimized)
- Width converters for data mismatches
- Internal crossbar instantiation
- APB/AXI4-Lite converter integration points

### Configuration Format Details

**TOML Port Configuration:**

The primary format is now **TOML** (preferred over CSV for better structure and interface configuration):

**Port Specifications:**
- `name` - Unique identifier (cpu, dma, ddr, etc.)
- `prefix` - Signal prefix (cpu_m_axi_, ddr_s_axi_, etc.)
- `id_width` - AXI4 ID width in bits
- `addr_width` - Address width in bits
- `data_width` - Data width in bits (32, 64, 128, 256, 512)
- `user_width` - AXI4 user signal width
- `base_addr` - Slave base address (slaves only)
- `addr_range` - Slave address range (slaves only)
- `interface` - Interface wrapper configuration (optional)
  - `type` - "axi4_master", "axi4_slave", "axi4_master_mon", "axi4_slave_mon", or omit for direct connection
  - `skid_depths` - Per-channel buffer depths: {ar, r, aw, w, b} (valid: 2, 4, 6, 8)

**CSV Connectivity Matrix:**
```csv
master\slave,slave0,slave1,slave2
master0,1,0,1
master1,0,1,1
```
- `1` = connected, `0` = not connected
- Partial connectivity supported (not all masters to all slaves)
- Auto-detected based on TOML filename: `bridge_name.toml` → `bridge_name_connectivity.csv`

**Legacy CSV Format:**

For backwards compatibility, the generator still supports CSV port files:
- See `test_configs/README.md` for migration guide from CSV to TOML
- TOML is now preferred for new bridges (better structure, interface config support)

### Channel-Specific Masters (Phase 2 Feature)

**Why Channel-Specific?**
Real hardware often has dedicated read or write masters. Generating all 5 AXI4 channels wastes resources:

**Traditional (wasteful):**
```systemverilog
// Write-only master gets unused read channels
input  logic [63:0]  rapids_descr_m_axi_awaddr,  // ✅ USED
input  logic [511:0] rapids_descr_m_axi_wdata,   // ✅ USED
output logic [7:0]   rapids_descr_m_axi_bid,     // ✅ USED
input  logic [63:0]  rapids_descr_m_axi_araddr,  // ❌ UNUSED (50% waste!)
output logic [511:0] rapids_descr_m_axi_rdata,   // ❌ UNUSED
```

**Channel-Specific (optimized):**
```csv
rapids_descr_wr,master,axi4,wr,rapids_descr_m_axi_,512,64,8,N/A,N/A
```

**Generated:**
```systemverilog
// Write-only master - only AW, W, B channels
input  logic [63:0]  rapids_descr_m_axi_awaddr,
input  logic [511:0] rapids_descr_m_axi_wdata,
output logic [7:0]   rapids_descr_m_axi_bid,
// ✅ NO READ CHANNELS (araddr, rdata, etc.)
```

**Resource Savings:**
- 40-60% fewer ports for dedicated masters
- Only necessary width converters instantiated
- Channel-aware direct connection wiring
- Faster synthesis, smaller netlists

### Example: RAPIDS-Style Configuration

**RAPIDS Architecture:**
- Descriptor write master (wr) - Writes descriptors to memory
- Sink write master (wr) - Writes incoming packets to memory
- Source read master (rd) - Reads outgoing packets from memory
- CPU master (rw) - Full access for configuration

**TOML Configuration (bridge_rapids.toml):**
```toml
[bridge]
  name = "bridge_rapids"
  description = "RAPIDS accelerator bridge"
  defaults.skid_depths = {ar = 2, r = 4, aw = 2, w = 4, b = 2}

  masters = [
    {name = "rapids_descr_wr", prefix = "rapids_descr_m_axi", channels = "wr",
     id_width = 8, addr_width = 64, data_width = 512, user_width = 1,
     interface = {type = "axi4_master"}},
    {name = "rapids_sink_wr", prefix = "rapids_sink_m_axi", channels = "wr",
     id_width = 8, addr_width = 64, data_width = 512, user_width = 1,
     interface = {type = "axi4_master"}},
    {name = "rapids_src_rd", prefix = "rapids_src_m_axi", channels = "rd",
     id_width = 8, addr_width = 64, data_width = 512, user_width = 1,
     interface = {type = "axi4_master"}},
    {name = "cpu", prefix = "cpu_m_axi", channels = "rw",
     id_width = 4, addr_width = 32, data_width = 64, user_width = 1,
     interface = {type = "axi4_master"}}
  ]

  slaves = [
    {name = "ddr", prefix = "ddr_s_axi", protocol = "axi4",
     id_width = 8, addr_width = 64, data_width = 512, user_width = 1,
     base_addr = 0x80000000, addr_range = 0x80000000,
     interface = {type = "axi4_slave"}},
    {name = "apb_periph", prefix = "apb0_", protocol = "apb",
     addr_width = 32, data_width = 32,
     base_addr = 0x00000000, addr_range = 0x00010000}
  ]
```

**Connectivity CSV (bridge_rapids_connectivity.csv):**
```csv
master\slave,ddr,apb_periph
rapids_descr_wr,1,0
rapids_sink_wr,1,0
rapids_src_rd,1,0
cpu,1,1
```

**Generated RTL Features:**
- rapids_descr_wr: 37 signals (write channels only) vs 61 signals (full) = **39% reduction**
- rapids_sink_wr: 37 signals (write channels only) vs 61 signals (full) = **39% reduction**
- rapids_src_rd: 24 signals (read channels only) vs 61 signals (full) = **61% reduction**
- cpu_master: Width converters for 64b→512b upsize (both wr and rd converters)
- ddr_controller: Direct 512b connection (no conversion)
- apb_periph0: APB converter placeholder (Phase 3)

### Common User Questions

**Q: "How do I generate a bridge?"**

**A: Three steps:**

1. Create TOML port configuration file
2. Create CSV connectivity matrix
3. Run bridge_generator.py

```bash
# Create bridge_mybridge.toml (port configuration)
# Create bridge_mybridge_connectivity.csv (connectivity matrix)

cd projects/components/bridge/bin
python3 bridge_generator.py --ports test_configs/bridge_mybridge.toml
# Auto-finds bridge_mybridge_connectivity.csv

# Or use bulk generation for multiple bridges
python3 bridge_generator.py --bulk bridge_batch.csv
```

**Q: "What's the difference between wr/rd/rw channels?"**

**A: Number of AXI4 channels generated:**

- **rw** (read/write) - All 5 channels: AW, W, B, AR, R
- **wr** (write-only) - 3 channels: AW, W, B (no read channels)
- **rd** (read-only) - 2 channels: AR, R (no write channels)

**Benefits:** 40-60% fewer ports for dedicated masters, less logic, faster synthesis

**Q: "Can I add timing isolation to ports?"**

**A: Yes, use interface configuration:**

```toml
masters = [
  {name = "cpu", prefix = "cpu_m_axi", ...,
   interface = {type = "axi4_master", skid_depths = {ar = 2, r = 4, aw = 2, w = 4, b = 2}}}
]
```

Available interface types:
- `"axi4_master"` - Timing isolation on master port
- `"axi4_slave"` - Timing isolation on slave port
- `"axi4_master_mon"` - Timing + monitoring
- `"axi4_slave_mon"` - Timing + monitoring
- Omit `interface` field for direct connection

**Q: "Can I mix AXI4 and APB slaves?"**

**A: Yes, use protocol field in TOML:**

```toml
slaves = [
  {name = "ddr", prefix = "ddr_s_axi", protocol = "axi4", ...},
  {name = "apb0", prefix = "apb0_", protocol = "apb", ...}
]
```

Generator inserts AXI2APB converters automatically (Phase 3 for full implementation).

**Q: "What if data widths don't match?"**

**A: Generator inserts width converters automatically:**

```toml
masters = [
  {name = "cpu", data_width = 64, ...},  # 64b master
]
slaves = [
  {name = "ddr", data_width = 512, ...}  # 512b slave
]
# Generator creates width converter: 64b → 512b
```

**Q: "Do all masters need to connect to all slaves?"**

**A: No, use partial connectivity in CSV:**

```csv
master\slave,ddr,sram,apb
rapids_descr,1,1,0     # Connects to ddr and sram only
cpu,1,1,1              # Connects to all three
```

### Generator Output Structure

**Generated File Contains:**

1. **Module Header** - Parameterized with NUM_MASTERS, NUM_SLAVES, widths
2. **Port Declarations** - Custom prefix per port, channel-specific signals
3. **Internal Signals** - Crossbar interface arrays (xbar_m_*, xbar_s_*)
4. **Width Converters** - Master-side upsize instances (channel-aware)
5. **Crossbar Instance** - Internal AXI4 full crossbar
6. **Direct Connections** - For matching-width interfaces
7. **APB Converters** - Placeholder TODO comments (Phase 3)

**Example Output Size:**
- Simple 2x2 bridge: ~400 lines
- Complex 5x3 with mixed protocols: ~900 lines
- Includes comprehensive comments and structure

### Testing Generated Bridges

**For Pure AXI4 Bridges (Working Now):**
```bash
# Generate bridge
python3 bridge_csv_generator.py --ports ports.csv --connectivity conn.csv --name my_bridge --output ../rtl/

# Create testbench (use BridgeAXI4FlatTB from dv/tbclasses/)
cd ../dv/tests/fub_tests/basic
pytest test_my_bridge.py -v
```

**For Mixed AXI4/APB (Requires Phase 3):**
APB converter placeholders need implementation before end-to-end testing.

---

## Bridge Architecture Quick Reference

### Generated Bridge Crossbar Structure

```systemverilog
module bridge_axi4_flat_2x2 #(
    parameter NUM_MASTERS = 2,
    parameter NUM_SLAVES = 2,
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 32,
    parameter ID_WIDTH = 4
) (
    input  logic aclk,
    input  logic aresetn,

    // Master-side interfaces (slave ports on bridge)
    // AW, W, B, AR, R channels for each master

    // Slave-side interfaces (master ports on bridge)
    // AW, W, B, AR, R channels for each slave
);
```

### Key Features

1. **5-Channel Implementation:** Complete AW, W, B, AR, R routing
2. **Round-Robin Arbitration:** Per-slave arbitration with grant locking
3. **Transaction ID Tracking:** Distributed RAM for B/R response routing
4. **ID-Based Routing:** Enables out-of-order responses
5. **Configurable Parameters:** NxM topology, data/addr/ID widths

### Address Map

Default address map (configurable):
- Slave 0: 0x00000000 - 0x0FFFFFFF (256MB)
- Slave 1: 0x10000000 - 0x1FFFFFFF (256MB)
- Slave N: N * 0x10000000

---

## Test Organization

### Test Hierarchy

```
projects/components/bridge/dv/tests/
├── conftest.py              # Pytest configuration with fixtures
├── fub_tests/               # Functional unit block tests
│   └── basic/
│       ├── test_bridge_axi4_2x2.py       # Basic 2x2 tests
│       ├── test_bridge_axi4_4x4.py       # Full 4x4 tests
│       └── test_bridge_axi4_routing.py   # Routing tests
├── integration_tests/       # Multi-bridge scenarios
│   └── test_bridge_cascade.py
└── system_tests/            # Full system tests
    └── test_bridge_dma.py
```

### Test Levels

**Basic (FUB) Tests:**
- Individual bridge functionality
- Address routing
- ID tracking
- Arbitration

**Integration Tests:**
- Multi-bridge cascades
- Complex topologies
- Cross-bridge transactions

**System Tests:**
- Full DMA transfers
- Realistic traffic patterns
- Performance validation

---

## Common User Questions and Responses

### Q: "How does the Bridge work?"

**A: Direct answer:**

The Bridge AXI4 crossbar connects multiple AXI4 masters to multiple slaves:

1. **Address Decode (AW/AR):** Routes master requests to appropriate slave based on address
2. **Write Path:** AW → arbitration → slave, W follows locked grant
3. **Read Path:** AR → arbitration → slave, R returns via ID table
4. **Arbitration:** Per-slave round-robin with grant locking until burst complete
5. **Response Routing:** B/R responses use ID lookup tables (not grant-based)

**Key Features:**
- Out-of-order response support via ID tracking
- Burst-aware arbitration (grant locked until WLAST/RLAST)
- Configurable NxM topology
- Single-clock domain

**📖 See:**
- `projects/components/bridge/PRD.md` - Complete specification
- `projects/components/bridge/bin/bridge_generator.py` - Generator implementation

### Q: "How do I generate a Bridge?"

**A: Use the bridge_generator.py tool:**

```bash
cd projects/components/bridge/bin
python bridge_generator.py --masters 2 --slaves 4 --data-width 32 --addr-width 32 --id-width 4 --output ../rtl/bridge_axi4_flat_2x4.sv
```

**Generated files:**
- RTL: `projects/components/bridge/rtl/bridge_axi4_flat_<config>.sv`
- Contains complete 5-channel crossbar with ID tracking

### Q: "How do I test a Bridge?"

**A: Use the Bridge testbench class:**

```python
# Import from project area
import sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../../..'))
from projects.components.bridge.dv.tbclasses.bridge_axi4_flat_tb import BridgeAXI4FlatTB

@cocotb.test()
async def test_basic(dut):
    tb = BridgeAXI4FlatTB(dut, num_masters=2, num_slaves=2)
    await tb.setup_clocks_and_reset()

    # Send write to slave 0
    await tb.write_transaction(master_idx=0, address=0x00001000, data=0xDEADBEEF)

    # Verify routing
    assert len(tb.aw_slaves[0]._recvQ) > 0, "Slave 0 should receive AW"
```

**Run tests:**
```bash
cd projects/components/bridge/dv/tests/fub_tests/basic
pytest test_bridge_axi4_2x2.py -v
```

---

## Anti-Patterns to Avoid

### ❌ Anti-Pattern 1: Embedded Testbench Classes

```python
❌ WRONG: TB class in test file
class BridgeTB:
    """NOT REUSABLE - WRONG LOCATION"""

✅ CORRECT: Import from project area
import sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../../..'))
from projects.components.bridge.dv.tbclasses.bridge_axi4_flat_tb import BridgeAXI4FlatTB
```

### ❌ Anti-Pattern 2: Manual AXI4 Handshaking

```python
❌ WRONG: Manual signal driving
self.dut.s0_axi4_awvalid.value = 1
while self.dut.s0_axi4_awready.value == 0:
    await RisingEdge(self.clock)

✅ CORRECT: Use GAXI components
await self.aw_master.send(aw_pkt)
```

### ❌ Anti-Pattern 3: Memory Models for Simple Tests

```python
❌ WRONG: Unnecessary complexity
memory = MemoryModel()
memory.write(addr, data)
result = memory.read(addr)

✅ CORRECT: Direct queue verification
aw_pkt = self.aw_slave._recvQ.popleft()
assert aw_pkt.addr == expected_addr
```

---

## Quick Reference

### Finding Existing Components

```bash
# Bridge TB class (in PROJECT AREA, not framework!)
cat projects/components/bridge/dv/tbclasses/bridge_axi4_flat_tb.py

# Bridge generator
cat projects/components/bridge/bin/bridge_generator.py

# Test examples
ls projects/components/bridge/dv/tests/fub_tests/basic/
```

### Common Commands

```bash
# Generate 2x2 bridge
python projects/components/bridge/bin/bridge_generator.py --masters 2 --slaves 2 --output projects/components/bridge/rtl/bridge_axi4_flat_2x2.sv

# Run tests
pytest projects/components/bridge/dv/tests/fub_tests/basic/ -v

# Lint generated RTL
verilator --lint-only projects/components/bridge/rtl/bridge_axi4_flat_2x2.sv
```

---

## Remember

1. 🏗️ **MANDATORY: Testbench architecture** - TB classes in framework, tests import them
2. 📁 **MANDATORY: Directory structure** - Follow RAPIDS/AMBA pattern exactly
3. 📋 **MANDATORY: conftest.py** - Must exist in dv/tests/
4. 🎯 **Use GAXI components** - Never manually drive AXI4 handshakes
5. 📊 **Queue-based verification** - Simple tests use direct queue access
6. 🏛️ **Three-layer architecture** - TB (framework) + Test (runner) + Scoreboard (verification)
7. ⚙️ **Three mandatory methods** - setup_clocks_and_reset, assert_reset, deassert_reset
8. 🔍 **Search first** - Use existing components before creating new ones
9. 📈 **Test scalability** - Support basic/medium/full test levels
10. 💯 **100% success** - All tests must achieve 100% success rate

---

## PDF Generation Location

**IMPORTANT: PDF files should be generated in the docs directory:**
```
/mnt/data/github/rtldesignsherpa/projects/components/bridge/docs/
```

**Quick Command:** Use the provided shell script:
```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/bridge/docs
./generate_pdf.sh
```

The shell script will automatically:
1. Use the md_to_docx.py tool from bin/
2. Process the bridge_spec index file
3. Generate both DOCX and PDF files in the docs/ directory
4. Create table of contents and title page

**📖 See:** `bin/md_to_docx.py` for complete implementation details

---

**Version:** 1.0
**Last Updated:** 2025-10-18
**Maintained By:** RTL Design Sherpa Project
