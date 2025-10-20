# Claude Code Guide: Bridge Subsystem

**Version:** 1.0
**Last Updated:** 2025-10-18
**Purpose:** AI-specific guidance for working with Bridge subsystem

---

## Quick Context

**What:** AXI4 Bridge Crossbar - Configurable NxM crossbar for connecting multiple AXI4 masters to multiple slaves
**Status:** 🟡 Active development - Infrastructure complete, initial validation in progress
**Your Role:** Help users understand architecture, create tests, and validate functionality

**📖 Complete Specification:** `projects/components/bridge/PRD.md` ← **Always reference this for technical details**

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
