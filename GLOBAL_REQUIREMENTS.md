# Global Hard Requirements for RTL Design Sherpa

**Version:** 1.0
**Created:** 2025-10-31
**Purpose:** Consolidated mandatory requirements extracted from all CLAUDE.md files

---

## Overview

This document consolidates all **MANDATORY** requirements found across repository CLAUDE.md files. These are **HARD REQUIREMENTS** that must be followed - not suggestions or guidelines.

**Sources Analyzed:**
- Root `/CLAUDE.md`
- `projects/components/CLAUDE.md`
- `projects/components/rapids/CLAUDE.md`
- `projects/components/stream/CLAUDE.md`
- `bin/CocoTBFramework/CLAUDE.md`
- `rtl/amba/CLAUDE.md`
- `rtl/common/CLAUDE.md`

---

## Category 1: RTL Standards

### 1.1 Reset Handling (MANDATORY - NO EXCEPTIONS)

**Requirement:** ALL RTL in projects/components/ MUST use standardized reset macros

**Pattern:**
```systemverilog
`include "reset_defs.svh"

`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        r_state <= IDLE;
    end else begin
        r_state <= w_next_state;
    end
)
```

**NOT Allowed:**
```systemverilog
// ❌ WRONG - Manual reset handling
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_state <= IDLE;
    end else begin
        r_state <= w_next_state;
    end
end
```

**Applies to:** projects/components/ area
**Source:** `projects/components/CLAUDE.md` Rule #0
**Tool:** `bin/update_resets.py` for conversion
**Status:** rtl/common/ and rtl/amba/ already compliant

---

### 1.2 FPGA Synthesis Attributes (MANDATORY)

**Requirement:** ALL memory arrays MUST have FPGA synthesis hints

**Pattern:**
```systemverilog
`ifdef XILINX
    (* ram_style = "auto" *)
`elsif INTEL
    /* synthesis ramstyle = "AUTO" */
`endif
logic [DATA_WIDTH-1:0] mem [DEPTH];
```

**Attributes:**
- Xilinx: `ram_style = "auto" | "block" | "distributed" | "ultra"`
- Intel: `ramstyle = "AUTO" | "M20K" | "MLAB" | "logic"`

**Applies to:** All memory array declarations
**Source:** `projects/components/CLAUDE.md` Rule #1

---

### 1.3 Array Syntax Standard (MANDATORY)

**Requirement:** Use `[DEPTH]` NOT `[0:DEPTH-1]`

**Pattern:**
```systemverilog
// ✅ CORRECT
logic [DATA_WIDTH-1:0] mem [DEPTH];

// ❌ WRONG
logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];
```

**Reason:** Iverilog compatibility, cleaner syntax
**Applies to:** All unpacked array declarations
**Source:** `projects/components/CLAUDE.md` Rule #2

---

### 1.4 SRAM Module Standards (MANDATORY)

**Requirement:** SRAM modules DO NOT have reset ports

**Pattern:**
```systemverilog
module simple_sram #(
    parameter int DATA_WIDTH = 32,
    parameter int DEPTH = 1024
) (
    input  logic clk,
    // NO rst_n port!
    // ... other ports
);
```

**Reason:**
- Real SRAM chips don't have reset pins
- FPGA block RAM doesn't reset contents
- Initialize via writes during system init

**Applies to:** All SRAM/memory modules
**Source:** `projects/components/CLAUDE.md` Rule #3

---

### 1.5 Reset Convention (STANDARD)

**Requirement:** ALWAYS use active-low asynchronous reset

**Signal Names:**
- `rst_n` - Active-low reset (projects/components/)
- `aresetn` - Active-low asynchronous reset (AMBA standard)
- `i_rst_n` - Active-low reset (rtl/common/)

**NOT Allowed:**
- `rst` (positive reset)
- `reset` (ambiguous polarity)

**Applies to:** All RTL modules
**Source:** Root `/CLAUDE.md`, `rtl/common/CLAUDE.md` Rule #3

---

## Category 2: Testbench Architecture

### 2.1 TB Location Requirements (MANDATORY)

**Requirement:** Project-specific TB classes MUST be in project area, NOT framework

**Directory Structure:**
```
✅ CORRECT:
projects/components/{name}/dv/tbclasses/{module}_tb.py

❌ WRONG:
bin/CocoTBFramework/tbclasses/{name}/{module}_tb.py
```

**Import Pattern:**
```python
# Add repo root to path
import os, sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

# Import from PROJECT AREA
from projects.components.rapids.dv.tbclasses.scheduler_tb import SchedulerTB

# Shared framework utilities
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_master import AXI4Master
```

**Applies to:** ALL project-specific testbenches
**Source:** Root `/CLAUDE.md`, `projects/components/CLAUDE.md` Rule #4, `rapids/CLAUDE.md` Rule #0.1, `stream/CLAUDE.md` Rule #0.1, `amba/CLAUDE.md` Rule #0

---

### 2.2 Three Mandatory TB Methods (MANDATORY)

**Requirement:** EVERY testbench class MUST implement these three methods

**Pattern:**
```python
class MyModuleTB(TBBase):
    async def setup_clocks_and_reset(self):
        """Complete initialization - starts clocks and performs reset"""
        await self.start_clock('clk', freq=10, units='ns')

        # Set config before reset (if needed)
        self.dut.cfg_param.value = initial_value

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

    async def assert_reset(self):
        """Assert reset signal"""
        self.dut.rst_n.value = 0  # Active-low

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.dut.rst_n.value = 1
```

**Why Required:**
- Consistency across all testbenches
- Reusability for mid-test resets
- Clear test structure and intent
- Configuration control (some RTL needs signals set BEFORE reset)

**Applies to:** ALL testbench classes
**Source:** Root `/CLAUDE.md`, `rapids/CLAUDE.md` Rule #0.5, `stream/CLAUDE.md` Rule #0.2, `CocoTBFramework/CLAUDE.md` Rule #3

---

### 2.3 TBBase Inheritance (MANDATORY)

**Requirement:** ALL testbench classes MUST inherit from TBBase

**Pattern:**
```python
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class MyModuleTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        # Testbench-specific initialization
```

**What TBBase Provides:**
- Clock management (`start_clock`, `wait_clocks`)
- Reset utilities (`assert_reset`, `deassert_reset`)
- Logging (`self.log`)
- Progress tracking (`mark_progress`)
- Common utilities (`convert_to_int`, `format_dec`)

**Applies to:** ALL testbench classes
**Source:** `CocoTBFramework/CLAUDE.md` Rule #2

---

### 2.4 Three-Layer Architecture (MANDATORY)

**Requirement:** Verification MUST be separated into three layers

**Layers:**

1. **Testbench (TB):** `projects/components/{name}/dv/tbclasses/{module}_tb.py`
   - Infrastructure + BFMs
   - Clock/reset control
   - Base test methods
   - NO verification logic

2. **Scoreboard:** `bin/CocoTBFramework/scoreboards/{protocol}/{module}_scoreboard.py`
   - Verification logic
   - Expected vs actual comparison
   - Coverage collection

3. **Test:** `projects/components/{name}/dv/tests/test_{module}.py`
   - Test intelligence
   - **Imports** TB class (does NOT define it)
   - Pytest wrappers
   - Scenario logic

**NEVER Embed TB Classes in Test Files**

**Applies to:** ALL verification code
**Source:** `amba/CLAUDE.md` Rule #0, `rapids/CLAUDE.md` Rule #0.1, `CocoTBFramework/CLAUDE.md` Rule #4

---

### 2.5 Queue-Based Verification (PREFERRED)

**Requirement:** Use direct queue access for simple tests, NOT memory models

**Pattern:**
```python
# ✅ CORRECT: Direct queue access
aw_pkt = self.aw_monitor._recvQ.popleft()
w_pkt = self.w_monitor._recvQ.popleft()

# Verify
assert aw_pkt.addr == expected_addr
assert w_pkt.data == expected_data

# ❌ WRONG: Memory model for simple test
memory_model = MemoryModel()
written_data = memory_model.read(addr, 4)  # Unnecessary complexity
```

**When to Use:**
- ✅ **Queue Access:** Simple in-order tests, single-master, no overlap
- ✅ **Memory Models:** Complex OOO scenarios, multi-master with address overlap

**Applies to:** Simple in-order verification scenarios
**Source:** `rapids/CLAUDE.md` Scoreboard Pattern, `CocoTBFramework/CLAUDE.md` Rule #5

---

## Category 3: Test Standards

### 3.1 Test Naming Convention (MANDATORY)

**Requirement:** Pytest function MUST match module name

**Pattern:**
```python
# Module: axi4_dwidth_converter_wr.sv

✅ CORRECT:
def test_axi4_dwidth_converter_wr(request, params):
    """Test for axi4_dwidth_converter_wr.sv"""
    ...

❌ WRONG:
def test_converter(request, params):  # Too generic!
    ...
```

**Why:** Prevents pytest collection conflicts between related modules

**Applies to:** ALL pytest test functions
**Source:** Root `/CLAUDE.md`

---

### 3.2 Test Pattern - CocoTB + Pytest (MANDATORY for projects/components/)

**Requirement:** Use two-tier pattern with cocotb_test_* prefix

**Pattern:**
```python
# 1. CocoTB test functions - prefix with "cocotb_test_*"
@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic(dut):  # ← cocotb_test_* prefix!
    """CocoTB test function - NOT collected by pytest"""
    tb = SimpleSRAMTB(dut)
    await tb.setup_clocks_and_reset()
    # ... test logic

# 2. Pytest wrapper - calls specific cocotb_test_* function
@pytest.mark.parametrize("addr_width, data_width", params)
def test_basic(request, addr_width, data_width):
    """Pytest wrapper - calls cocotb_test_basic"""
    run(
        # ... setup
        testcase="cocotb_test_basic",  # ← Explicitly specify
        # ... compilation args
    )
```

**Why:**
- Pytest collects only wrappers, not CocoTB functions
- Each wrapper calls ONE specific CocoTB function
- Allows parameter sweeps at pytest level

**Applies to:** ALL tests in projects/components/
**Source:** Root `/CLAUDE.md`

---

### 3.3 100% Success Requirement (MANDATORY)

**Requirement:** ALL tests MUST achieve 100% success rate

**Pattern:**
```python
# ❌ WRONG: Accepting partial success
assert success_rate >= 70  # "Good enough" - NO!

# ✅ CORRECT: Require 100% success
assert success_rate >= 100  # 100% required
```

**Rationale:**
- RTL is deterministic - 100% success is achievable
- Partial success indicates bugs or timing issues
- Lower thresholds mask real problems
- Tests must reliably catch regressions

**Applies to:** ALL tests
**Source:** `rapids/CLAUDE.md`, `CocoTBFramework/CLAUDE.md`

---

### 3.4 Simulation Timestamps in Logs (MANDATORY)

**Requirement:** ALL test log messages MUST include simulation time

**Pattern:**
```python
# ✅ CORRECT: Include simulation timestamp
self.log.info(f"@ {cocotb.utils.get_sim_time('ns')}ns: Beat {i}: data=0x{data:X}, s_ready={ready}, occupancy={occ}")

# ❌ WRONG: No simulation timestamp
self.log.info(f"Beat {i}: data=0x{data:X}, s_ready={ready}, occupancy={occ}")
```

**Output Example:**
```
2025-11-06 19:11:20,688 - INFO - @ 150ns: Beat 1: data=0xA000, s_ready=1, occupancy=0
2025-11-06 19:11:20,688 - INFO - @ 160ns: Beat 2: data=0xA001, s_ready=1, occupancy=1
2025-11-06 19:11:20,688 - INFO - @ 170ns: Beat 3: data=0xA002, s_ready=1, occupancy=2
2025-11-06 19:11:20,688 - INFO - @ 180ns: Beat 4 BLOCKED: s_ready=0, occupancy=3
```

**Why Critical:**
- Correlate test events with waveform timing
- Debug timing-sensitive failures
- Understand cycle-accurate behavior
- Match log messages to specific clock edges

**What Counts as "Simulation Time":**
- Use `cocotb.utils.get_sim_time('ns')` for nanoseconds
- Use `cocotb.utils.get_sim_time('ps')` for picoseconds
- Format: `@ {time}{unit}:` at START of message

**Anti-Pattern:**
```python
# ❌ WRONG: Only Python logging timestamp
self.log.info(f"Beat {i} completed")
# Output: "2025-11-06 19:11:20,688 - INFO - Beat 1 completed"
# Problem: Can't correlate with waveform!
```

**Applies to:** ALL test log messages showing DUT behavior
**Priority:** P0 - CRITICAL for debugging
**Source:** User feedback 2025-11-06

---

## Category 4: Framework Usage

### 4.1 Search Before Creating (MANDATORY)

**Requirement:** ALWAYS search existing modules/components BEFORE creating new

**Search Commands:**
```bash
# Search for existing RTL modules
find rtl/{subsystem}/ -name "*.sv" | xargs grep -l "keyword"

# Search for existing BFMs
find bin/CocoTBFramework/components/ -name "*.py" | xargs grep -l "class.*BFM"

# Search for existing TB classes
find bin/CocoTBFramework/tbclasses/ -name "*_tb.py"
```

**Decision Tree:**
- ✅ Exact match exists → Use it
- ✅ Close match exists → Adapt with parameters
- ⚠️ No match found → Document search, propose new
- ❌ Didn't search → STOP, go back and search

**Applies to:** RTL modules, BFMs, TB components
**Source:** `rtl/common/CLAUDE.md` Rule #1, `CocoTBFramework/CLAUDE.md` Rule #1

---

### 4.2 BFM Usage for Protocols (MANDATORY for RAPIDS)

**Requirement:** MUST use framework BFMs for all protocol interfaces

**BFM Selection:**
- **Custom valid/ready:** GAXI Master/Slave (`bin/CocoTBFramework/components/gaxi/`)
- **AXI4:** AXI4 Master/Slave (`bin/CocoTBFramework/components/axi4/`)
- **APB:** APB drivers (`bin/CocoTBFramework/components/apb/`)
- **AXI-Stream:** AXIS drivers (`bin/CocoTBFramework/components/axis4/`)

**NEVER:**
- ❌ Manually drive valid/ready handshakes
- ❌ Create custom protocol drivers when framework has them

**Applies to:** All RAPIDS FUB-level tests
**Source:** `rapids/CLAUDE.md` Rule #1

---

## Category 5: Documentation

### 5.1 No Emojis in Technical Docs (MANDATORY)

**Requirement:** No emojis in technical specifications

**Rationale:**
- Break PDF generation tools (LaTeX)
- Appear unprofessional in formal documentation
- Use plain text for all technical documentation

**Exception:** User explicitly requests emojis (rare)

**Applies to:** All technical documentation
**Source:** Root `/CLAUDE.md`

---

## Category 6: Project-Specific Requirements

### 6.1 RAPIDS Attribution Format

**Requirement:** Use specific attribution format for RAPIDS

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Applies to:** RAPIDS git commits only
**Source:** `rapids/CLAUDE.md` Rule #0

---

### 6.2 STREAM Attribution Format

**Requirement:** Use specific attribution format for STREAM

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Applies to:** STREAM git commits only
**Source:** `stream/CLAUDE.md` Rule #0

---

### 6.3 STREAM Tutorial Focus

**Requirement:** STREAM has intentional simplifications - DO NOT "fix" them

**Intentional Simplifications:**
1. ✅ Aligned addresses only - No alignment fixup logic
2. ✅ Length in beats - Not bytes or chunks
3. ✅ No circular buffers - Explicit chain termination only
4. ✅ No credit management - Simple transaction limits
5. ✅ Pure memory-to-memory - No network interfaces

**When users ask "Can we add alignment fixup?"**
- ✅ **Correct answer:** "STREAM intentionally keeps addresses aligned for tutorial simplicity. For complex alignment, see RAPIDS."
- ❌ **Wrong answer:** "Sure, let me add alignment logic..." (defeats tutorial purpose!)

**Applies to:** STREAM component only
**Source:** `stream/CLAUDE.md` Rule #0.1

---

## Summary by Priority

### P0 - Critical (Enforcement Required)

1. ✅ Reset macro usage (`projects/components/`)
2. ✅ TB location (project area, not framework)
3. ✅ Three mandatory TB methods
4. ✅ TBBase inheritance
5. ✅ Three-layer architecture
6. ✅ 100% test success requirement

### P1 - High Priority (Strong Recommendation)

7. ✅ FPGA synthesis attributes
8. ✅ Array syntax standard
9. ✅ SRAM module standards
10. ✅ Test naming convention
11. ✅ CocoTB + Pytest pattern
12. ✅ Queue-based verification

### P2 - Standard Practice (Best Practices)

13. ✅ Search before creating
14. ✅ BFM usage for protocols
15. ✅ Active-low reset convention
16. ✅ No emojis in technical docs

### P3 - Project-Specific

17. ✅ RAPIDS attribution format
18. ✅ STREAM attribution format
19. ✅ STREAM tutorial focus

---

## Compliance Checklist

Use this checklist when creating new RTL or testbenches:

**RTL Module:**
- [ ] Uses `ALWAYS_FF_RST` macro (projects/components/)
- [ ] Memory arrays have FPGA attributes
- [ ] Arrays use `[DEPTH]` syntax
- [ ] SRAM modules have no reset port
- [ ] Uses active-low reset (`rst_n` or `aresetn`)

**Testbench Class:**
- [ ] Located in `projects/components/{name}/dv/tbclasses/`
- [ ] Inherits from TBBase
- [ ] Implements `setup_clocks_and_reset()`
- [ ] Implements `assert_reset()`
- [ ] Implements `deassert_reset()`
- [ ] Uses framework BFMs (not manual handshaking)

**Test File:**
- [ ] Imports TB class from project area
- [ ] CocoTB functions prefixed with `cocotb_test_*`
- [ ] Pytest function matches module name
- [ ] Uses `testcase=` to specify CocoTB function
- [ ] Requires 100% success rate
- [ ] Uses queue-based verification (for simple tests)

**Documentation:**
- [ ] No emojis in technical specs
- [ ] Correct attribution format (if RAPIDS/STREAM)

---

## Enforcement

**These requirements are enforced via:**

1. **Code Review** - All PRs reviewed for compliance
2. **Automated Tools:**
   - `bin/update_resets.py` - Reset macro conversion
   - `bin/audit_signal_naming_conflicts.py` - Signal naming checks
3. **CI/CD Checks:**
   - Verilator linting
   - Pytest test execution
   - Test success rate validation
4. **Documentation:**
   - CLAUDE.md files per subsystem
   - PRD.md requirements per component

**Non-Compliance:**
- PRs will be REJECTED if they violate P0 requirements
- P1 violations require justification and approval
- P2/P3 violations should be corrected but may not block PR

---

## References

**Main Documentation:**
- `/CLAUDE.md` - Repository-wide guidance
- `/PRD.md` - Master requirements
- `projects/components/CLAUDE.md` - Project area standards
- `bin/CocoTBFramework/CLAUDE.md` - Framework patterns

**Subsystem Documentation:**
- `projects/components/rapids/CLAUDE.md` - RAPIDS guidance
- `projects/components/stream/CLAUDE.md` - STREAM guidance
- `rtl/amba/CLAUDE.md` - AMBA subsystem guidance
- `rtl/common/CLAUDE.md` - Common RTL library guidance

**Tools:**
- `bin/update_resets.py` - Reset macro conversion
- `bin/audit_signal_naming_conflicts.py` - Signal naming audit
- `bin/md_to_docx.py` - Documentation generation

---

**Version:** 1.0
**Last Updated:** 2025-10-31
**Maintained By:** RTL Design Sherpa Project
