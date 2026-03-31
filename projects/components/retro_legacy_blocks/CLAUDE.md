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

# Claude Code Guide: Retro Legacy Blocks

**Version:** 2.0
**Last Updated:** 2025-10-29
**Purpose:** AI-specific guidance for working with Retro Legacy Blocks (RLB) peripheral blocks

---

## Quick Context

**What:** Collection of production-quality retro-compatible legacy peripherals
**Status:** 🟢 Active Development - HPET Production Ready, 12 more blocks planned
**Your Role:** Help users develop new legacy blocks, integrate existing blocks, understand RLB architecture

**📖 Complete Documentation:**
- `projects/components/retro_legacy_blocks/PRD.md` ← Master requirements for all blocks
- `projects/components/retro_legacy_blocks/README.md` ← Component overview and usage guide
- `docs/hpet_spec/hpet_index.md` ← HPET complete specification

**RLB Address Map:** Single APB entry point at `0x4000_0000`, 4KB windows for clean decode

---

## Critical Rules for All Blocks

### Rule #0: Attribution Format for Git Commits

**IMPORTANT:** When creating git commit messages for retro_legacy_blocks documentation or code:

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Rationale:** Retro Legacy Blocks receives AI assistance for structure and clarity, while design concepts and architectural decisions remain human-authored.

---

### Rule #0.1: Reset Macro Standards - MANDATORY FOR ALL BLOCKS

**⚠️ ALL BLOCKS MUST USE RESET MACROS - NO EXCEPTIONS ⚠️**

**Status:** HPET has been converted (2025-10-25). All future blocks MUST use reset macros from day one.

**Include in ALL new RTL files:**
```systemverilog
`include "reset_defs.svh"
```

**Standard Pattern:**
```systemverilog
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        r_state <= IDLE;
        r_counter <= '0;
    end else begin
        r_state <= w_next_state;
        r_counter <= r_counter + 1'b1;
    end
)
```

**HARD REQUIREMENT:**
1. **ALL new RTL files** MUST use reset macros from creation
2. **PRs will be REJECTED** if they contain manual `always_ff @(posedge clk or negedge rst_n)` patterns
3. **Use the conversion tool** if adapting existing code: `bin/update_resets.py`

**Why This Matters for RLB Peripherals:**
- FPGA-friendly reset inference (critical for timing closure)
- Consistent synthesis across Xilinx, Intel, and ASIC flows
- Single-point reset polarity control for IP reuse
- Better timing closure in complex systems

**See also:**
- `rtl/amba/includes/reset_defs.svh` - Complete macro definitions
- `projects/components/CLAUDE.md` Rule #0 - Repository-wide reset standards

---

### Rule #0.2: FPGA Synthesis Attributes - MANDATORY

**⚠️ ALL memory arrays MUST have FPGA synthesis hints ⚠️**

**Standard Pattern:**
```systemverilog
`ifdef XILINX
    (* ram_style = "auto" *)  // Let Xilinx decide block vs distributed
`elsif INTEL
    /* synthesis ramstyle = "AUTO" */  // Let Intel Quartus decide
`endif
logic [DATA_WIDTH-1:0] mem [DEPTH];  // Use [DEPTH], not [0:DEPTH-1]
```

**Why This Matters:**
- Prevents logic explosion for large memories
- Enables vendor-specific optimizations
- Cross-vendor compatibility (Xilinx, Intel/Altera)
- Proper FPGA resource inference

**See also:** `projects/components/CLAUDE.md` Rule #1 - FPGA synthesis attributes

---

### Rule #0.3: Testbench Architecture - MANDATORY SEPARATION

**⚠️ THIS IS A HARD REQUIREMENT - NO EXCEPTIONS ⚠️**

**NEVER embed testbench classes inside test runner files!**

**MANDATORY Structure:**
```
projects/components/retro_legacy_blocks/dv/
├── tbclasses/{block}/             # ★ Block-specific TB classes HERE
│   ├── {block}_tb.py              # Main testbench
│   ├── {block}_tests_basic.py     # Basic test suite
│   ├── {block}_tests_medium.py    # Medium test suite
│   └── {block}_tests_full.py      # Full test suite
│
└── tests/{block}/                 # Test runners (import TB classes)
    ├── test_apb_{block}.py        # Test runner only
    └── conftest.py                # Pytest configuration
```

**Import Pattern (CORRECT):**
```python
# Import framework utilities (PYTHONPATH includes bin/)
import os, sys
from TBClasses.shared.utilities import get_repo_root, get_paths, create_view_cmd
from TBClasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import from PROJECT AREA (not framework!)
from projects.components.retro_legacy_blocks.dv.tbclasses.{block}.{block}_tb import {Block}TB
from projects.components.retro_legacy_blocks.dv.tbclasses.{block}.{block}_tests_basic import {Block}BasicTests
```

**Why This Matters:**
1. **Reusability**: Same TB class used in basic/medium/full tests
2. **Maintainability**: Fix bug once in TB class, all tests benefit
3. **Composition**: TB classes can inherit/compose for complex scenarios
4. **Consistency**: All blocks follow same pattern

**See also:** Root `/CLAUDE.md` Section "Organizational Requirements"

---

### Rule #0.4: Test Hierarchy - 3 Levels Required

**Every block must have 3 test levels:**

1. **Basic Tests (Target: 4-6 tests, 100% pass rate)**
   - Register access (read/write)
   - Core functionality enable/disable
   - Simple operation verification
   - Interrupt generation
   - **Duration:** <30 seconds per test

2. **Medium Tests (Target: 5-8 tests, 100% pass rate)**
   - Mode switching (e.g., one-shot vs periodic)
   - Multi-feature interaction
   - 64-bit operations (if applicable)
   - Configuration edge cases
   - **Duration:** 30-90 seconds per test

3. **Full Tests (Target: 3-5 tests, ≥95% pass rate)**
   - Stress testing (all resources active)
   - Clock domain crossing variants (if CDC supported)
   - Corner cases and timing edge cases
   - Long-duration operations
   - **Duration:** 90+ seconds per test

**Test Level Selection:**
```python
# Use TEST_LEVEL environment variable
test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

if test_level == 'basic':
    num_operations = 10
elif test_level == 'medium':
    num_operations = 50
else:  # full
    num_operations = 200
```

**Why This Hierarchy:**
- **Basic:** Quick smoke tests for CI/PR checks
- **Medium:** Standard functional validation
- **Full:** Comprehensive coverage for releases

---

### Rule #0.5: Register Generation - Use PeakRDL

**Preferred approach for ALL new blocks:**

1. Define registers in SystemRDL (`.rdl` file)
2. Generate RTL using PeakRDL regblock
3. Create wrapper module connecting registers to core logic
4. Use edge detection for write strobes (not level)

**Benefits:**
- Consistent register interface across all blocks
- Auto-generated documentation
- Reduced manual RTL errors
- Easy register map changes

**Example SystemRDL:**
```systemverilog
// gpio_regs.rdl
regfile gpio_regs {
    name = "GPIO Register File";
    desc = "General Purpose I/O control registers";

    reg {
        name = "GPIO Direction";
        field {
            sw = rw;
            hw = r;
        } direction[32] = 32'h0;
    } gpio_dir @ 0x00;

    reg {
        name = "GPIO Output";
        field {
            sw = rw;
            hw = r;
        } output[32] = 32'h0;
    } gpio_out @ 0x04;

    reg {
        name = "GPIO Input";
        field {
            sw = r;
            hw = w;
        } input[32] = 32'h0;
    } gpio_in @ 0x08;
};
```

**Generation:**
```bash
cd rtl/{block}/peakrdl
peakrdl regblock {block}_regs.rdl --cpuif apb4 -o ../
```

**See:** HPET implementation (`rtl/hpet/peakrdl/`) for complete example

---

## Block Development Workflow

### Adding a New Block

**1. Create Directory Structure:**
```bash
cd projects/components/retro_legacy_blocks

# RTL
mkdir -p rtl/{block}/peakrdl
mkdir -p rtl/{block}/filelists

# DV
mkdir -p dv/tbclasses/{block}
mkdir -p dv/tests/{block}

# Docs
mkdir -p docs/{block}_spec
```

**2. Create RTL Files:**
```
rtl/{block}/
├── apb_{block}.sv          # Top-level wrapper
├── {block}_core.sv         # Core logic
├── {block}_config_regs.sv  # Register wrapper
├── {block}_regs_pkg.sv     # PeakRDL generated package
├── {block}_regs.sv         # PeakRDL generated registers
├── peakrdl/
│   ├── {block}_regs.rdl    # SystemRDL specification
│   └── README.md           # Generation instructions
├── filelists/
│   ├── component           # Component-level filelist
│   └── integration         # Integration-level filelist
├── Makefile                # Build targets
└── README.md               # RTL documentation
```

**3. Create Testbench Classes:**
```python
# dv/tbclasses/{block}/{block}_tb.py
from TBClasses.shared.tbbase import TBBase

class {Block}TB(TBBase):
    """Testbench for {Block} peripheral"""

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.pclk = dut.pclk
        self.presetn = dut.presetn
        # Block-specific initialization

    async def setup_clocks_and_reset(self):
        """Complete initialization - MANDATORY METHOD"""
        await self.start_clock('pclk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)

    async def assert_reset(self):
        """Assert reset - MANDATORY METHOD"""
        self.presetn.value = 0  # Active-low APB reset

    async def deassert_reset(self):
        """Deassert reset - MANDATORY METHOD"""
        self.presetn.value = 1

    async def write_register(self, addr, data):
        """Write to APB register"""
        # APB write transaction

    async def read_register(self, addr):
        """Read from APB register"""
        # APB read transaction
        return data
```

**4. Create Test Suites:**
```python
# dv/tbclasses/{block}/{block}_tests_basic.py
class {Block}BasicTests:
    """Basic test suite for {Block}"""

    def __init__(self, tb):
        self.tb = tb

    async def test_register_access(self):
        """Test basic register read/write"""
        # Test implementation
        return True

    async def test_enable_disable(self):
        """Test block enable/disable"""
        # Test implementation
        return True
```

**5. Create Test Runner:**
```python
# dv/tests/{block}/test_apb_{block}.py
import os, sys

# Import framework utilities (PYTHONPATH includes bin/)
from TBClasses.shared.utilities import get_repo_root

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.retro_legacy_blocks.dv.tbclasses.{block}.{block}_tb import {Block}TB
from projects.components.retro_legacy_blocks.dv.tbclasses.{block}.{block}_tests_basic import {Block}BasicTests

@cocotb.test()
async def cocotb_test_basic(dut):
    tb = {Block}TB(dut)
    await tb.setup_clocks_and_reset()
    tests = {Block}BasicTests(tb)
    result = await tests.test_register_access()
    assert result, "Basic test failed"

@pytest.mark.parametrize("params", generate_test_params())
def test_{block}(request, params):
    # Pytest wrapper
    run(verilog_sources=..., module=module, ...)
```

**6. Create conftest.py:**
```python
# dv/tests/{block}/conftest.py
import os
import pytest
import logging

def pytest_configure(config):
    """Configure pytest for {block} tests"""
    # Create logs directory
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    # Register markers
    config.addinivalue_line("markers", "basic: Basic functionality tests")
    config.addinivalue_line("markers", "medium: Extended feature tests")
    config.addinivalue_line("markers", "full: Stress and corner case tests")
```

**7. Update Documentation:**
- Add block section to `PRD.md`
- Create `docs/{block}_spec/{block}_index.md`
- Update `README.md` status table

---

## HPET-Specific Guidance

### HPET Quick Reference

**Status:** ✅ Production Ready (5/6 configurations 100% passing)
**RTL Location:** `rtl/hpet/`
**Test Location:** `dv/tests/hpet/`

### Critical HPET Rules

#### Rule #1: Timer Cleanup is MANDATORY

**⚠️ ALWAYS Reset Counter Between Tests ⚠️**

```python
# ✅ CORRECT: Clean up at end of test
async def test_64bit_counter(self):
    await self.tb.write_register(HPET_COUNTER_LO, 0xFFFFFFFF)
    # ... test logic ...

    # MANDATORY cleanup
    await self.tb.write_register(HPET_COUNTER_LO, 0x0)
    await self.tb.write_register(HPET_COUNTER_HI, 0x0)
    return True
```

**Why:** Test leaves counter at high value, next test expects counter at 0. Timer 2+ won't fire if counter starts high.

#### Rule #2: Timer Timeout Calculations

**Account for counter starting value when setting timeouts:**

```python
# Calculate timeout based on timer periods
timer_configs = [
    {"period": 100},  # Timer 0 fires at 100
    {"period": 200},  # Timer 1 fires at 200
    {"period": 700},  # Timer 2 fires at 700 (needs most time)
]

# 3x safety margin for latest timer
timeout_ns = max(cfg["period"] for cfg in timer_configs) * 3
timeout_us = (timeout_ns + 999) // 1000
```

#### Rule #3: HPET Register Map

```
0x000: HPET_CONFIG          (enable, legacy_mapping)
0x004: HPET_STATUS          (timer interrupt status, W1C)
0x008: HPET_COUNTER_LO      (main counter bits [31:0], RW)
0x00C: HPET_COUNTER_HI      (main counter bits [63:32], RW)
0x010: HPET_CAPABILITIES    (num_timers, vendor_id, revision_id, RO)

Per-Timer Registers (i = 0 to NUM_TIMERS-1):
0x100 + i*0x20: TIMER[i]_CONFIG         (enable, int_enable, type, size)
0x104 + i*0x20: TIMER[i]_COMPARATOR_LO  (bits [31:0], RW)
0x108 + i*0x20: TIMER[i]_COMPARATOR_HI  (bits [63:32], RW)
```

#### Rule #4: HPET Timer Modes

**One-Shot:**
- Timer fires once when counter >= comparator
- Does NOT automatically reload
- Must reconfigure for next fire

**Periodic:**
- Timer fires repeatedly
- Comparator auto-increments by period value
- Fires indefinitely until disabled

### HPET Common Issues

**Issue: Timer Not Firing**
1. ✅ HPET enabled? (HPET_CONFIG bit 0)
2. ✅ Timer enabled? (TIMER_CONFIG bit 0)
3. ✅ Comparator set correctly?
4. ✅ Counter incrementing?
5. ✅ Counter will reach comparator?
6. ✅ Interrupt enable set? (TIMER_CONFIG bit 1)

**Issue: Tests Failing Inconsistently**
- Most common cause: Missing test cleanup (counter not reset)
- Solution: Add cleanup at end of EVERY test

**See:** Complete HPET guidance in `docs/hpet_spec/hpet_index.md`

---

## Common User Questions

### Q: "Which blocks are implemented?"

**A: Current status:**

| Block | Priority | Status | Address | Documentation |
|-------|----------|--------|---------|---------------|
| **HPET** | High | ✅ Production | 0x4000_0000-0x0FFF | ✅ Complete |
| **8259 PIC** | High | 📋 Planned | 0x4000_1000-0x1FFF | N/A |
| **8254 PIT** | High | 📋 Planned | 0x4000_2000-0x2FFF | N/A |
| **RTC** | Medium | 📋 Planned | 0x4000_3000-0x3FFF | N/A |
| **SMBus** | Medium | 📋 Planned | 0x4000_4000-0x4FFF | N/A |
| **PM/ACPI** | Medium | 📋 Planned | 0x4000_5000-0x5FFF | N/A |
| **IOAPIC** | Medium | 📋 Planned | 0x4000_6000-0x6FFF | N/A |
| GPIO | Medium | 📋 Planned | TBD | N/A |
| UART | Medium | 📋 Planned | TBD | N/A |
| SPI | Low | 📋 Planned | TBD | N/A |
| I2C | Low | 📋 Planned | TBD | N/A |
| Watchdog | Low | 📋 Planned | TBD | N/A |
| **Interconnect** | Low | 📋 Planned | 0x4000_F000-0xFFFF | N/A |

**📖 See:** `PRD.md` Section 3 for planned block details and Section 4.2 for complete address map

### Q: "How do I integrate a block in my design?"

**A: Each block has APB interface, example:**

```systemverilog
apb_hpet #(
    .NUM_TIMERS(3),
    .VENDOR_ID(16'h8086),
    .REVISION_ID(16'h0001),
    .CDC_ENABLE(0)
) u_hpet (
    // APB interface
    .pclk         (apb_clk),
    .presetn      (apb_rst_n),
    .paddr        (paddr),
    .psel         (psel_hpet),
    .penable      (penable),
    .pwrite       (pwrite),
    .pwdata       (pwdata),
    .prdata       (prdata_hpet),
    .pready       (pready_hpet),
    .pslverr      (pslverr_hpet),
    // Block-specific signals
    .hpet_clk     (timer_clk),
    .hpet_rst_n   (timer_rst_n),
    .timer_irq    (timer_irq[2:0])
);
```

**📖 See:** `README.md` for integration examples

### Q: "What's the RLB wrapper goal?"

**A: Create unified subsystem combining all blocks with single APB entry point:**

```
RLB Wrapper Architecture:

Single APB Slave → APB Decoder/Bridge → Individual Blocks
(0x4000_0000)    (4KB window decode)   (HPET, 8259, 8254, etc.)
```

**Address Map (4KB windows):**
- `0x4000_0000-0x0FFF`: HPET
- `0x4000_1000-0x1FFF`: 8259 PIC
- `0x4000_2000-0x2FFF`: 8254 PIT
- `0x4000_3000-0x3FFF`: RTC
- `0x4000_4000-0x4FFF`: SMBus
- `0x4000_5000-0x5FFF`: PM/ACPI
- `0x4000_6000-0x6FFF`: IOAPIC
- `0x4000_F000-0xFFFF`: Interconnect/ID/Version
- All others → Error Slave (DECERR/SLVERR)

**Benefits:**
- Single APB slave port (easy integration)
- Drop-in retro-compatible peripheral subsystem
- Clean power-of-2 decode (4KB = bits [15:12])
- 32KB reserved space for expansion

**📖 See:** `PRD.md` Section 4.2 for complete RLB wrapper specification and decoder implementation

### Q: "Why 'Retro Legacy Blocks'?"

**A:**
- **Retro**: Implements proven architectures from older platforms
- **Legacy**: Based on time-tested peripheral interface specifications
- **Blocks**: Collection of independent peripherals

Not experimental - production-ready implementations of time-tested designs.

---

## Anti-Patterns to Avoid

### ❌ Anti-Pattern 1: Not Using Reset Macros

```systemverilog
❌ WRONG: Manual reset handling
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) r_state <= IDLE;
    else r_state <= w_next_state;
end

✅ CORRECT: Use reset macros
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) r_state <= IDLE;
    else r_state <= w_next_state;
)
```

### ❌ Anti-Pattern 2: Missing FPGA Attributes

```systemverilog
❌ WRONG: No synthesis hints
logic [31:0] mem [1024];

✅ CORRECT: FPGA attributes
`ifdef XILINX
    (* ram_style = "auto" *)
`endif
logic [31:0] mem [1024];
```

### ❌ Anti-Pattern 3: TB Class in Test File

```python
❌ WRONG: Embedded in test file
# test_apb_gpio.py
class GPIOTB:  # NOT REUSABLE!
    ...

✅ CORRECT: Separate TB class file
# dv/tbclasses/gpio/gpio_tb.py
class GPIOTB(TBBase):  # REUSABLE!
    ...

# test_apb_gpio.py
from projects.components.retro_legacy_blocks.dv.tbclasses.gpio.gpio_tb import GPIOTB
```

### ❌ Anti-Pattern 4: Inconsistent Test Levels

```python
❌ WRONG: Only basic tests
# Missing medium and full test suites

✅ CORRECT: All 3 levels
# {block}_tests_basic.py - 4-6 tests
# {block}_tests_medium.py - 5-8 tests
# {block}_tests_full.py - 3-5 tests
```

---

## Quick Commands

```bash
# Run all HPET tests
pytest projects/components/retro_legacy_blocks/dv/tests/hpet/ -v

# Run specific block tests
pytest projects/components/retro_legacy_blocks/dv/tests/{block}/ -v

# Run basic tests only
pytest projects/components/retro_legacy_blocks/dv/tests/{block}/ -v -k "basic"

# With waveforms
WAVES=1 pytest projects/components/retro_legacy_blocks/dv/tests/{block}/ -v

# Lint block RTL
verilator --lint-only projects/components/retro_legacy_blocks/rtl/{block}/apb_{block}.sv

# Generate PeakRDL registers
cd projects/components/retro_legacy_blocks/rtl/{block}/peakrdl
peakrdl regblock {block}_regs.rdl --cpuif apb4 -o ../

# View documentation
cat projects/components/retro_legacy_blocks/PRD.md
cat projects/components/retro_legacy_blocks/docs/{block}_spec/{block}_index.md
```

---

## Remember

1. 🔧 **Reset Macros** - MANDATORY for all RTL (`ALWAYS_FF_RST`)
2. 🏭 **FPGA Attributes** - MANDATORY for all memory arrays
3. 🏗️ **TB Separation** - TB classes in `dv/tbclasses/{block}/`, NOT in test files
4. 📊 **3 Test Levels** - Basic/Medium/Full for every block
5. 📝 **PeakRDL** - Preferred for register generation
6. 🧹 **Test Cleanup** - Reset state at end of tests (especially counters)
7. ✅ **100% Pass Rate** - Target for basic and medium tests
8. 📖 **Documentation** - Update PRD.md, README.md for every new block
9. 🔍 **Lint Clean** - All RTL must pass Verilator --lint-only
10. 🎯 **RLB Goal** - Working toward integrated RLB wrapper

---

## PDF Generation Location

**IMPORTANT: PDF files should be generated in the docs directory:**
```
/mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/docs/
```

**Quick Command:** Use the provided shell script:
```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/retro_legacy_blocks/docs
./generate_pdf.sh
```

---

**Version:** 2.0
**Last Updated:** 2025-10-29
**Maintained By:** RTL Design Sherpa Project
