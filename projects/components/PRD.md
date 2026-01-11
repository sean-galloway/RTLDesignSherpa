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

# Projects/Components Design Standards and Requirements

**Version:** 1.0
**Last Updated:** 2025-10-24
**Status:** Active

---

## 1. Document Purpose and Scope

### 1.1 Purpose

This Product Requirements Document (PRD) defines the design standards, coding conventions, and verification requirements for all RTL components developed in the `projects/components/` area of the RTL Design Sherpa repository.

### 1.2 Scope

This document applies to:
- All new RTL modules developed in `projects/components/`
- All modifications to existing RTL in `projects/components/`
- All testbenches and verification infrastructure for these components
- All documentation for these components

### 1.3 Component Categories

The `projects/components/` area contains high-performance accelerator blocks and system components:

| Component | Purpose | Status |
|-----------|---------|--------|
| **STREAM** | Streaming datapath engine with AXI and SRAM control | Active Development |
| **RAPIDS** | Rapid AXI Programmable In-band Descriptor System | Active Development |
| **Bridge** | Protocol bridges and converters | Active Development |
| **APB HPET** | APB High Precision Event Timer | Production |

Each component has its own subdirectory with RTL, verification, and documentation:
```
projects/components/{component}/
├── rtl/                # RTL source files
├── dv/                 # Design verification
│   ├── tbclasses/      # Component-specific testbench classes
│   ├── components/     # Component-specific BFM extensions (if needed)
│   └── tests/          # Test runners and pytest configurations
├── docs/               # Component-specific documentation
├── CLAUDE.md           # AI assistant guidance
└── PRD.md              # Component requirements document
```

---

## 2. Design Standards

### 2.1 Reset Handling

**REQUIREMENT: All sequential logic MUST use standardized reset macros**

#### 2.1.1 Reset Macro Usage

All new RTL files MUST include the reset definitions header:
```systemverilog
`include "reset_defs.svh"
```

All sequential logic MUST use the `ALWAYS_FF_RST` macro instead of manual `always_ff` blocks:

**REQUIRED Pattern:**
```systemverilog
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        // Reset logic
        r_state <= IDLE;
        r_counter <= '0;
    end else begin
        // Normal operation logic
        r_state <= w_next_state;
        r_counter <= r_counter + 1'b1;
    end
)
```

**PROHIBITED Pattern:**
```systemverilog
// DO NOT USE - Manual reset handling
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_state <= IDLE;
    end else begin
        r_state <= w_next_state;
    end
end
```

#### 2.1.2 Reset Signal Naming

Standard reset signal names:
- `rst_n` - Active-low asynchronous reset (default for projects/components)
- `aresetn` - Active-low asynchronous reset (AMBA protocol standard)

Reset signals MUST use the actual signal name in macros, NOT a `sync_` prefix.

#### 2.1.3 Reset Macro Definitions

The reset macros provide:
- `ALWAYS_FF_RST(clk, rst, ...)` - Sequential logic with asynchronous reset
- `RST_ASSERTED(rst)` - Test if reset is asserted (polarity-aware)
- `RST_RELEASED(rst)` - Test if reset is released (polarity-aware)

#### 2.1.4 Rationale

Standardized reset macros provide:
1. **Consistency** - Same reset pattern across all modules
2. **FPGA-friendly** - Async reset with sync release for better timing
3. **Maintainability** - Single point to modify reset behavior
4. **Tool compatibility** - Works with all synthesis and simulation tools

#### 2.1.5 Conversion Tool

Existing RTL can be converted using `bin/update_resets.py`:
```bash
# Dry-run to preview changes
python3 bin/update_resets.py projects/components/{component}/rtl/ --dry-run

# Perform conversion (outputs to UPDATED/ directory)
python3 bin/update_resets.py projects/components/{component}/rtl/

# Review and copy back
cp UPDATED/*.sv projects/components/{component}/rtl/
```

**Reference:** `rtl/amba/includes/reset_defs.svh` for complete macro definitions

---

### 2.2 FPGA Synthesis Attributes

**REQUIREMENT: All memory arrays MUST include FPGA synthesis attributes**

#### 2.2.1 Memory Array Attributes

All memory arrays (depth > 1) MUST include vendor-specific synthesis attributes:

```systemverilog
// REQUIRED for all memories
`ifdef XILINX
    (* ram_style = "auto" *)  // Let Xilinx tools decide
`elsif INTEL
    /* synthesis ramstyle = "AUTO" */  // Let Intel tools decide
`endif
logic [DATA_WIDTH-1:0] mem [DEPTH];
```

#### 2.2.2 Available Xilinx Attributes

| Attribute | Usage | When to Use |
|-----------|-------|-------------|
| `ram_style = "auto"` | Let tools decide | Default - recommended for most cases |
| `ram_style = "block"` | Force block RAM | Large memories (>256 words) |
| `ram_style = "distributed"` | Force LUT RAM | Small memories (<32 words), need low latency |
| `ram_style = "ultra"` | Force UltraRAM | Very large memories (Ultrascale+ only) |

#### 2.2.3 Available Intel Attributes

| Attribute | Usage | When to Use |
|-----------|-------|-------------|
| `ramstyle = "AUTO"` | Let tools decide | Default - recommended for most cases |
| `ramstyle = "M20K"` | Force M20K block RAM | Large memories |
| `ramstyle = "MLAB"` | Force MLAB distributed | Small memories, low latency |
| `ramstyle = "logic"` | Force logic (registers) | Tiny memories, fastest access |

#### 2.2.4 Other FPGA Attributes

DSP inference control:
```systemverilog
`ifdef XILINX
    (* use_dsp = "yes" *)  // Force DSP48 usage
`endif
logic [31:0] product = a * b;
```

Shift register inference control:
```systemverilog
`ifdef XILINX
    (* shreg_extract = "no" *)  // Prevent SRL inference
`endif
logic [7:0] pipe_stage;
```

#### 2.2.5 Rationale

FPGA synthesis attributes:
1. **Performance** - Better memory architecture selection
2. **Area efficiency** - Prevents logic explosion for large memories
3. **Cross-vendor** - Works on both Xilinx and Intel FPGAs
4. **Predictability** - Explicit control over synthesis decisions

#### 2.2.6 Examples

See reference implementations:
- `rtl/common/fifo_sync.sv` - FIFO with auto memory inference
- `projects/components/stream/rtl/stream_fub/simple_sram.sv` - SRAM with attributes

---

### 2.3 Array Declaration Syntax

**REQUIREMENT: Use unpacked array syntax `[DEPTH]` instead of `[0:DEPTH-1]`**

#### 2.3.1 Standard Syntax

**REQUIRED:**
```systemverilog
logic [DATA_WIDTH-1:0] mem [DEPTH];
```

**PROHIBITED:**
```systemverilog
logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];  // Old style - DO NOT USE
```

#### 2.3.2 Memory Initialization

Standard initialization patterns:
```systemverilog
// Initialize all elements to zero
logic [DATA_WIDTH-1:0] mem [DEPTH] = '{default:0};

// Initialize with specific values
logic [7:0] lut [16] = '{
    8'h00, 8'h01, 8'h02, 8'h03,
    8'h04, 8'h05, 8'h06, 8'h07,
    8'h08, 8'h09, 8'h0A, 8'h0B,
    8'h0C, 8'h0D, 8'h0E, 8'h0F
};
```

#### 2.3.3 Rationale

Modern array syntax provides:
1. **Tool compatibility** - Works with all modern simulators
2. **Readability** - Cleaner, more intuitive syntax
3. **Safety** - Reduces off-by-one indexing errors

---

### 2.4 SRAM and Memory Module Standards

**REQUIREMENT: SRAM modules MUST NOT include reset ports**

#### 2.4.1 SRAM Module Interface

SRAM modules represent physical memory and MUST NOT have reset ports:

```systemverilog
module simple_sram #(
    parameter int DATA_WIDTH = 32,
    parameter int DEPTH = 1024
) (
    input  logic                        clk,
    // NO rst_n port!

    // Write port
    input  logic                        wr_en,
    input  logic [$clog2(DEPTH)-1:0]    wr_addr,
    input  logic [DATA_WIDTH-1:0]       wr_data,

    // Read port
    input  logic                        rd_en,
    input  logic [$clog2(DEPTH)-1:0]    rd_addr,
    output logic [DATA_WIDTH-1:0]       rd_data
);
```

#### 2.4.2 SRAM Memory Array

SRAM memory arrays MUST include:
1. FPGA synthesis attributes
2. Modern array syntax
3. Optional initialization (default:0)

```systemverilog
// Memory array with FPGA hints
`ifdef XILINX
    (* ram_style = "auto" *)
`elsif INTEL
    /* synthesis ramstyle = "AUTO" */
`endif
logic [DATA_WIDTH-1:0] mem [DEPTH] = '{default:0};
```

#### 2.4.3 SRAM Controller Pattern

SRAM controllers HAVE reset, but SRAM itself does NOT:

```systemverilog
module sram_controller (
    input logic clk,
    input logic rst_n,  // Controller has reset
    // ... ports
);

    // Controller registers with reset
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_wr_ptr <= '0;
            r_rd_ptr <= '0;
        end else begin
            // Control logic
        end
    )

    // SRAM instance - NO reset port
    simple_sram u_sram (
        .clk(clk),
        // No .rst_n connection!
        .wr_en(wr_en),
        .wr_addr(r_wr_ptr),
        // ...
    );

endmodule
```

#### 2.4.4 Rationale

SRAM modules without reset:
1. **Realism** - Real SRAM chips don't have reset pins
2. **FPGA accuracy** - Block RAM doesn't reset contents
3. **Area/power** - Avoid wasted silicon for unnecessary reset logic
4. **Initialization** - Software writes during system startup

#### 2.4.5 Examples

Reference implementations:
- `projects/components/stream/rtl/stream_fub/simple_sram.sv` - SRAM module
- `projects/components/stream/rtl/stream_fub/sram_controller.sv` - Controller with reset

---

### 2.5 Coding Style

#### 2.5.1 Module Structure

Standard module organization:
```systemverilog
`timescale 1ns / 1ps

// Include files
`include "reset_defs.svh"
`include "{component}_imports.svh"  // If needed

module module_name #(
    // Parameters (UPPER_CASE)
    parameter int DATA_WIDTH = 32,
    parameter int ADDR_WIDTH = 16
) (
    // Clock and reset
    input  logic                    clk,
    input  logic                    rst_n,

    // Other ports grouped by function
    // ...
);

    // Local parameters
    localparam int LOCAL_PARAM = DATA_WIDTH / 8;

    // Internal signals
    logic r_register;  // Registers: r_ prefix
    logic w_wire;      // Wires: w_ prefix

    // Logic blocks
    // ...

endmodule : module_name  // Always use explicit end label
```

#### 2.5.2 Naming Conventions

| Element | Convention | Example |
|---------|-----------|----------|
| Modules | `snake_case` | `axi_read_engine` |
| Parameters | `UPPER_CASE` | `DATA_WIDTH`, `MAX_BURST` |
| Ports (input) | `snake_case` | `s_valid`, `m_ready` |
| Ports (output) | `snake_case` | `m_valid`, `s_ready` |
| Registers | `r_` prefix + `snake_case` | `r_state`, `r_counter` |
| Wires | `w_` prefix + `snake_case` | `w_sum`, `w_match` |
| Active-low signals | `_n` suffix | `rst_n`, `enable_n` |

#### 2.5.3 State Machines

Standard state machine pattern:
```systemverilog
// State type definition
typedef enum logic [2:0] {
    IDLE    = 3'b000,
    ACTIVE  = 3'b001,
    WAIT    = 3'b010,
    DONE    = 3'b011
} state_t;

state_t r_state, w_next_state;

// State register
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        r_state <= IDLE;
    end else begin
        r_state <= w_next_state;
    end
)

// Next state logic (combinational)
always_comb begin
    w_next_state = r_state;  // Default: hold state
    case (r_state)
        IDLE:   if (start)  w_next_state = ACTIVE;
        ACTIVE: if (done)   w_next_state = DONE;
        WAIT:   if (ready)  w_next_state = ACTIVE;
        DONE:               w_next_state = IDLE;
        default:            w_next_state = IDLE;
    endcase
end

// Output logic (combinational or registered)
assign output_signal = (r_state == ACTIVE);
```

#### 2.5.4 Streaming Interfaces

Standard streaming interface pattern (valid/ready handshaking):
```systemverilog
// Upstream interface (slave)
input  logic                    s_valid,
output logic                    s_ready,
input  logic [DATA_WIDTH-1:0]   s_data,

// Downstream interface (master)
output logic                    m_valid,
input  logic                    m_ready,
output logic [DATA_WIDTH-1:0]   m_data,
```

Ready signal calculation (pipeline can accept data):
```systemverilog
// Pipeline is ready when:
// 1. Output stage is empty (!m_valid), OR
// 2. Output is being consumed (m_ready)
assign s_ready = !m_valid || m_ready;
```

#### 2.5.5 Documentation

All modules MUST include:
1. **File header** - Copyright, license, brief description
2. **Parameter documentation** - Valid ranges, defaults, constraints
3. **Port documentation** - Function, timing, protocol
4. **Complex logic comments** - Why, not just what

Example file header:
```systemverilog
// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: module_name
// Purpose: Brief description of functionality
//
// Description:
//   Detailed description of what this module does,
//   key features, and design decisions.
//
// Parameters:
//   - DATA_WIDTH: Data bus width in bits (8, 16, 32, 64, 128, 256, 512)
//   - DEPTH: Memory depth, must be power of 2 (16 to 16384)
//
// Notes:
//   - Special constraints or usage requirements
//   - Related modules or dependencies
//
// Author: author_name
// Created: YYYY-MM-DD
```

---

## 3. Verification Requirements

### 3.1 Testbench Architecture

**REQUIREMENT: Project-specific testbench classes MUST reside in project dv/ area**

#### 3.1.1 Directory Structure

```
projects/components/{component}/
├── dv/
│   ├── tbclasses/          # Component-specific TB classes
│   │   ├── {module}_tb.py
│   │   └── {feature}_tb.py
│   ├── components/         # Component-specific BFM extensions (if needed)
│   └── tests/              # Test runners
│       ├── conftest.py     # Pytest configuration (MANDATORY)
│       └── test_*.py       # Test runner files
```

#### 3.1.2 Testbench Class Requirements

All testbench classes MUST implement three mandatory methods:

```python
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class ModuleTB(TBBase):
    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        # Initialize testbench

    async def setup_clocks_and_reset(self):
        """MANDATORY: Complete initialization - clocks and reset"""
        await self.start_clock('clk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

    async def assert_reset(self):
        """MANDATORY: Assert reset signal(s)"""
        self.dut.rst_n.value = 0  # Active-low

    async def deassert_reset(self):
        """MANDATORY: Deassert reset signal(s)"""
        self.dut.rst_n.value = 1  # Release active-low
```

#### 3.1.3 Test Runner Pattern

Test runners MUST:
1. Import TB classes from project dv/tbclasses/ area
2. Import shared framework utilities from CocoTBFramework
3. Use pytest parametrization for multiple configurations
4. Include conftest.py for pytest configuration

```python
# Import framework utilities (PYTHONPATH includes bin/)
import os, sys
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import from project area
from projects.components.stream.dv.tbclasses.scheduler_tb import SchedulerTB

# Import shared framework components
from CocoTBFramework.components.axi4.axi4_master import AXI4Master

@cocotb.test()
async def test_operation(dut):
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_test()
```

#### 3.1.4 Rationale

Project-specific testbenches in project area:
1. **Easy discovery** - All project code in one place
2. **Clear ownership** - Each project owns their dv/ area
3. **No confusion** - Never wonder where TB classes live
4. **Framework stays clean** - Only truly shared code in framework

---

### 3.2 Test Naming Conventions

**REQUIREMENT: Test functions MUST match module names to prevent conflicts**

#### 3.2.1 Pytest Function Naming

Pattern: `test_{module_name}` where `{module_name}` EXACTLY matches the RTL module

Examples:
```python
# CORRECT - Matches module name
def test_axi_read_engine(request, params):
    """Test for axi_read_engine.sv"""

def test_descriptor_engine(request, params):
    """Test for descriptor_engine.sv"""

# WRONG - Generic names cause conflicts
def test_engine(request, params):  # Too generic!
def test_read(request, params):    # Conflicts with write test!
```

#### 3.2.2 CocoTB Function Naming

Pattern: `cocotb_test_{scenario}` for CocoTB test functions

Examples:
```python
@cocotb.test()
async def cocotb_test_basic(dut):
    """Basic functionality test"""

@cocotb.test()
async def cocotb_test_backpressure(dut):
    """Backpressure handling test"""
```

---

### 3.3 Test Coverage Requirements

All RTL modules MUST have:
1. **Basic tests** - Register access, simple operations
2. **Functional tests** - All features and modes
3. **Error tests** - Error conditions and recovery
4. **Stress tests** - Performance limits, backpressure

Target coverage metrics:
- **Functional coverage** - >95% of features
- **Code coverage** - >90% of lines (where applicable)
- **Corner cases** - All boundary conditions

---

### 3.4 Waveform Generation

All tests SHOULD support waveform generation:
```python
@pytest.mark.parametrize("params", generate_test_params())
def test_module(request, params):
    # Generate waves if requested
    extra_args = []
    if hasattr(request.config, 'getoption') and request.config.getoption('--vcd'):
        extra_args.append('--vcd=test_module.vcd')

    run(
        verilog_sources=sources,
        module=module,
        extra_args=extra_args
    )
```

---

## 4. Documentation Requirements

### 4.1 Component Documentation Structure

Each component MUST have:
```
projects/components/{component}/
├── CLAUDE.md           # AI assistant guidance
├── PRD.md              # Component requirements
├── TASKS.md            # Work tracking
├── known_issues/       # Bug tracking
└── docs/               # Additional documentation
    ├── architecture.md
    ├── integration.md
    └── test_results.md
```

### 4.2 CLAUDE.md Requirements

CLAUDE.md files MUST include:
1. **Quick Context** - What, status, role
2. **Critical Rules** - Component-specific guidance
3. **Architecture** - Block diagram, key modules
4. **Common Patterns** - How to use the component
5. **Anti-Patterns** - What not to do
6. **Quick Commands** - Common operations

### 4.3 PRD.md Requirements

PRD.md files MUST include:
1. **Purpose and scope**
2. **Functional requirements**
3. **Interface specifications**
4. **Performance requirements**
5. **Verification strategy**
6. **Integration guidelines**

### 4.4 Inline Documentation

All RTL files MUST include:
1. **File header** - Copyright, license, description
2. **Parameter documentation** - Valid ranges, constraints
3. **Port documentation** - Function, timing, protocol
4. **Complex logic comments** - Design rationale

---

## 5. Tools and Automation

### 5.1 Reset Macro Conversion

**Tool:** `bin/update_resets.py`

Automatically converts manual reset patterns to standardized macros:
```bash
# Dry-run
python3 bin/update_resets.py projects/components/{component}/rtl/ --dry-run

# Convert
python3 bin/update_resets.py projects/components/{component}/rtl/

# Review and apply
diff -u projects/components/{component}/rtl/*.sv UPDATED/*.sv
cp UPDATED/*.sv projects/components/{component}/rtl/
```

### 5.2 Linting

All RTL MUST pass Verilator linting:
```bash
verilator --lint-only projects/components/{component}/rtl/*.sv
```

### 5.3 Testing

All components MUST pass pytest:
```bash
pytest projects/components/{component}/dv/tests/ -v
```

---

## 6. Integration Requirements

### 6.1 Reusability

All components MUST be:
1. **Parameterized** - Configurable for different use cases
2. **Self-contained** - Minimal external dependencies
3. **Well-documented** - Clear integration guidelines
4. **Verified** - Comprehensive test coverage

### 6.2 Interface Standards

Follow standard interface protocols:
- **AXI4** - For memory-mapped transactions
- **AXI4-Stream** - For streaming data
- **APB** - For control/status registers
- **Valid/Ready** - For internal streaming pipelines

### 6.3 Clock Domain Crossing

When crossing clock domains:
1. **Use proven CDC primitives** - From rtl/common/ or rtl/amba/
2. **Document CDC points** - In comments and documentation
3. **Verify CDC** - With appropriate constraints

---

## 7. Version Control

### 7.1 Commit Messages

Standard commit message format:
```
Brief description (50 chars or less)

More detailed explanation if needed. Wrap at 72 characters.
- Bullet points for multiple changes
- Link to issues or PRs

Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>
```

### 7.2 Branch Strategy

- **main** - Stable, tested code
- **feature/{name}** - New features
- **fix/{name}** - Bug fixes
- **refactor/{name}** - Code improvements

---

## 8. References

### 8.1 Related Documents

- Root `/CLAUDE.md` - Repository-wide guidance
- Root `/PRD.md` - Master requirements
- `rtl/amba/includes/reset_defs.svh` - Reset macro definitions
- `bin/update_resets.py` - Reset conversion tool

### 8.2 Component-Specific Documents

Each component has detailed documentation:
- `projects/components/stream/CLAUDE.md` and `PRD.md`
- `projects/components/rapids/CLAUDE.md` and `PRD.md`
- `projects/components/apb_hpet/CLAUDE.md` and `PRD.md`
- `projects/components/bridge/CLAUDE.md` and `PRD.md`

---

## 9. Compliance

### 9.1 Mandatory Requirements

All new RTL MUST:
- Include `reset_defs.svh` and use reset macros
- Include FPGA synthesis attributes on memory arrays
- Use modern array syntax `[DEPTH]`
- SRAM modules have NO reset ports
- Pass Verilator linting
- Have comprehensive testbenches
- Include complete documentation

### 9.2 Review Checklist

Before committing new RTL, verify:
- [ ] Reset macros used throughout
- [ ] FPGA attributes on all memories
- [ ] Modern array syntax
- [ ] SRAM modules have no reset
- [ ] Passes Verilator lint
- [ ] Tests written and passing
- [ ] Documentation complete
- [ ] Code review performed

---

**Version:** 1.0
**Last Updated:** 2025-10-24
**Maintained By:** RTL Design Sherpa Project
