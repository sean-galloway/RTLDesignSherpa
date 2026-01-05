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

# Claude Code Guide: Miscellaneous Components

**Version:** 1.0
**Last Updated:** 2025-11-11
**Purpose:** AI-specific guidance for working with miscellaneous utility components

---

## Quick Context

**What:** Collection of reusable utility components and adapters
**Status:** ✅ Active - Currently planning AXI ROM wrapper
**Your Role:** Help users develop utility components following repository standards

**📖 Complete Documentation:** `projects/components/misc/README.md` ← Component overview

---

## 📖 Global Requirements Reference

**IMPORTANT: Check `/GLOBAL_REQUIREMENTS.md` for all mandatory requirements**

This file contains misc-specific guidance. For complete requirements:
- **See:** `/GLOBAL_REQUIREMENTS.md` - Consolidated mandatory requirements
- **See:** `projects/components/CLAUDE.md` - Component area standards
- **See:** Root `/CLAUDE.md` - Repository-wide guidance

---

## Critical Rules for This Component Area

### Rule #0: Reset Macro Standards (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 1.1

**ALL RTL in misc/ MUST use reset macros:**

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

**No exceptions.** This is enforced for ALL new components.

---

### Rule #1: FPGA Synthesis Attributes (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 1.2

**ALL memory arrays MUST have FPGA attributes:**

```systemverilog
`ifdef XILINX
    (* ram_style = "block" *)  // Block RAM for large ROMs
`elsif INTEL
    /* synthesis ramstyle = "M20K" */
`endif
logic [DATA_WIDTH-1:0] rom_data [DEPTH];
```

**Why critical for misc/:**
- ROM/RAM wrappers are primary use case
- Proper inference prevents logic explosion
- Cross-vendor compatibility essential

---

### Rule #2: Testbench Location (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.1

**TB classes MUST be in `dv/tbclasses/`, NOT in test files:**

```python
# CORRECT structure
dv/
├── tbclasses/
│   └── axi_rom_tb.py          # ✅ TB class here
└── tests/
    └── test_axi_rom.py         # ✅ Test runner imports from above
```

**Import pattern:**
```python
from projects.components.misc.dv.tbclasses.axi_rom_tb import AXIRomTB
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
```

---

### Rule #3: Three Mandatory TB Methods

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.2

**ALL TB classes MUST implement:**

```python
class AXIRomTB(TBBase):
    async def setup_clocks_and_reset(self):
        """Complete initialization"""
        await self.start_clock('aclk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()

    async def assert_reset(self):
        """Assert reset signal"""
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.dut.aresetn.value = 1
```

---

## Component Development Workflow

### Step 1: Validate Component Suitability

**Before adding to misc/, verify:**

✅ **Belongs in misc/ if:**
- Solves common integration problem
- Reusable across multiple projects
- Doesn't fit existing categories
- Uses standard interfaces
- Production quality (tested, documented)

❌ **Does NOT belong in misc/ if:**
- Project-specific glue logic
- Experimental or prototype code
- Duplicates existing functionality
- Lacks standard interface

**Examples:**

| Component | Belongs in misc/? | Reason |
|-----------|-------------------|--------|
| AXI ROM wrapper | ✅ Yes | Common, reusable, standard interface |
| AXI RAM wrapper | ✅ Yes | Common, reusable, standard interface |
| Project X custom mux | ❌ No | Project-specific, no standard interface |
| Debug probe | ❌ No | Better in separate debug infrastructure |

---

### Step 2: Create Directory Structure

```bash
cd projects/components/misc

# RTL directory
mkdir -p rtl/{component_name}/filelists

# Testbench directories
mkdir -p dv/tbclasses/{component_name}
mkdir -p dv/tests/{component_name}

# Documentation
mkdir -p docs
```

**Standard file layout:**
```
{component_name}/
├── rtl/{component_name}.sv              # Main implementation
├── rtl/{component_name}_pkg.sv          # Package (if needed)
├── rtl/filelists/{component_name}.f     # Synthesis filelist
├── dv/tbclasses/{component_name}_tb.py  # TB class
├── dv/tests/test_{component_name}.py    # Test runner
└── docs/{component_name}_spec.md        # Specification
```

---

### Step 3: Implement RTL Following Standards

**Template for AXI ROM wrapper:**

```systemverilog
`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_rom_wrapper #(
    parameter int DATA_WIDTH = 64,
    parameter int ADDR_WIDTH = 16,
    parameter int ID_WIDTH = 4,
    parameter string INIT_FILE = "none"
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // AXI4 AR channel
    input  logic [ADDR_WIDTH-1:0]   s_axi_araddr,
    input  logic [ID_WIDTH-1:0]     s_axi_arid,
    input  logic [7:0]              s_axi_arlen,
    input  logic [2:0]              s_axi_arsize,
    input  logic [1:0]              s_axi_arburst,
    input  logic                    s_axi_arvalid,
    output logic                    s_axi_arready,

    // AXI4 R channel
    output logic [DATA_WIDTH-1:0]   s_axi_rdata,
    output logic [ID_WIDTH-1:0]     s_axi_rid,
    output logic [1:0]              s_axi_rresp,
    output logic                    s_axi_rlast,
    output logic                    s_axi_rvalid,
    input  logic                    s_axi_rready
);

    // Local parameters
    localparam int DEPTH = 2**(ADDR_WIDTH - $clog2(DATA_WIDTH/8));
    localparam int BYTE_OFFSET = $clog2(DATA_WIDTH/8);

    // ROM storage with FPGA attributes
    `ifdef XILINX
        (* ram_style = "block" *)
    `elsif INTEL
        /* synthesis ramstyle = "M20K" */
    `endif
    logic [DATA_WIDTH-1:0] rom_data [DEPTH];

    // Initialize ROM from file
    initial begin
        if (INIT_FILE != "none") begin
            $readmemh(INIT_FILE, rom_data);
        end else begin
            // Default initialization (all zeros)
            for (int i = 0; i < DEPTH; i++) begin
                rom_data[i] = '0;
            end
        end
    end

    // State machine for burst handling
    typedef enum logic [1:0] {
        IDLE    = 2'b00,
        ACTIVE  = 2'b01
    } state_t;

    state_t r_state, w_next_state;

    // Registered transaction info
    logic [ADDR_WIDTH-1:0]  r_addr;
    logic [ID_WIDTH-1:0]    r_id;
    logic [7:0]             r_len;
    logic [7:0]             r_beat_count;

    // State register with reset macro
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_state <= IDLE;
        end else begin
            r_state <= w_next_state;
        end
    )

    // Next state logic
    always_comb begin
        w_next_state = r_state;
        case (r_state)
            IDLE:    if (s_axi_arvalid) w_next_state = ACTIVE;
            ACTIVE:  if (s_axi_rvalid && s_axi_rready && s_axi_rlast) w_next_state = IDLE;
            default: w_next_state = IDLE;
        endcase
    end

    // Transaction registers with reset macro
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_addr <= '0;
            r_id <= '0;
            r_len <= '0;
            r_beat_count <= '0;
        end else begin
            if (r_state == IDLE && s_axi_arvalid) begin
                r_addr <= s_axi_araddr;
                r_id <= s_axi_arid;
                r_len <= s_axi_arlen;
                r_beat_count <= '0;
            end else if (r_state == ACTIVE && s_axi_rvalid && s_axi_rready) begin
                r_addr <= r_addr + (DATA_WIDTH / 8);  // Byte increment
                r_beat_count <= r_beat_count + 1'b1;
            end
        end
    )

    // Output assignments
    assign s_axi_arready = (r_state == IDLE);
    assign s_axi_rvalid = (r_state == ACTIVE);
    assign s_axi_rdata = rom_data[r_addr[ADDR_WIDTH-1:BYTE_OFFSET]];
    assign s_axi_rid = r_id;
    assign s_axi_rresp = 2'b00;  // OKAY response
    assign s_axi_rlast = (r_beat_count == r_len);

endmodule : axi_rom_wrapper
```

**Key points:**
1. ✅ Uses reset macros (`ALWAYS_FF_RST`)
2. ✅ FPGA synthesis attributes on ROM
3. ✅ Parameterized (DATA_WIDTH, ADDR_WIDTH, etc.)
4. ✅ Modern array syntax `[DEPTH]`
5. ✅ File initialization support

---

### Step 4: Create Testbench Class

**Template for AXI ROM TB:**

```python
# dv/tbclasses/axi_rom_tb.py
import os
import sys
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
from cocotb.clock import Clock

# Add repo to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_master import AXI4Master

class AXIRomTB(TBBase):
    """Testbench for AXI ROM wrapper"""

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.aclk = dut.aclk
        self.aresetn = dut.aresetn

        # Create AXI4 master driver
        self.axi_master = AXI4Master(
            dut=dut,
            prefix="s_axi",
            clock=dut.aclk,
            reset=dut.aresetn,
            reset_active_level=False
        )

    async def setup_clocks_and_reset(self):
        """Complete initialization - MANDATORY METHOD"""
        await self.start_clock('aclk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)

    async def assert_reset(self):
        """Assert reset - MANDATORY METHOD"""
        self.aresetn.value = 0

    async def deassert_reset(self):
        """Deassert reset - MANDATORY METHOD"""
        self.aresetn.value = 1

    async def read_single(self, addr, size=3):
        """Read single beat from ROM"""
        return await self.axi_master.read_burst(
            addr=addr,
            length=1,
            size=size,
            burst_type=1  # INCR
        )

    async def read_burst(self, addr, length, size=3):
        """Read burst from ROM"""
        return await self.axi_master.read_burst(
            addr=addr,
            length=length,
            size=size,
            burst_type=1  # INCR
        )

    def verify_data(self, expected, actual):
        """Verify read data matches expected"""
        if expected != actual:
            self.log.error(f"Data mismatch: expected=0x{expected:x}, actual=0x{actual:x}")
            return False
        return True
```

---

### Step 5: Create Test Runner

```python
# dv/tests/test_axi_rom.py
import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

from projects.components.misc.dv.tbclasses.axi_rom_tb import AXIRomTB

@cocotb.test()
async def cocotb_test_basic_read(dut):
    """Test basic single read"""
    tb = AXIRomTB(dut)
    await tb.setup_clocks_and_reset()

    # Read from address 0
    data = await tb.read_single(addr=0x0000, size=3)
    tb.log.info(f"Read data: 0x{data[0]:016x}")

    assert data is not None, "Read failed"

@cocotb.test()
async def cocotb_test_burst_read(dut):
    """Test burst read"""
    tb = AXIRomTB(dut)
    await tb.setup_clocks_and_reset()

    # Read burst of 8 beats
    data = await tb.read_burst(addr=0x0000, length=8, size=3)
    tb.log.info(f"Read {len(data)} beats")

    assert len(data) == 8, f"Expected 8 beats, got {len(data)}"

# Pytest wrapper
@pytest.mark.parametrize("data_width,addr_width", [
    (64, 16),
    (32, 14),
    (128, 18),
])
def test_axi_rom(request, data_width, addr_width):
    """Test AXI ROM wrapper"""

    # Get paths
    tests_dir = os.path.dirname(os.path.abspath(__file__))
    rtl_dir = os.path.join(tests_dir, '../../rtl')

    # RTL sources
    verilog_sources = [
        os.path.join(rtl_dir, 'axi_rom_wrapper.sv'),
    ]

    # Includes
    includes = [
        os.path.join(repo_root, 'rtl/amba/includes'),
    ]

    # Parameters
    parameters = {
        'DATA_WIDTH': data_width,
        'ADDR_WIDTH': addr_width,
        'ID_WIDTH': 4,
        'INIT_FILE': "none"
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="axi_rom_wrapper",
        module="test_axi_rom",
        parameters=parameters,
        simulator="verilator",
        timescale="1ns/1ps",
    )
```

---

### Step 6: Create Documentation

**Create `docs/axi_rom_spec.md` with:**
1. Purpose and overview
2. Interface description (all ports)
3. Parameter definitions
4. Timing diagrams
5. Usage examples
6. Resource utilization
7. Known limitations

---

## Anti-Patterns to Avoid

### ❌ Anti-Pattern 1: No Reset Macros

```systemverilog
❌ WRONG:
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) r_data <= '0;
    else r_data <= rom_data[addr];
end

✅ CORRECT:
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) r_data <= '0;
    else r_data <= rom_data[addr];
)
```

### ❌ Anti-Pattern 2: Missing FPGA Attributes

```systemverilog
❌ WRONG:
logic [63:0] rom_data [4096];  // Will become logic!

✅ CORRECT:
`ifdef XILINX
    (* ram_style = "block" *)
`endif
logic [63:0] rom_data [4096];  // Block RAM
```

### ❌ Anti-Pattern 3: TB Class in Test File

```python
❌ WRONG:
# test_axi_rom.py
class AXIRomTB:  # DON'T DO THIS
    pass

✅ CORRECT:
# dv/tbclasses/axi_rom_tb.py
class AXIRomTB(TBBase):  # Separate file
    pass
```

### ❌ Anti-Pattern 4: Project-Specific Logic

```systemverilog
❌ WRONG:
// Hard-coded for Project X only
module project_x_rom_wrapper #(
    parameter PROJECT_X_ADDR = 32'h1000_0000  // NOT REUSABLE
) (...);

✅ CORRECT:
// Generic, parameterized
module axi_rom_wrapper #(
    parameter int DATA_WIDTH = 64,  // REUSABLE
    parameter int ADDR_WIDTH = 16
) (...);
```

---

## Quick Commands

```bash
# Create new component structure
cd projects/components/misc
mkdir -p rtl/{name}/{filelists,peakrdl}
mkdir -p dv/{tbclasses,tests}/{name}
mkdir -p docs

# Lint RTL
verilator --lint-only rtl/{name}.sv

# Run tests
pytest dv/tests/test_{name}.py -v

# Run with waveforms
WAVES=1 pytest dv/tests/test_{name}.py -v

# View waveforms
gtkwave dv/tests/logs/test_{name}.vcd
```

---

## Remember

1. 🔧 **Reset Macros** - MANDATORY for ALL RTL
2. 🏭 **FPGA Attributes** - MANDATORY for ALL memories
3. 🏗️ **TB Separation** - TB classes in `dv/tbclasses/`, NOT test files
4. ✅ **Standard Interfaces** - Use AXI4, APB, etc.
5. 📦 **Reusable** - Parameterized, configurable
6. 📝 **Documented** - Specification + inline comments
7. 🧪 **Tested** - 100% pass rate target
8. 🎯 **Focused** - Single-purpose utility components

---

**Version:** 1.0
**Last Updated:** 2025-11-11
**Maintained By:** RTL Design Sherpa Project
