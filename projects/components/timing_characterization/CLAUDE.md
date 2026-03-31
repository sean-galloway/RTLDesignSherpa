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

# Claude Code Guide: Timing Characterization

**Version:** 2.0
**Last Updated:** 2026-03-18
**Purpose:** AI-specific guidance for working with timing characterization components

---

## Quick Context

**What:** Synthesis benchmarking harness with 9 FUBs measuring combinational delay across technologies
**Status:** Complete -- 9 FUBs, char_top wrapper, 45 tests passing, multi-flow SDC
**Your Role:** Help users run synthesis characterization, add new FUBs, and analyze results

**Key Documentation:**
- `README.md` -- Component overview and quick start
- `PRD.md` -- Complete product requirements and FUB specifications
- `TASKS.md` -- Task tracking and enhancement roadmap
- `rtl/syn/SYNTHESIS_GUIDE.md` -- Synthesis workflow and result interpretation

---

## Global Requirements Reference

**IMPORTANT: Check `/GLOBAL_REQUIREMENTS.md` for all mandatory requirements**

This file contains timing-characterization-specific guidance. For complete requirements:
- **See:** `/GLOBAL_REQUIREMENTS.md` -- Consolidated mandatory requirements
- **See:** `projects/components/CLAUDE.md` -- Component area standards
- **See:** Root `/CLAUDE.md` -- Repository-wide guidance

---

## Critical Rules for This Component Area

### Rule #0: Reset Macro Standards (MANDATORY)

**See:** `/GLOBAL_REQUIREMENTS.md` Section 1.1

**ALL RTL in timing_characterization/ MUST use reset macros for flip-flops:**

```systemverilog
`include "reset_defs.svh"

`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        r_data <= '0;
    end else begin
        r_data <= w_nand_chain_out;
    end
)
```

**No exceptions.** This is enforced for ALL components.

---

### Rule #1: Prevent Synthesis Optimization (CRITICAL)

**This is unique to timing characterization.** Synthesis tools will optimize away combinational chains if they detect constant propagation or redundant logic. You MUST prevent this:

**Required synthesis attributes on all chain signals:**
```systemverilog
`ifdef XILINX
    (* dont_touch = "true" *)
`elsif INTEL
    /* synthesis preserve */
`endif
```

**LFSR anti-optimization:** The shared 32-bit Galois LFSR (`x^32 + x^22 + x^2 + x + 1`) prevents constant propagation by driving all FUB inputs with pseudo-random data every cycle. All outputs are routed to top-level ports to prevent pruning.

**Dual-input decorrelation:** For two-operand FUBs (carry_chain, multiplier_tree), the second operand uses a 16-bit-shifted LFSR mapping (`r_lfsr[(b+16) % 32]`) to prevent common subexpression elimination.

---

### Rule #2: Testbench Location (MANDATORY)

**See:** `/GLOBAL_REQUIREMENTS.md` Section 2.1

**TB classes MUST be in `dv/tbclasses/`, NOT in test files:**

```
dv/
  tbclasses/
      timing_char_tb.py      # Shared TB base + LFSR reference model
  tests/
      fub/                   # 9 FUB-level tests
      top/                   # char_top integration test
```

**Import pattern:**
```python
from projects.components.timing_characterization.dv.tbclasses.timing_char_tb import (
    TimingCharTB, lfsr_step, lfsr_sequence, bit,
)
from TBClasses.shared.tbbase import TBBase
```

---

### Rule #3: Three Mandatory TB Methods

**See:** `/GLOBAL_REQUIREMENTS.md` Section 2.2

**ALL TB classes MUST implement:**

```python
class TimingCharTB(TBBase):
    async def setup_clocks_and_reset(self):
        """Standard initialization: start clock, assert reset, release."""
        await self.start_clock('clk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

    async def assert_reset(self):
        """Assert active-low reset."""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert active-low reset."""
        self.dut.rst_n.value = 1
```

---

### Rule #4: Pipeline Timing for char_top Tests

**The design has a 3-edge pipeline:**

```
Edge N:   r_lfsr updates (LFSR state N)
Edge N+1: FUB input flop captures combinational from r_lfsr (state N)
Edge N+2: FUB output flop captures result of combinational logic
```

When comparing outputs to expected values in char_top tests, the output
sampled after rising edge at cycle C reflects LFSR state from cycle C-2:

```python
lfsr_idx = settle_cycles + cyc - 2
```

The LFSR reference model in `timing_char_tb.py` provides `lfsr_step()`,
`lfsr_sequence()`, and `bit()` functions for computing expected values.

**Note:** The LFSR in char_top is a **left-shift Galois LFSR** (polynomial
`0x0040_0007`). This is architecturally different from the right-shift
tap-based Galois LFSR in `val/common/test_shifter_lfsr_galois.py` -- do not
reuse that model.

---

## Architecture Quick Reference

### Module Inventory

**FUBs (9):**

| FUB | File | Key Parameter | What It Measures |
|-----|------|--------------|-----------------|
| nand_chain | `rtl/fub/nand_chain.sv` | `NAND_LEVELS` | NAND-to-LUT mapping |
| inverter_chain | `rtl/fub/inverter_chain.sv` | `INVERTER_COUNT` | Baseline per-gate delay |
| xor_tree | `rtl/fub/xor_tree.sv` | `XOR_LEVELS` | XOR LUT packing |
| carry_chain | `rtl/fub/carry_chain.sv` | `CARRY_WIDTH` | Dedicated carry speed |
| multiplier_tree | `rtl/fub/multiplier_tree.sv` | `MULT_WIDTH`, `MULT_TYPE` | DSP vs. LUT timing |
| mux_tree | `rtl/fub/mux_tree.sv` | `MUX_LEVELS` | Mux-to-LUT mapping |
| queue_depth | `rtl/fub/queue_depth.sv` | `FIFO_DEPTH` | Memory inference thresholds |
| clock_divider_chain | `rtl/fub/clock_divider_chain.sv` | `CLK_DIV_STAGES` | Counter-based clock timing |
| gray_counter_chain | `rtl/fub/gray_counter_chain.sv` | `GRAY_WIDTH` | Binary-to-Gray conversion |

**Top-level:**
- `rtl/top/char_top.sv` -- Main synthesis target (9 FUBs + shared LFSR)
- `rtl/top/nand_chain_top.sv` -- Standalone NAND chain wrapper

**Synthesis:**
- `rtl/syn/char_top.sdc` -- Multi-flow SDC (ASIC/Vivado/Quartus)
- `rtl/syn/SYNTHESIS_GUIDE.md` -- Complete synthesis documentation

### Test Inventory

| Suite | Location | Tests | Description |
|-------|----------|-------|-------------|
| FUB tests | `dv/tests/fub/` | 34 | Per-FUB parameter sweeps |
| Integration | `dv/tests/top/` | 11 | char_top enable-mix configurations |
| **Total** | | **45** | **All passing** |

---

## Adding a New FUB

Follow this checklist when adding a new characterization block:

### Step 1: Create FUB RTL

```systemverilog
`timescale 1ns / 1ps
`include "reset_defs.svh"

module new_fub #(
    parameter int DEPTH = 8
) (
    input  logic clk,
    input  logic rst_n,
    input  logic [WIDTH-1:0] i_data,
    output logic [WIDTH-1:0] o_data
);
    // Input register
    logic [WIDTH-1:0] r_input;
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) r_input <= '0;
        else r_input <= i_data;
    )

    // Combinational logic with dont_touch
    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [WIDTH-1:0] w_result;
    // ... combinational logic here ...

    // Output register
    logic [WIDTH-1:0] r_output;
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) r_output <= '0;
        else r_output <= w_result;
    )
    assign o_data = r_output;
endmodule : new_fub
```

### Step 2: Add to char_top.sv

1. Add `EN_NEW_FUB` parameter (default 1)
2. Add FUB-specific parameters
3. Add output port(s)
4. Add conditional generate block with LFSR-driven inputs
5. Add tie-to-zero in the else branch

### Step 3: Update Filelist

Add the new .sv file to `rtl/filelists/char_top.f`.

### Step 4: Write FUB Test

Create `dv/tests/fub/test_new_fub.py` following Pattern B (CocoTB + pytest wrappers).

### Step 5: Update Integration Test

Add a new enable-mix configuration to `dv/tests/top/test_char_top.py` and
add expected-value computation for the new FUB.

### Step 6: Update Documentation

- Update `PRD.md` Section 4 (FUB Specifications)
- Update `SYNTHESIS_GUIDE.md` Section 3 (FUB Catalog)
- Update `TASKS.md` to track the work

---

## Anti-Patterns to Avoid

### Anti-Pattern 1: No Synthesis Preservation Attributes

```systemverilog
// WRONG: Synthesis will optimize the chain away
logic w_chain [NUM_GATES+1];

// CORRECT: Preserve the chain
(* dont_touch = "true" *)
logic w_chain [NUM_GATES+1];
```

### Anti-Pattern 2: Constant Inputs

```systemverilog
// WRONG: One input is always 1, tool may simplify
assign nand_out = ~(chain_in & 1'b1);

// CORRECT: Use LFSR-driven inputs through registered flops
assign nand_out = ~(chain_in & r_enable);
```

### Anti-Pattern 3: Missing Reset Macros on Flops

```systemverilog
// WRONG
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) r_data <= '0;
    else r_data <= w_chain_out;
end

// CORRECT
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        r_data <= '0;
    end else begin
        r_data <= w_chain_out;
    end
)
```

### Anti-Pattern 4: Wrong LFSR Model

```python
# WRONG: Using right-shift model from val/common/
from val.common.test_shifter_lfsr_galois import simulate_galois_lfsr

# CORRECT: Using left-shift model from timing_char_tb
from projects.components.timing_characterization.dv.tbclasses.timing_char_tb import (
    lfsr_step, lfsr_sequence,
)
```

---

## Quick Commands

```bash
# Run all FUB tests
PYTHONPATH=bin:$PYTHONPATH pytest dv/tests/fub/ -v

# Run char_top integration test
PYTHONPATH=bin:$PYTHONPATH pytest dv/tests/top/ -v

# Run everything
PYTHONPATH=bin:$PYTHONPATH pytest dv/tests/ -v

# Run with waveforms
WAVES=1 PYTHONPATH=bin:$PYTHONPATH pytest dv/tests/fub/test_carry_chain.py -v

# Lint single FUB
verilator --lint-only rtl/fub/carry_chain.sv
```

---

## Remember

1. **Prevent Optimization** -- Use dont_touch/preserve attributes on all chain signals
2. **Reset Macros** -- MANDATORY for ALL flip-flops
3. **Parameterize** -- Every FUB needs a depth/width sweep parameter
4. **TB Separation** -- TB classes in `dv/tbclasses/`, NOT in test files
5. **Pipeline Alignment** -- char_top outputs lag LFSR by 2 cycles (3-edge pipeline)
6. **Left-shift LFSR** -- Do NOT reuse the right-shift model from val/common/
7. **Multi-flow SDC** -- ASIC/Vivado/Quartus supported, set FLOW before sourcing
8. **Results Documentation** -- Record characterization data in `docs/`

---

**Version:** 2.0
**Last Updated:** 2026-03-18
**Maintained By:** RTL Design Sherpa Project
