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
## Timing Characterization -- Synthesis Benchmarking Harness

**Version:** 1.0
**Date:** 2026-03-18
**Status:** Complete -- RTL, verification, and synthesis infrastructure in place
**Owner:** RTL Design Sherpa Project
**Parent Document:** `/PRD.md`

---

## 1. Executive Summary

The **Timing Characterization** component is a synthesis benchmarking harness
that forces synthesis tools to build specific combinational structures between
registered endpoints. The resulting timing reports enable direct comparison of
gate delay across FPGA families, ASIC standard-cell libraries, synthesis tool
settings, and parameter sweeps.

### 1.1 Quick Stats

- **Modules:** 37 SystemVerilog files (9 FUBs + 2 top-level + 26 shared deps)
- **FUBs:** 9 independently-enableable characterization blocks
- **Tests:** 45 (34 FUB-level + 11 integration)
- **Synthesis flows:** ASIC (DC/Genus), Vivado, Quartus
- **Target frequency:** 500 MHz (configurable)

### 1.2 Project Goals

- **Primary:** Measure combinational delay per logic level across technologies
- **Secondary:** Provide a reusable synthesis benchmark harness for FPGA/ASIC evaluation
- **Tertiary:** Educational tool demonstrating synthesis optimization, anti-optimization techniques, and SDC constraint strategy

---

## 2. Key Design Principles

### 2.1 Anti-Optimization

Synthesis tools aggressively optimize logic. A benchmarking harness must
prevent this without distorting the results:

| Technique | Implementation | Purpose |
|-----------|---------------|---------|
| **LFSR-driven inputs** | 32-bit Galois LFSR feeds all FUB inputs | Prevents constant propagation |
| **Output port routing** | Every FUB output reaches a top-level port | Prevents output pruning |
| **Synthesis attributes** | `dont_touch` (Xilinx), `preserve` (Intel) | Prevents chain collapsing |
| **Decorrelated operands** | Second operand uses 16-bit-shifted LFSR taps | Prevents common subexpression elimination |

### 2.2 Registered Endpoints

Every FUB follows the pattern:

```
Input flop(s) --> Combinational logic --> Output flop(s)
```

This ensures that all critical paths are register-to-register, making timing
reports directly comparable across FUBs and technologies.

### 2.3 Parameterization

Every FUB has at least one depth/width parameter that controls the
combinational path length. This enables parameter sweeps to map delay
as a function of logic depth.

---

## 3. Architecture

### 3.1 Top-Level Block Diagram

```
char_top
├── 32-bit Galois LFSR (shared, x^32 + x^22 + x^2 + x + 1)
│   ├── Seed interface: i_seed_valid, i_seed_data[31:0]
│   └── Default seed: 0xDEAD_BEEF
│
├── FUB: nand_chain          (EN_NAND_TREE)
├── FUB: inverter_chain      (EN_INVERTER_CHAIN)
├── FUB: xor_tree            (EN_XOR_TREE)
├── FUB: carry_chain         (EN_CARRY_CHAIN)
├── FUB: multiplier_tree     (EN_MULTIPLIER)
├── FUB: mux_tree            (EN_MUX_TREE)
├── FUB: queue_depth         (EN_QUEUE_DEPTH)
├── FUB: clock_divider_chain (EN_CLK_DIVIDER)
└── FUB: gray_counter_chain  (EN_GRAY_COUNTER)
```

Each FUB is wrapped in a conditional generate block. When disabled (`EN_*=0`),
the block emits only a tie-to-zero assignment and consumes zero logic.

### 3.2 LFSR Data Distribution

The LFSR provides 32 pseudo-random bits each cycle. FUB inputs are wired as
combinational taps:

- **Single-input FUBs** (nand, inverter, xor, mux): `r_lfsr[b % 32]`
- **Dual-input FUBs** (carry, multiplier): Operand A uses `r_lfsr[b % 32]`,
  operand B uses `r_lfsr[(b+16) % 32]` for decorrelation
- **Control signals** (mux selects): Separate LFSR bit ranges

### 3.3 Pipeline Timing

The design has a 3-edge pipeline:

```
Edge N:   r_lfsr updates (LFSR state N)
Edge N+1: FUB input flop captures combinational from r_lfsr (state N)
Edge N+2: FUB output flop captures result of combinational logic
```

Output sampled after rising edge at cycle C reflects LFSR state from cycle C-2.

---

## 4. FUB Specifications

### 4.1 nand_chain -- NAND Gate Binary Tree

| Attribute | Specification |
|-----------|--------------|
| **File** | `rtl/fub/nand_chain.sv` |
| **Enable parameter** | `EN_NAND_TREE` |
| **Key parameters** | `NAND_LEVELS` (tree depth), `NUM_FLOPS` (input flop count) |
| **Input** | `NUM_FLOPS` registered flops from LFSR |
| **Output** | 1-bit registered output |
| **Critical path** | NAND_LEVELS gate delays (root to leaf) |
| **Structure** | Complete binary tree with heap-style indexing; leaf modulo wrapping when `2^LEVELS > NUM_FLOPS` |

### 4.2 inverter_chain -- Linear Inverter Chain

| Attribute | Specification |
|-----------|--------------|
| **File** | `rtl/fub/inverter_chain.sv` |
| **Enable parameter** | `EN_INVERTER_CHAIN` |
| **Key parameters** | `INVERTER_COUNT` (chain length) |
| **Input** | 1-bit registered input from LFSR |
| **Output** | 1-bit registered output |
| **Critical path** | INVERTER_COUNT inverter delays (linear) |
| **Structure** | Simple linear chain: `r_in -> ~() -> ~() -> ... -> r_out` |

### 4.3 xor_tree -- XOR Gate Binary Tree

| Attribute | Specification |
|-----------|--------------|
| **File** | `rtl/fub/xor_tree.sv` |
| **Enable parameter** | `EN_XOR_TREE` |
| **Key parameters** | `XOR_LEVELS` (tree depth), `NUM_FLOPS` (input flop count) |
| **Input** | `NUM_FLOPS` registered flops from LFSR |
| **Output** | 1-bit registered output |
| **Critical path** | XOR_LEVELS gate delays |
| **Structure** | Identical topology to nand_chain but with XOR gates |

### 4.4 carry_chain -- Ripple-Carry Adder

| Attribute | Specification |
|-----------|--------------|
| **File** | `rtl/fub/carry_chain.sv` |
| **Enable parameter** | `EN_CARRY_CHAIN` |
| **Key parameters** | `CARRY_WIDTH` (adder bit width) |
| **Input** | Two CARRY_WIDTH-bit registered operands from LFSR |
| **Output** | (CARRY_WIDTH+1)-bit registered sum |
| **Critical path** | WIDTH carry-propagation delays |
| **Structure** | `w_sum = {1'b0, r_input_a} + {1'b0, r_input_b}` inferred as ripple-carry |

### 4.5 multiplier_tree -- Multiplier Wrapper

| Attribute | Specification |
|-----------|--------------|
| **File** | `rtl/fub/multiplier_tree.sv` |
| **Enable parameter** | `EN_MULTIPLIER` |
| **Key parameters** | `MULT_WIDTH` (operand width), `MULT_TYPE` (0-4) |
| **Input** | Two MULT_WIDTH-bit registered operands from LFSR |
| **Output** | (2*MULT_WIDTH)-bit registered product |
| **Critical path** | Multiplier reduction tree depth |

**MULT_TYPE options:**

| Type | Implementation | Available widths |
|------|---------------|-----------------|
| 0 | Inferred (`*` operator) | Any |
| 1 | Dadda tree (structural) | 8, 16, 32 |
| 2 | Wallace tree (structural) | 8, 16, 32 |
| 3 | Wallace tree CSA (structural) | 8, 16, 32 |
| 4 | Dadda 4:2 compressor (structural) | 8, 11, 24 |

### 4.6 mux_tree -- Binary Mux Tree

| Attribute | Specification |
|-----------|--------------|
| **File** | `rtl/fub/mux_tree.sv` |
| **Enable parameter** | `EN_MUX_TREE` |
| **Key parameters** | `MUX_LEVELS` (tree depth), `NUM_FLOPS` (data input count) |
| **Input** | `NUM_FLOPS` data flops + select vector from LFSR |
| **Output** | 1-bit registered output |
| **Critical path** | MUX_LEVELS 2:1 mux delays |
| **Structure** | Binary tree of 2:1 multiplexers reducing to single output |

### 4.7 queue_depth -- FIFO Queue

| Attribute | Specification |
|-----------|--------------|
| **File** | `rtl/fub/queue_depth.sv` |
| **Enable parameter** | `EN_QUEUE_DEPTH` |
| **Key parameters** | `FIFO_DATA_WIDTH`, `FIFO_DEPTH` |
| **Input** | LFSR data written when FIFO has space |
| **Output** | Read data + valid + count (registered) |
| **Critical path** | FIFO read path + output register |
| **Structure** | Wraps `gaxi_fifo_sync` from rtl/common |

### 4.8 clock_divider_chain -- Clock Divider Cascade

| Attribute | Specification |
|-----------|--------------|
| **File** | `rtl/fub/clock_divider_chain.sv` |
| **Enable parameter** | `EN_CLK_DIVIDER` |
| **Key parameters** | `CLK_DIV_STAGES`, `CLK_DIV_CW`, `CLK_DIV_PICKOFF` |
| **Input** | Clock signal |
| **Output** | NUM_STAGES divided clock outputs (registered) |
| **Critical path** | Counter increment + pickoff mux per stage |
| **Structure** | Cascaded `clock_divider` instances from rtl/common |

### 4.9 gray_counter_chain -- Gray Counter

| Attribute | Specification |
|-----------|--------------|
| **File** | `rtl/fub/gray_counter_chain.sv` |
| **Enable parameter** | `EN_GRAY_COUNTER` |
| **Key parameters** | `GRAY_WIDTH` |
| **Input** | Enable from LFSR bit |
| **Output** | Binary count + Gray code (registered) |
| **Critical path** | Binary carry chain + XOR tree for Gray conversion |
| **Structure** | Wraps `counter_bingray` from rtl/common |

---

## 5. Interfaces

### 5.1 char_top Port List

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` | Input | 1 | System clock |
| `rst_n` | Input | 1 | Active-low asynchronous reset |
| `i_seed_valid` | Input | 1 | LFSR seed load strobe |
| `i_seed_data` | Input | 32 | LFSR seed value |
| `o_nand` | Output | 1 | NAND tree output |
| `o_inverter` | Output | 1 | Inverter chain output |
| `o_xor` | Output | 1 | XOR tree output |
| `o_carry` | Output | CARRY_WIDTH+1 | Carry chain sum |
| `o_mult` | Output | 2*MULT_WIDTH | Multiplier product |
| `o_mux` | Output | 1 | Mux tree output |
| `o_queue_data` | Output | FIFO_DATA_WIDTH | FIFO read data |
| `o_queue_valid` | Output | 1 | FIFO read valid |
| `o_queue_count` | Output | varies | FIFO occupancy count |
| `o_clk_div` | Output | CLK_DIV_STAGES | Divided clock outputs |
| `o_gray_bin` | Output | GRAY_WIDTH | Binary counter value |
| `o_gray_code` | Output | GRAY_WIDTH | Gray code value |

### 5.2 char_top Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `EN_NAND_TREE` | 1 | Enable NAND tree FUB |
| `EN_INVERTER_CHAIN` | 1 | Enable inverter chain FUB |
| `EN_XOR_TREE` | 1 | Enable XOR tree FUB |
| `EN_CARRY_CHAIN` | 1 | Enable carry chain FUB |
| `EN_MULTIPLIER` | 1 | Enable multiplier FUB |
| `EN_MUX_TREE` | 1 | Enable mux tree FUB |
| `EN_QUEUE_DEPTH` | 1 | Enable FIFO queue FUB |
| `EN_CLK_DIVIDER` | 1 | Enable clock divider FUB |
| `EN_GRAY_COUNTER` | 1 | Enable Gray counter FUB |
| `NAND_LEVELS` | 4 | NAND tree depth |
| `NAND_NUM_FLOPS` | 8 | NAND tree input flop count |
| `INVERTER_COUNT` | 16 | Inverter chain length |
| `XOR_LEVELS` | 4 | XOR tree depth |
| `XOR_NUM_FLOPS` | 8 | XOR tree input flop count |
| `CARRY_WIDTH` | 8 | Carry chain bit width |
| `MULT_WIDTH` | 8 | Multiplier operand width |
| `MULT_TYPE` | 0 | Multiplier implementation (0-4) |
| `MUX_LEVELS` | 4 | Mux tree depth |
| `MUX_NUM_FLOPS` | 8 | Mux tree data input count |
| `FIFO_DATA_WIDTH` | 8 | FIFO data width |
| `FIFO_DEPTH` | 16 | FIFO depth |
| `CLK_DIV_STAGES` | 3 | Number of clock divider stages |
| `CLK_DIV_CW` | 4 | Clock divider counter width |
| `CLK_DIV_PICKOFF` | 2 | Clock divider pickoff bit |
| `GRAY_WIDTH` | 8 | Gray counter width |

---

## 6. Verification

### 6.1 Test Architecture

Tests are organized in two tiers:

**Tier 1 -- FUB Tests** (`dv/tests/fub/`):
Each FUB has a dedicated test file that sweeps parameter points and verifies
functional correctness (outputs toggle, correct polarity/value after pipeline
latency). 34 test cases across 9 FUBs.

**Tier 2 -- Integration Test** (`dv/tests/top/`):
`test_char_top.py` tests 11 configurations of char_top:
- 10 enable-mix configurations (all-on, individual FUBs, groups)
- 1 LFSR seed verification test (loads custom seed, verifies sequence)

### 6.2 Testbench Infrastructure

- **Base class:** `TimingCharTB` in `dv/tbclasses/timing_char_tb.py`
- **LFSR reference model:** `lfsr_step()`, `lfsr_sequence()`, `bit()` functions
  in the same file, matching the left-shift Galois LFSR in char_top.sv
- **Pattern:** All tests use Pattern B (CocoTB + pytest wrappers)

### 6.3 Verification Scope

Simulation verifies **functional correctness** (data propagates, outputs
toggle). The real characterization happens in **synthesis timing reports**,
which is the primary purpose of this design.

---

## 7. Synthesis Strategy

### 7.1 SDC Constraints

`rtl/syn/char_top.sdc` provides multi-flow constraints:

| Parameter | Default | Rationale |
|-----------|---------|-----------|
| Target frequency | 500 MHz | Aggressive enough to expose path differences |
| Input delay | 80% of period | Forces interesting paths into FUB internals |
| Output delay | 20% of period | Trivially met for registered outputs |
| Clock uncertainty | 100 ps | Covers jitter + skew |
| Reset | False path | Asynchronous, not timing-critical |

### 7.2 Supported Flows

| Flow | Tool | Setup |
|------|------|-------|
| ASIC | Synopsys DC / Cadence Genus | Target library, operating conditions |
| FPGA (Xilinx) | Vivado | Part number |
| FPGA (Intel) | Quartus Prime | FAMILY, DEVICE |

### 7.3 Recommended Sweeps

| Sweep | FUB | Parameter | Values |
|-------|-----|-----------|--------|
| Carry width | carry_chain | `CARRY_WIDTH` | 8, 16, 32, 64, 128, 256 |
| NAND depth | nand_chain | `NAND_LEVELS` | 4, 6, 8, 10, 12 |
| DSP vs. LUT | multiplier_tree | `MULT_TYPE` | 0 (DSP), 1 (Dadda LUT) |
| Memory inference | queue_depth | `FIFO_DEPTH` | 4, 16, 64, 256, 1024, 4096 |
| Gray width | gray_counter_chain | `GRAY_WIDTH` | 4, 8, 16, 32, 64, 128 |

See `rtl/syn/SYNTHESIS_GUIDE.md` for complete workflow documentation.

---

## 8. Dependencies

### 8.1 Shared RTL from rtl/common/

The following modules are copied into `rtl/common/` within this component
to keep the synthesis filelist self-contained:

| Module | Used By |
|--------|---------|
| `counter_bin.sv` | clock_divider_chain, queue_depth |
| `counter_bingray.sv` | gray_counter_chain |
| `clock_divider.sv` | clock_divider_chain |
| `fifo_control.sv` | queue_depth |
| `gaxi_fifo_sync.sv` | queue_depth |
| `math_adder_*.sv` | multiplier_tree (structural variants) |
| `math_multiplier_*.sv` | multiplier_tree (Dadda, Wallace, CSA) |
| `math_compressor_4to2.sv` | multiplier_tree (4:2 variant) |
| `math_prefix_cell*.sv` | multiplier_tree (Han-Carlson adder) |

### 8.2 Verification Framework

- `CocoTBFramework.tbclasses.shared.tbbase.TBBase` -- base testbench class
- CocoTB + cocotb-test -- simulation runner
- pytest -- test collection and parameterization

---

## 9. Future Extensions

| Extension | Priority | Description |
|-----------|----------|-------------|
| Parameter sweep scripts | Medium | Automated synthesis sweeps with report parsing |
| Cross-technology comparison reports | Medium | Structured results in `docs/` |
| Additional FUBs (barrel shifter, priority encoder) | Low | Broader logic family coverage |
| Automated Fmax extraction | Low | Script to compute Fmax from timing reports |
| PDF generation for synthesis guide | Low | Markdown-to-PDF pipeline |

---

**Version:** 1.0
**Last Updated:** 2026-03-18
**Maintained By:** RTL Design Sherpa Project
