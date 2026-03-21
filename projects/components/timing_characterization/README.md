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

# Timing Characterization

**Version:** 2.0
**Last Updated:** 2026-03-18
**Status:** Complete -- RTL, verification, and synthesis infrastructure in place

---

## Overview

The `timing_characterization/` component is a **synthesis benchmarking harness**
designed to measure combinational logic delay across FPGA families and ASIC
standard-cell libraries. It wraps nine distinct Functional Unit Blocks (FUBs)
in a single top-level module (`char_top`) so that synthesis timing reports can
be compared directly.

**Design Philosophy:**
- **Empirical Measurement** -- Determine real-world combinational depth limits
- **Technology Comparison** -- Same RTL, same SDC, different targets
- **Frequency Sweeps** -- Parameterized clock period to find max gate count
- **Anti-Optimization** -- LFSR-driven inputs + dont_touch attributes prevent synthesis shortcuts

---

## Quick Start

```bash
# Run all 9 FUB-level tests (34 parameter points)
PYTHONPATH=bin:$PYTHONPATH pytest projects/components/timing_characterization/dv/tests/fub/ -v

# Run char_top integration test (11 enable-mix configurations)
PYTHONPATH=bin:$PYTHONPATH pytest projects/components/timing_characterization/dv/tests/top/ -v

# Run everything
PYTHONPATH=bin:$PYTHONPATH pytest projects/components/timing_characterization/dv/tests/ -v
```

---

## Architecture

```
                    +-------------------------------------------+
                    |              char_top                      |
                    |                                           |
  i_seed_valid ---->|  +--------+                               |
  i_seed_data  ---->|  | 32-bit |   r_lfsr[31:0]               |
                    |  | Galois |---------------------------+-->| FUB inputs
                    |  |  LFSR  |                           |  |
                    |  +--------+                           |  |
                    |                                       |  |
                    |  +--------------+  +---------------+  |  |
                    |  | nand_chain   |  | inverter_chain|<-+  |
                    |  +--------------+  +---------------+  |  |
                    |  +--------------+  +---------------+  |  |
                    |  | xor_tree     |  | carry_chain   |<-+  |
                    |  +--------------+  +---------------+  |  |
                    |  +--------------+  +---------------+  |  |
                    |  | mux_tree     |  | multiplier    |<-+  |
                    |  |              |  |   _tree       |  |  |
                    |  +--------------+  +---------------+  |  |
                    |  +--------------+  +---------------+  |  |
                    |  | queue_depth  |  | clock_divider |<-+  |
                    |  |              |  |   _chain      |  |  |
                    |  +--------------+  +---------------+  |  |
                    |  +--------------+                     |  |
                    |  | gray_counter |<--------------------+  |
                    |  |   _chain     |                        |
                    |  +--------------+                        |
                    +------------------------------------------+
                              |
                              v
                    o_nand, o_inverter, o_xor, o_carry, o_mult,
                    o_mux, o_queue_data/valid/count,
                    o_clk_div, o_gray_bin, o_gray_code
```

Each FUB is controlled by an `EN_*` parameter. Disabled FUBs emit tie-to-zero
and consume zero logic, allowing targeted synthesis runs.

---

## FUB Catalog

| FUB | RTL File | Key Parameter | Critical Path | What It Measures |
|-----|----------|--------------|---------------|-----------------|
| **nand_chain** | `rtl/fub/nand_chain.sv` | `NAND_LEVELS` | NAND tree depth | Raw NAND-to-LUT mapping |
| **inverter_chain** | `rtl/fub/inverter_chain.sv` | `INVERTER_COUNT` | Linear inverter chain | Baseline per-gate delay |
| **xor_tree** | `rtl/fub/xor_tree.sv` | `XOR_LEVELS` | XOR tree depth | XOR LUT packing efficiency |
| **carry_chain** | `rtl/fub/carry_chain.sv` | `CARRY_WIDTH` | Carry propagation | Dedicated carry-chain speed |
| **multiplier_tree** | `rtl/fub/multiplier_tree.sv` | `MULT_WIDTH`, `MULT_TYPE` | Multiplier reduction tree | DSP vs. LUT-fabric timing |
| **mux_tree** | `rtl/fub/mux_tree.sv` | `MUX_LEVELS` | Mux tree depth | Mux-to-LUT mapping |
| **queue_depth** | `rtl/fub/queue_depth.sv` | `FIFO_DEPTH` | FIFO read path | Memory inference thresholds |
| **clock_divider_chain** | `rtl/fub/clock_divider_chain.sv` | `CLK_DIV_STAGES` | Counter + pickoff mux | Counter-based clock timing |
| **gray_counter_chain** | `rtl/fub/gray_counter_chain.sv` | `GRAY_WIDTH` | Binary carry + XOR tree | Binary-to-Gray conversion |

See `rtl/syn/SYNTHESIS_GUIDE.md` for detailed synthesis goals per FUB.

---

## Directory Structure

```
projects/components/timing_characterization/
├── README.md                      # This file
├── CLAUDE.md                      # AI assistance guide
├── PRD.md                         # Product Requirements Document
├── TASKS.md                       # Task tracking and status
├── bin/                           # Utility scripts (sweep runners, report parsers)
├── docs/                          # Characterization results (future)
├── dv/
│   ├── tbclasses/
│   │   └── timing_char_tb.py      # Shared TB base + LFSR reference model
│   └── tests/
│       ├── fub/                   # 9 FUB-level tests (34 parameter points)
│       │   ├── conftest.py
│       │   ├── test_nand_chain.py
│       │   ├── test_inverter_chain.py
│       │   ├── test_xor_tree.py
│       │   ├── test_carry_chain.py
│       │   ├── test_multiplier_tree.py
│       │   ├── test_mux_tree.py
│       │   ├── test_queue_depth.py
│       │   ├── test_clock_divider_chain.py
│       │   └── test_gray_counter_chain.py
│       └── top/                   # char_top integration test (11 configs)
│           ├── conftest.py
│           └── test_char_top.py
└── rtl/
    ├── common/                    # Shared dependencies (from rtl/common/)
    │   ├── counter_bin.sv
    │   ├── counter_bingray.sv
    │   ├── clock_divider.sv
    │   ├── fifo_control.sv
    │   ├── gaxi_fifo_sync.sv
    │   └── math_multiplier_*.sv   # Structural multiplier variants
    ├── filelists/
    │   └── char_top.f             # Synthesis/simulation filelist
    ├── fub/                       # 9 characterization FUBs
    │   ├── nand_chain.sv
    │   ├── inverter_chain.sv
    │   ├── xor_tree.sv
    │   ├── carry_chain.sv
    │   ├── multiplier_tree.sv
    │   ├── mux_tree.sv
    │   ├── queue_depth.sv
    │   ├── clock_divider_chain.sv
    │   └── gray_counter_chain.sv
    ├── syn/                       # Synthesis constraints and guide
    │   ├── char_top.sdc           # Multi-flow SDC (ASIC/Vivado/Quartus)
    │   └── SYNTHESIS_GUIDE.md     # Comprehensive synthesis documentation
    └── top/                       # Top-level wrappers
        ├── char_top.sv            # Main synthesis target (9 FUBs + LFSR)
        └── nand_chain_top.sv      # Standalone NAND chain wrapper
```

---

## Synthesis

The SDC (`rtl/syn/char_top.sdc`) supports three flows:

| Flow | Tool | Key setup |
|------|------|----------|
| `"asic"` | Synopsys DC / Cadence Genus | Target library, operating conditions |
| `"vivado"` | Xilinx Vivado | Part number |
| `"quartus"` | Intel Quartus Prime | FAMILY, DEVICE in .qsf |

```tcl
# Example: Vivado at 500 MHz
set FLOW "vivado"
set TARGET_FREQ_MHZ 500.0
source char_top.sdc
```

See `rtl/syn/SYNTHESIS_GUIDE.md` for complete workflow, parameter sweeps,
and result interpretation.

---

## Verification Status

| Test Suite | Tests | Status |
|-----------|-------|--------|
| FUB tests (9 FUBs, 34 parameter points) | 34 | All passing |
| char_top integration (11 enable-mix configs) | 11 | All passing |
| **Total** | **45** | **All passing** |

---

## Design Standards

All components follow repository standards:

- **Reset macros** (`ALWAYS_FF_RST`) on all flip-flops
- **Synthesis preservation** (`dont_touch` / `preserve`) on all chain signals
- **Modern array syntax** `[DEPTH]` not `[0:DEPTH-1]`
- **TB classes** in `dv/tbclasses/` (not in test files)
- **Three mandatory TB methods** (setup_clocks_and_reset, assert_reset, deassert_reset)

**See:**
- Root `/CLAUDE.md` -- Repository-wide standards
- `/GLOBAL_REQUIREMENTS.md` -- Mandatory requirements
- `projects/components/CLAUDE.md` -- Component-area standards

---

## Navigation

- **Back to Components:** [`../README.md`](../README.md)
- **Product Requirements:** [`PRD.md`](PRD.md)
- **Task Tracking:** [`TASKS.md`](TASKS.md)
- **Synthesis Guide:** [`rtl/syn/SYNTHESIS_GUIDE.md`](rtl/syn/SYNTHESIS_GUIDE.md)
- **Repository Guide:** [`/CLAUDE.md`](../../../CLAUDE.md)
- **Global Requirements:** [`/GLOBAL_REQUIREMENTS.md`](../../../GLOBAL_REQUIREMENTS.md)
