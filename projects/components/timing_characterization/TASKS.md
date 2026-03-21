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

# Timing Characterization -- Task List

**Component:** Timing Characterization (Synthesis Benchmarking Harness)
**Last Updated:** 2026-03-18
**Version:** 1.0
**Status:** Core complete -- enhancement opportunities remain

---

## Current Status

### Completed (100% of core)

**FUB RTL (9/9):**
- [x] nand_chain.sv -- NAND gate binary tree
- [x] inverter_chain.sv -- Linear inverter chain
- [x] xor_tree.sv -- XOR gate binary tree
- [x] carry_chain.sv -- Ripple-carry adder
- [x] multiplier_tree.sv -- Multiplier wrapper (5 types)
- [x] mux_tree.sv -- Binary mux tree
- [x] queue_depth.sv -- FIFO queue (wraps gaxi_fifo_sync)
- [x] clock_divider_chain.sv -- Cascaded clock dividers
- [x] gray_counter_chain.sv -- Binary/Gray counter

**Top-Level:**
- [x] char_top.sv -- 9-FUB wrapper with shared LFSR
- [x] nand_chain_top.sv -- Standalone NAND chain wrapper

**Synthesis Infrastructure:**
- [x] char_top.sdc -- Multi-flow SDC (ASIC/Vivado/Quartus)
- [x] SYNTHESIS_GUIDE.md -- Comprehensive synthesis documentation

**Verification (45/45 tests passing):**
- [x] 9 FUB-level test files (34 parameter-sweep test cases)
- [x] char_top integration test (11 enable-mix configurations)
- [x] Shared TB base class (TimingCharTB) with LFSR reference model
- [x] conftest.py for both fub/ and top/ test directories

**Documentation:**
- [x] README.md -- Component overview
- [x] PRD.md -- Product requirements
- [x] TASKS.md -- This file
- [x] CLAUDE.md -- AI assistance guide

**Filelists:**
- [x] char_top.f -- Full synthesis/simulation filelist

---

## Remaining Work (Enhancements)

### TASK-001: Parameter Sweep Automation Scripts
**Status:** Planned
**Priority:** P1 (High)
**Effort:** 1-2 days

**Description:**
Create scripts in `bin/` to automate synthesis parameter sweeps and parse
timing reports into structured results.

**Acceptance Criteria:**
- [ ] Vivado batch sweep script (Tcl)
- [ ] Quartus batch sweep script (Tcl)
- [ ] Timing report parser (Python) extracting slack, data path delay, logic levels
- [ ] CSV/JSON output for downstream analysis
- [ ] Example sweep configuration file

**Files:**
- `bin/syn_sweep_vivado.tcl` (to be created)
- `bin/syn_sweep_quartus.tcl` (to be created)
- `bin/parse_timing_report.py` (to be created)

---

### TASK-002: Cross-Technology Comparison Reports
**Status:** Planned
**Priority:** P2 (Standard)
**Effort:** 1 day

**Description:**
Run baseline synthesis sweeps on available targets and document results in
`docs/` with comparison tables.

**Acceptance Criteria:**
- [ ] At least two FPGA targets compared (e.g., Artix-7 vs. UltraScale+)
- [ ] Carry chain width sweep results
- [ ] NAND depth sweep results
- [ ] DSP vs. LUT multiplier comparison
- [ ] Results documented in markdown tables

**Files:**
- `docs/baseline_results.md` (to be created)

---

### TASK-003: Additional FUBs
**Status:** Planned
**Priority:** P3 (Low)
**Effort:** 1-2 days per FUB

**Description:**
Add new characterization FUBs to broaden logic family coverage.

**Candidates:**
- [ ] Barrel shifter -- Funnel shift timing
- [ ] Priority encoder -- Wide OR-tree characterization
- [ ] Comparator chain -- Magnitude comparator depth
- [ ] DSP chain -- Cascaded DSP48 slice timing (Xilinx-specific)

**Files:**
- `rtl/fub/{new_fub}.sv` (to be created per FUB)
- `dv/tests/fub/test_{new_fub}.py` (to be created per FUB)
- char_top.sv updates (new EN_* parameters)

---

### TASK-004: PDF Generation for Synthesis Guide
**Status:** Planned
**Priority:** P3 (Low)
**Effort:** 0.5 day

**Description:**
Add markdown-to-PDF generation script for SYNTHESIS_GUIDE.md, following
the pattern used by bridge and stream components.

**Acceptance Criteria:**
- [ ] `docs/generate_pdf.sh` script
- [ ] Clean PDF output from SYNTHESIS_GUIDE.md
- [ ] No emoji issues in LaTeX pipeline

**Files:**
- `docs/generate_pdf.sh` (to be created)

---

## Completed Major Milestones

- [x] **2026-03-17:** Initial directory structure and CLAUDE.md
- [x] **2026-03-17:** All 9 FUB RTL modules implemented
- [x] **2026-03-17:** char_top.sv with shared LFSR and 9 EN_* parameters
- [x] **2026-03-17:** All 34 FUB-level tests passing
- [x] **2026-03-18:** char_top integration test -- 11/11 passing (LFSR pipeline alignment fixed)
- [x] **2026-03-18:** LFSR reference model centralized in timing_char_tb.py
- [x] **2026-03-18:** Multi-flow SDC (ASIC/Vivado/Quartus) and SYNTHESIS_GUIDE.md
- [x] **2026-03-18:** Complete documentation suite (README, PRD, TASKS, CLAUDE)

---

## Notes

**Architecture Stability:** All 9 FUBs and char_top are functionally verified.
The RTL is stable and ready for synthesis characterization runs.

**Synthesis Guide:** `rtl/syn/SYNTHESIS_GUIDE.md` contains detailed per-FUB
synthesis goals, SDC strategy, workflow instructions, and result interpretation.

**Shared Dependencies:** RTL modules from `rtl/common/` are copied into this
component's `rtl/common/` directory to keep the filelist self-contained.
