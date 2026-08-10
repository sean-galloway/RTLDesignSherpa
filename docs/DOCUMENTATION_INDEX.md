# RTL Design Sherpa Documentation

**Repository:** [RTLDesignSherpa](https://github.com/sean-galloway/RTLDesignSherpa)

*A progressive learning framework for RTL development using open-source tools*

---

## About This Documentation

This documentation supports **RTL Design Sherpa** - a hands-on learning
framework for digital hardware design, from fundamental building blocks to
production-ready FPGA systems, with comprehensive verification at every step.

**What makes RTL Design Sherpa different:**
- Progressive learning path (from counters to complete FPGA systems)
- Comprehensive test suites using CocoTB
- Open-source tools only (Verilator, pytest, PeakRDL, SymbiYosys)
- Industry best practices
- Complete transparency - all design decisions explained, failures included

---

## Start Here

### The Handbook - [handbook/](../vault/handbook/INDEX.md)

The repository's working memory: atomic, cross-linked notes on design rules,
DV practice, and FPGA process - each rule recorded with the failure that
taught it.

- **[handbook/design/](../vault/handbook/design/INDEX.md)** - reset and clocking, CDC,
  valid/ready contracts, streaming vs minimal FSMs, SRAM rules, sizing
  invariants, priority-logic depth, signal contracts and K-maps
- **[handbook/dv/](../vault/handbook/dv/INDEX.md)** - BFM usage, registers-by-name,
  seeds and determinism, TB structure, coverage, formal
- **[handbook/fpga/](../vault/handbook/fpga/INDEX.md)** - build flows, timing-closure
  triage, the UART harness, board handling

Authority hierarchy: [/GLOBAL_REQUIREMENTS.md](../GLOBAL_REQUIREMENTS.md)
(enforced) > handbook (practice and rationale) > code comments.

### User Guides - [user-guides/](user-guides/)

Practical how-tos for DOING something:

- **[AXI_Monitor_Configuration_Guide.md](user-guides/AXI_Monitor_Configuration_Guide.md)** -
  configure the AXI monitors (packet classes, masks, sizing)
- **[VERIFICATION_ARCHITECTURE_GUIDE.md](user-guides/VERIFICATION_ARCHITECTURE_GUIDE.md)** -
  verification methodology: three-layer TBs, queue vs memory-model checking
- **[rtl_coverage_guidelines.md](user-guides/rtl_coverage_guidelines.md)** -
  coverage methodology (fronted by the `coverage` skill)
- **[descriptor_engine_waveform_guide.md](user-guides/descriptor_engine_waveform_guide.md)** -
  debugging descriptor engines with waveforms
- **[HOW_TO_ADD_WAVES_SUPPORT.md](user-guides/HOW_TO_ADD_WAVES_SUPPORT.md)** -
  adding waveform capture to tests (update pending)
- **[GAXI_WAVEDROM_GUIDE.md](../bin/TBClasses/wavedrom_user/GAXI_WAVEDROM_GUIDE.md)** -
  WaveDrom capture and signal binding (lives with the tooling)

---

## RTL Library Books - [markdown/](markdown/)

Per-subsystem reference books; each renders to a PDF in this directory via
`markdown/generate_rtl_pdfs.sh`:

| Book source | Rendered PDF |
|---|---|
| [markdown/rtl-common/](markdown/rtl-common/) | [RTL_Common_Library.pdf](pdfs/RTL_Common_Library.pdf), [RTL_Math_Library.pdf](pdfs/RTL_Math_Library.pdf) |
| [markdown/rtl-amba/](markdown/rtl-amba/) | [RTL_AMBA_*.pdf](pdfs/) (APB4/APB5, AXI4, AXI4-Lite, AXI4/AXI5-Stream, AXI5, Monitor, Shared) |
| [markdown/rtl-amba/cdc/](markdown/rtl-amba/cdc/) | [RTL_CDC.pdf](pdfs/RTL_CDC.pdf) |
| [markdown/Scripts/](markdown/Scripts/) | tooling reference (assets in [Scripts/assets/](markdown/Scripts/assets/)) |
| [markdown/TestTutorial/](markdown/TestTutorial/) | getting started with testing |

Shared assets: [markdown/assets/](markdown/assets/) (WAVES waveform sets,
book front-matter). [logos/](logos/) - project branding.

---

## Component and Project Documentation

Specs live WITH their components, not here:

- **Components:** `projects/components/<name>/docs/` - HAS/MAS spec books
  with per-project `generate_pdf.sh` (dmas/stream, dmas/rapids, bridge,
  retro_legacy_blocks, memory-controllers/pumice-ddr2-lpddr2, ...)
  Master list: [../projects/components/index.md](../projects/components/index.md)
- **Board campaigns:** `projects/NexysA7/<campaign>/docs/` - operator guides
  and characterization reports
- **Subsystem guides:** `rtl/<area>/` CLAUDE.md, PRD.md, KNOWN_ISSUES/

---

## Learning Levels

1. **Common building blocks** - `rtl/common/` (counters, FIFOs, arbiters,
   CDC, data integrity) and `rtl/math/` (integer + floating-point arithmetic)
2. **AMBA protocol infrastructure** - `rtl/amba/` (APB, AXI4, AXI4-Lite,
   AXI-Stream, monitors, monbus)
3. **Integration examples** - `rtl/integ_common/`, `rtl/integ_amba/`
4. **Production components** - `projects/components/` (STREAM and RAPIDS
   DMAs, Bridge, APB crossbars, Retro Legacy Blocks, pumice memory
   controller)
5. **Complete FPGA projects** - `projects/NexysA7/` characterization
   campaigns (Nexys A7 and Genesys 2)

---

## Standards and Process

- **[DOCUMENTATION_STANDARDS.md](DOCUMENTATION_STANDARDS.md)** - doc style
  rules (no emojis in pipeline docs, caption encoding for LoF/LoT/LoW)
- **[/GLOBAL_REQUIREMENTS.md](../GLOBAL_REQUIREMENTS.md)** - mandatory
  repository requirements (the authority)
- **[vault/handbook/dv/](../vault/handbook/dv/INDEX.md)** - running tests:
  [test-runner](../vault/handbook/dv/test-runner.md) (REG_LEVEL/TEST_LEVEL,
  WAVES), [running-regressions](../vault/handbook/dv/running-regressions.md)
  (always the Makefile targets, never bare pytest),
  [seeds-and-determinism](../vault/handbook/dv/seeds-and-determinism.md)
- **[/bin/DOC_GENERATION.md](../bin/DOC_GENERATION.md)** - the doc pipeline:
  md_to_docx (--style required), book indexes, PDF generation
- **[kimi_humanization_style_guide.md](kimi_humanization_style_guide.md)** -
  voice guide for the external doc-review humanization pass
- **[fifo_depth_calculator_v2.xlsx](fifo_depth_calculator_v2.xlsx)** - FIFO
  sizing calculator (CDC-aware)

---

## For AI Assistants

Skills in `.claude/skills/` are auto-discovered signposts into the handbook.
Root [/CLAUDE.md](../CLAUDE.md) is loaded every session and points here.
When you learn a durable lesson, add it to the relevant handbook note - that
is where future sessions look.
