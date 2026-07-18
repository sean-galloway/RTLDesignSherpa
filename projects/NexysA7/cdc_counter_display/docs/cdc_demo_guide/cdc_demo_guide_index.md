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

# CDC Counter Display — Project Guide

**Version:** 0.90
**Date:** 2026-07-18
**Purpose:** Operator / developer guide for the Nexys A7 `cdc_counter_display`
project — how it works, how to build/simulate/program/run it, and the harness
CSR configuration.

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [What It Is and What It Demonstrates](ch01_overview/01_overview.md)

### Chapter 2: How It Works

- [Architecture, Clocking, and CDC Modes](ch02_how_it_works/01_architecture.md)

### Chapter 3: Test Methodology

- [What Is Tested and How](ch03_methodology/01_methodology.md)

### Chapter 4: Build and Run

- [Makefile Targets and the Host CLI](ch04_build_and_run/01_build_and_run.md)

### Chapter 5: Harness CSR Configuration

- [Register Map and By-Name Access](ch05_harness_csr/01_register_map.md)

### Chapter 6: Simulation / Silicon Equivalence

- [One Program, Two Targets](ch06_sim_equivalence/01_equivalence.md)

### Chapter 7: Troubleshooting

- [Common Issues and Fixes](ch07_troubleshooting/01_troubleshooting.md)

---

## Quick Reference

### Make Targets

| Target | Phase | What it does |
|--------|-------|--------------|
| `make sim` | 1 | Phase-1 CocoTB sim (`cdc_counter_display_top`) |
| `make sim-demo` | 2 | UART-equivalence sim (real bridge + harness; runs host programs) |
| `make regmap` | 2 | Regenerate the by-name regmap from `rtl/cdc_demo_csr.rdl` |
| `make consistency` | 2 | Guard: regmap vs hand-written harness SV |
| `make build-demo` | 2 | Build the phase-2 bitstream (`cdc_demo.bit`) |
| `make program-demo` | 2 | Flash the board |
| `make lint-demo` | 2 | Verilator lint (Xilinx primitives stubbed) |

### Host CLI (`host/run_cdc_demo.py`)

| Subcommand | Purpose |
|------------|---------|
| `smoke` | BUILD_ID + SCRATCH round-trip + per-counter defaults |
| `press` | Inject N HOST_PRESS events, verify VALUE = INIT + N*INC |
| `cfg-load` | CFG_LOAD reloads VALUE to INIT |
| `cdc-mode` | Round-trip every CDC_MODE code |
| `monitor` | Real-time VALUE / PRESS_COUNT for all four counters |
| `watch-fail` | NO-CDC + AUTO_INC, sweep pickoff slow→fast |
| `reset` / `set` / `get` | Soft reset / raw poke / raw peek |

---

**Last Updated:** 2026-07-18
**Maintained By:** RTL Design Sherpa Project
