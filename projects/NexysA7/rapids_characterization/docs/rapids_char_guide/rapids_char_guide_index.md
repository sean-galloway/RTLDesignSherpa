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

# RAPIDS Characterization — Project Guide

**Version:** 0.90
**Date:** 2026-07-18
**Purpose:** Operator / developer guide for the Nexys A7 `rapids_characterization`
project — how it works, how to build/simulate/program/run it, and the harness
CSR configuration. The RAPIDS beats DMA core is the device under test.

---

## Document Organization

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [What It Characterizes](ch01_overview/01_overview.md)

### Chapter 2: How It Works

- [Architecture: Region Decode, Harness, Engines](ch02_how_it_works/01_architecture.md)

### Chapter 3: Build and Run

- [Make Targets and the Host Campaign](ch03_build_and_run/01_build_and_run.md)

### Chapter 4: Harness CSR Configuration

- [Region Map and Register Map](ch04_harness_csr/01_register_map.md)

### Chapter 5: Simulation vs Silicon

- [Two Paths to the Same Golden CRC](ch05_sim_equivalence/01_equivalence.md)

### Chapter 6: Troubleshooting

- [Known State and Common Issues](ch06_troubleshooting/01_troubleshooting.md)

---

## Quick Reference

### Make Targets (`flows-rapids-beats`)

| Target | What it does |
|--------|--------------|
| `make sim` | cocotb harness self-check (sink + source) |
| `make bitstream` | Build the bitstream (depends on `verify-sim`) |
| `make program` | Flash the board |
| `make smoke` | Fast golden-validated UART confidence check |
| `make suite` | Full UART sweep → JSON reports |
| `make flow` | sim → bitstream → program → characterize |

### Identity

| Item | Value |
|------|-------|
| BUILD_ID / `RAP1` | `0x5241_5031` (region-2 `CTRL`/`ID` @ 0x000) |
| Region bases | DUT-REG 0x0_0000 · DESC-LOAD 0x1_0000 · HARNESS CSR 0x2_0000 |
| APB halves | SRC 0x0000 · SNK 0x1000 |

---

**Last Updated:** 2026-07-18
**Maintained By:** RTL Design Sherpa Project
