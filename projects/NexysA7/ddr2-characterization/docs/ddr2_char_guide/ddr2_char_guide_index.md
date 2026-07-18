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

# DDR2/LPDDR2 Characterization — Project Guide

**Version:** 0.90
**Date:** 2026-07-18
**Purpose:** Operator / developer guide for the Nexys A7 `ddr2-characterization`
project — how it works, how to build/simulate/program/run it, and the harness
CSR configuration. The DDR2 controller under test (pumice) is separate IP and is
treated here as a black box.

---

## Document Organization

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [What It Characterizes and the Flows](ch01_overview/01_overview.md)

### Chapter 2: How It Works

- [Architecture: Spine, Bridge, Engines, DFI](ch02_how_it_works/01_architecture.md)

### Chapter 3: Build and Run

- [Make Targets and the Host Programs](ch03_build_and_run/01_build_and_run.md)

### Chapter 4: Harness CSR Configuration

- [Address Map and Register Map](ch04_harness_csr/01_register_map.md)

### Chapter 5: Simulation / Silicon Equivalence

- [One Program, Two Targets](ch05_sim_equivalence/01_equivalence.md)

### Chapter 6: Troubleshooting

- [Known State and Common Issues](ch06_troubleshooting/01_troubleshooting.md)

---

## Quick Reference

### Flows

| Flow | Controller (DUT) | Purpose |
|------|------------------|---------|
| `flows-ours-uart/` | pumice DDR2 (black box) + a7ddrphy | Primary: UART-driven host + Vivado build |
| `flows-litedram-uart/` | LiteDRAM `litedram_core` | Apples-to-apples baseline, same engines/host |
| `ddr2_char_framework/` | — | Shared harness RTL + engines + cocotb DV |

### Bring-up sequence (flows-ours-uart)

| Step | Command |
|------|---------|
| Build bitstream | `make bitstream` |
| Program board | `make program` |
| Link smoke | `make smoke UART=/dev/ttyUSB1` |
| PHY leveling | `make level` |
| Write→read integrity | `make simple` |
| Full sweep | `make characterize` |
| Sim (no board) | `make sim` |

---

**Last Updated:** 2026-07-18
**Maintained By:** RTL Design Sherpa Project
