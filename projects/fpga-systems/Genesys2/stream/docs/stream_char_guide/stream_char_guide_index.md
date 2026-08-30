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

# STREAM Characterization — Project Guide

**Version:** 0.90
**Date:** 2026-07-18
**Purpose:** Operator / developer guide for the Nexys A7 `stream_characterization`
project — how it works, how to build/simulate/program/run it, and the harness CSR
configuration. The STREAM scatter-gather DMA is the device under test.

> This is the **characterization project** guide (`projects/NexysA7/stream_characterization/`).
> The STREAM core's architecture specs (HAS/MAS) live separately under
> `projects/components/dmas/stream/docs/`.

---

## Document Organization

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [What It Characterizes and the Flow Matrix](ch01_overview/01_overview.md)

### Chapter 2: How It Works

- [Architecture: Spine, Bridge, Harness](ch02_how_it_works/01_architecture.md)

### Chapter 3: Test Methodology

- [What Is Tested and How](ch03_methodology/01_methodology.md)

### Chapter 4: Build and Run

- [Make Targets and the Host Tools](ch04_build_and_run/01_build_and_run.md)

### Chapter 5: Harness CSR Configuration

- [Address Map and Register Map](ch05_harness_csr/01_register_map.md)

### Chapter 6: Simulation / Silicon Equivalence

- [One Program, Two Targets](ch06_sim_equivalence/01_equivalence.md)

### Chapter 7: Troubleshooting

- [Known State and Common Issues](ch07_troubleshooting/01_troubleshooting.md)

---

## Quick Reference

### Primary flow (`flows-stream-bridge`)

| Target | What it does |
|--------|--------------|
| `make bitstream` | regen-bridges + verify-sim + full P&R → `bitstream/stream_char.bit` |
| `make program` | JTAG flash |
| `make sim` | cocotb regression (`run-all-full-parallel`) |
| `make area` | out-of-context bare-DMA area report |

### Identity

| Item | Value |
|------|-------|
| BUILD_ID / `STRC` | `0x5354_5243` (harness CSR `0x24`) |
| Autodetect | SCRATCH echo of `0xC0FFEE5A` |
| harness_csr base | `0x0001_0000` |

---

**Last Updated:** 2026-07-18
**Maintained By:** RTL Design Sherpa Project
