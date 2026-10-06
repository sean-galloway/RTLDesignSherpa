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

# Binary BCH Board Validation Report

**Version:** 0.1
**Date:** 2026-10-05
**Purpose:** What was built, how it was exercised, and what the board says about
the BCH(4224,4120) t=8 codec on the Digilent Genesys 2. This book is the
publication-ready roll-up of the harness, the campaign methodology, and the
2026-10-05 one-million-block soak.

---

## Document Organization

### Front Matter
- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview
- [Scope and Claims](ch01_overview/01_scope.md)
- [Images and Codec Profile](ch01_overview/02_images.md)

### Chapter 2: The Harness
- [Architecture](ch02_harness/01_architecture.md)

### Chapter 3: Methodology
- [Campaigns and the Oracle Argument](ch03_methodology/01_campaigns.md)
- [Testing Choices](ch03_methodology/02_testing_choices.md)

### Chapter 4: Findings
- [Soak Results](ch04_findings/02_soak.md)

### Chapter 5: Limits
- [Honest Limits](ch05_limits/01_limits.md)

---

## Quick Reference

| Item | Path (under `projects/fpga-systems/Genesys2/bch/`) |
|------|------|
| Harness documentation | `docs/UART_HARNESS.md` |
| Build record | `stable/MANIFEST.md` |
| Soak artifacts | `stable/results/2026-10-05_soak/` |
| Bitstreams | `stable/reports/genesys2_axis/`, `stable/reports/genesys2_axi4/` |

| Item | Value |
|------|-------|
| Board | Digilent Genesys 2, Kintex-7 XC7K325T-2 |
| Board serial | `200300B818A0` |
| Toolchain | Vivado 2025.1 |
| Harness clock | 100 MHz derived from 200 MHz LVDS input |
| Host link | UART 115200-8N1 |
