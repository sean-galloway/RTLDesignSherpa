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

# Reed-Solomon UART Harness

**Version:** 0.1
**Date:** 2026-10-06
**Purpose:** What the RS(252,236) t=8 UART harness is, what is inside it, how
the pieces connect, and why the FPGA testing choices are shaped the way they
are. This is the harness guide; the run evidence lives in the companion
*Reed-Solomon Board Validation Report*.

---

## Document Organization

### Front Matter
- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview
- [Purpose and Geometry](ch01_overview/01_purpose.md)

### Chapter 2: The Harness
- [What Is In It](ch02_the_harness/01_contents.md)
- [How The Pieces Connect](ch02_the_harness/02_connectivity.md)

### Chapter 3: Testing Choices
- [The FPGA-Testing Choices, And Why](ch03_testing_choices/01_choices.md)

### Chapter 4: Operation
- [Operating It](ch04_operation/01_operating.md)
- [What Is Deliberately Not Board-Tested](ch04_operation/02_not_board_tested.md)

---

## Quick Reference

| Item | Path (under `projects/fpga-systems/Genesys2/ecc-ip/reed-solomon/`) |
|------|------|
| Harness markdown (living copy) | `docs/UART_HARNESS.md` |
| Board validation book | `docs/Reed_Solomon_Board_Validation_v0.1.pdf` |
| Build record | `stable/MANIFEST.md` |
| Run artifacts | `stable/results/` |
| Bitstreams | `stable/reports/genesys2_{axis_ribm,axis_euclid,axi4_ribm,axi4_euclid}/` |

| Item | Value |
|------|-------|
| Codec | RS(252,236) t=8, 4 symbols/beat |
| Board | Digilent Genesys 2, Kintex-7 XC7K325T-2 |
| Board serial | `200300B818A0` |
| Toolchain | Vivado 2025.1 |
| Harness clock | 100 MHz derived from 200 MHz LVDS input |
| Host link | UART 115200-8N1 |
