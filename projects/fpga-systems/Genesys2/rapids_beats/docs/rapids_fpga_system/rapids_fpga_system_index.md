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

# RAPIDS beats on the Genesys 2 -- The FPGA System

**Version:** 1.0
**Date:** 2026-09-29
**Purpose:** What is on the bench and in the bitstream for the `rapids_beats`
characterization system: the board, the harness that surrounds the DUT, why
there is one RTL source and several bitstreams built from it at different
parameters, and how a host command becomes a number in the performance
report. The RAPIDS beats DMA core is the device under test; its own
architecture lives in the RAPIDS HAS/MAS under
`projects/components/dma-ip/rapids/docs/`.

> The measured results are in the performance report,
> `reports/perf/README.md` (v2.2 as of this writing). This book explains the
> apparatus those numbers came out of. The older operator guide
> (`rapids_char_guide`, v0.90) predates the Genesys 2 port and the 256-bit
> design point; this book supersedes its system description.

---

## Document Organization

### Front Matter
- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: The System
- [Board, Host, Clocks and the Two USB Chips](ch01_overview/01_system.md)

### Chapter 2: The Harness
- [Every Block Around the DUT, and the Launch Path](ch02_harness/01_harness.md)

### Chapter 3: One RTL, Several Bitstreams
- [The Build Variants and Why Each Exists](ch03_builds/01_build_variants.md)

### Chapter 4: Host Tools and Flow
- [From a Make Target to a Report Cell](ch04_host_and_flow/01_host_and_flow.md)

---

## Quick Reference

### Where things are

| Item | Path (under `projects/fpga-systems/Genesys2/rapids_beats/`) |
|------|------|
| Board top, pin top, harness | `flows-rapids-beats/rtl/rapids_char_genesys2_top.sv`, `rapids_char_top.sv`, `rapids_char_harness.sv` |
| Build knobs | `flows-rapids-beats/Makefile` (BOARD, CHANNELS, DATA_WIDTH, SRAM_DEPTH, USE_AXI_MONITORS, GEN_MON, USE_OBSERVERS, OBS_ENABLE_MON_TAPS) |
| Vivado scripts | `flows-rapids-beats/tcl/` (create_project, build_all, build_ila, capture_ila_*) |
| Host tools | `flows-rapids-beats/host/` (run_characterization.py and friends) |
| Sim gate | `flows-rapids-beats/dv/test_rapids_char_harness.py` |
| Results and report | `reports/perf/` (README.md, json/, plots/, the versioned DOCX/PDF) |

### Identity

| Item | Value |
|------|-------|
| Board | Digilent Genesys 2, Kintex-7 XC7K325T-2 |
| aclk | 100 MHz (200 MHz LVDS sysclk through an MMCM) |
| Host link | UART 115200-8N1 on the board's FT232R; JTAG on its FT2232 |
| ID register | `RAP1` = `0x5241_5031` at harness CSR 0x000 |
| BUILD register | harness CSR 0x004: bytes/beat, channels, log2 SRAM depth, monitors, observers, GEN_MON |
| Design point | 256-bit AXI4 and AXIS, 8 channels, 128 beats (4 KB) of SRAM per channel |
