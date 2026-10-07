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

# pumice on the Nexys A7 -- The FPGA System

**Version:** 1.0
**Date:** 2026-09-29
**Purpose:** What is on the bench and in the bitstream for the DDR2
characterization system: the board and the clock chain that fixes the peak, the
harness that surrounds the controller and why each block is shaped the way it
is, why one harness source produces five targets, and how a host command becomes
a number. The pumice DDR2/LPDDR2 controller is the device under test; its own
architecture lives in the pumice HAS/MAS under
`projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/docs/`.

> The measured results live in `build-perf/results/` and
> `ddr2-characterization/char_results/`. This book explains the apparatus those
> numbers came out of. The older operator guide
> (`ddr2-characterization/docs/ddr2_char_guide/`) and the
> `ddr2-characterization/README.md` skeleton notice both predate the working
> `build-perf` harness; this book supersedes their system description.

---

## Quick reference

| Question | Answer | Chapter |
|---|---|---|
| Theoretical peak? | 600 MB/s (300 MT/s x 2 bytes, BL4 x16) | 1 |
| Design point? | 75 MHz system, `PUMICE_SYS_75`; 66.67 MHz is not it | 1, 3 |
| Where do host tools find registers? | `harness_csr` at `0x0001_0000`, controller APB at `0x0` | 2 |
| Is the harness RTL different per build? | No. One source; the DUT, the PHY or the ILA cores change | 3 |
| Why is there a LiteDRAM build? | Same harness, different controller, so the numbers compare | 3 |
| Why did my CSR write not take? | `Config.apply()` re-programs every CSR on every point | 4 |
| Why is my percentage half what it should be? | `bytes_moved` is per phase, not both directions | 4 |

: Table 0.0: Quick reference

---

## Document Organization

### Front Matter
- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: The System
- [Board, the Single USB Connector, and the Clock Chain](ch01_overview/01_system.md)

### Chapter 2: The Harness
- [Every Block Around the DUT, the Address Map, and Why Each Block Is Shaped That Way](ch02_harness/01_harness.md)

### Chapter 3: One Harness, Five Targets
- [What Actually Changes Per Build, and What Does Not](ch03_builds/01_build_variants.md)

### Chapter 4: Host Tools and Flow
- [The Shared Transport, Bring-Up, and the Two Traps in the Arithmetic](ch04_host_and_flow/01_host_and_flow.md)

---

## Diagrams

Every figure is a Graphviz source in `assets/graphviz/`, rendered to PNG by
`assets/graphviz/regenerate_all_graphviz.sh`. Edit the `.dot` and re-run the
script; never hand-edit a PNG.

| Figure | Source | Subject |
|---|---|---|
| 1.1 | `01_board_and_host.dot` | host, the single USB connector, the Artix-7, the DDR2 part |
| 2.1 | `02_harness_blocks.dot` | every block around the DUT and the address map |
| 3.1 | `03_build_variants.dot` | one harness source, five targets |
| 4.1 | `04_measurement_path.dot` | from a host command to a row of the CSV |

: Table 0.1: The diagrams and their sources
