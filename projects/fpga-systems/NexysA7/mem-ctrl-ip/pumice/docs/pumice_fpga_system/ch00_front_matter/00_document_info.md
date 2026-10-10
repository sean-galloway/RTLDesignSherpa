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

# Document Information

| Field | Value |
|-------|-------|
| Title | pumice on the Nexys A7 -- The FPGA System |
| Version | 1.0 |
| Date | 2026-09-29 |
| Scope | The DDR2 characterization system: board, the harness around the controller, the five things built from one harness source, and the host flow |
| Not in scope | The pumice controller itself (HAS/MAS under `projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2/docs/`); the measured results (`build-perf/results/`, `ddr2-characterization/char_results/`) |
| Status | Current; written against the tree after the `mem-ctrl-ip` and `fabric-gen-ip` family moves |

: Table 0.1: Document information

## Related documents

| Document | Where | What it gives you |
|---|---|---|
| pumice HAS / MAS | `projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2/docs/` | the controller's own architecture; this book treats it as the DUT |
| Harness address map | `build-perf/host/ADDRESS_MAP.md` | the authoritative register decode, mirrored from the RTL |
| LiteDRAM flow README | `ddr2-characterization/flows-litedram-uart/README.md` | the A/B reference build and its config |
| DDR2 char guide | `ddr2-characterization/docs/ddr2_char_guide/` | the older operator guide (v0.90) |
| STREAM / RAPIDS system books | `projects/fpga-systems/Genesys2/*/docs/*_fpga_system/` | the same book for the Genesys 2 boards |

: Table 0.2: Related documents

## Terminology

**DFI**
DDR PHY Interface. The boundary between the controller and the PHY, and the
same boundary the DV repo's BFM drives in simulation.

**a7ddrphy**
LiteDRAM's Artix-7 DDR PHY, reused verbatim. It owns the IOB serdes, bitslip
and IDELAY training that are FPGA-specific and deliberately out of the
controller's scope.

**Harness**
Everything in the bitstream that is not the DUT: the UART bridge, the address
bridge, the CSR block, the stimulus generators, the meters and the displays.

**Engine spine**
`char_engine_block.sv` -- the DUT-agnostic part of the harness: generator
registers, generator array, AXI merge, bus meters and latency histograms.

**Design point**
75 MHz system clock (`PUMICE_SYS_75`), 1:2 gear to a 150 MHz DDR2 clock,
300 MT/s, BL4 on a 16-bit bus: 600 MB/s theoretical peak.

## Revision History

| Version | Date | Change |
|---------|------|--------|
| 1.0 | 2026-09-29 | First edition. Written after the family-directory moves, so every path in it is `mem-ctrl-ip/` and `fabric-gen-ip/`. |

: Table 0.3: Revision history

## How to read this book

Chapter 1 is the bench: one USB connector, one DRAM part, and the clock chain
that fixes the peak every later number is measured against. Chapter 2 is the
bitstream around the DUT, block by block, with the address map every host tool
depends on -- and, for each block, why it is shaped the way it is. Chapter 3 is
the chapter that answers the question people actually ask: the harness RTL does
*not* change per build, and the chapter says what does. Chapter 4 is the
measurement loop, including two traps that have each cost a wrong conclusion.

Every diagram is a Graphviz source under `assets/graphviz/`, rendered to PNG by
`regenerate_all_graphviz.sh`. Edit the `.dot`, re-run the script, never hand-edit
a PNG.
