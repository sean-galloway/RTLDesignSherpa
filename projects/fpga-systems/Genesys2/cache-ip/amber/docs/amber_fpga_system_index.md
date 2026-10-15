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

**[← Back to README](../README.md)**

# Amber Pair-Rig on Genesys 2 -- FPGA System Book

**Version:** 1.0
**Date:** 2026-10-14
**Purpose:** What is on the bench and in the bitstream for the amber MESI L1
cache pair-rig bring-up: the board, the harness, the host flow, the address
space, and the internal block diagrams of every significant piece.

---

## Document Organization

- [Address Map and Register Details](address_map.md)

---

## Quick Reference

| Question | Answer |
| --- | --- |
| Board | Digilent Genesys 2 (Kintex-7 `xc7k325tffg900-2`) |
| Clock | 90 MHz from 200 MHz LVDS oscillator via MMCM |
| Host link | UART 115200 8N1 through FT232R |
| DUT top | `amber_pair_genesys2_top` |
| Harness | `amber_pair_harness` |
| Cache geometry | `s128w4l64b64` (128 sets, 4 ways, 64-byte line, 64-bit bus) |
| Shared memory | 512 KB on-chip BRAM (`sdpram_slave_axi4_axi4`) |
| Default smoke | `python3 host/amber_board.py --smoke --count 20000` |
| Build | `make bitstream` from the area root |

: Table 0.0: Quick reference

---

## Diagrams

Every figure is a Graphviz source in `assets/graphviz/`, rendered to PNG by
`assets/graphviz/regenerate_all_graphviz.sh`. Edit the `.dot` and re-run the
script; never hand-edit a PNG.

| Figure | Source | Subject |
| --- | --- | --- |
| 1.1 | `amber_pair_genesys2_harness.dot` | Whole-unit harness: host → UART → bridge → caches → fabric → memory |
| 2.1 | `amber_address_map.dot` | Host-visible AXI4-Lite address space |
| 3.1 | `amber_uart_harness.dot` | Host → UART → AXIL → CSR decode → DUT |
| 3.2 | `amber_cycle_injector.dot` | Per-core stimulus engine internals |
| 3.3 | `amber_cache_top.dot` | `amber_top` internals: L1 core, AXI masters, monitor |
| 3.4 | `amber_pair_fabric.dot` | Snooping grant-pick fabric between caches and memory |
| 3.5 | `amber_tally_path.dot` | Cache MonBus streams → merge → ingest → tally |

: Table 0.1: The diagrams and their sources

All diagrams are as-built from the RTL in `rtl/` and the component cache RTL
referenced by the harness. No planned-only blocks are shown.

---

**Last Updated:** 2026-10-14
**Maintained By:** RTL Design Sherpa Project
