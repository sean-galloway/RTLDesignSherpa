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

# scoria DDR3/LPDDR3 Family Controller — Micro-Architecture Specification Index

## Overview

**Version:** 0.1 (first issue)
**Date:** 2026-10-07
**Status:** v0.1 — the HAS taken one level down, written against complete RTL.
scoria's RTL is complete and sim-verified (221 tests and 9 formal blocks
measured 2026-10-01; TASK-001's bounded advanced modes then landed with their
own FUB, macro, and top suites and the refresh proofs re-run). Unlike its
siblings' MAS books, this one was written after the fact: every page below
describes logic that already exists, and the RTL is the authority where the
two disagree.

The book covers every active block at signal level — interface tables,
cycle behavior, FSM policy, and the traps worth institutionalizing — plus
the DFI v3.1 pin-level table the HAS's interface chapter promises and the
signal contracts whose anchors a future kmap book will cite. The two dormant
FUBs (`powerdown_ctrl`, `dfi_signal_pack`) share one page; the verification-
side `cmd_history_checker` is described where it lives, in the testbench
tier, not in the design tree.

---

## Related Modules

Listed as paths, not links: the document build inlines every Markdown link in
this index, and these are companions, not chapters.

- **HAS** - `projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/docs/scoria_has/scoria_has_index.md` - the architecture this document takes one level down (v0.9)
- **PRD** - `projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/PRD.md` - product requirements
- **design requirements** - `projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/docs/design-requirements.md` - the delta analysis against JESD79-3F / JESD209-3C / DFI 3.1 that binds the HAS, and through it this book
- **Family docs** - `projects/components/mem-ctrl-ip/common-ip/docs/` - the shared-core design and family doctrine this book follows
- **pumice MAS** - `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/docs/pumice_mas/` - the book this one inherits its block mechanisms from
- **andesite MAS** - `projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/` - the downstream consumer: andesite's inherited-unchanged blocks are referenced to this book's pages, not rewritten
- **Family README** - `projects/components/mem-ctrl-ip/README.md` - family overview and per-IP status

---

## Navigation

**Note:** Every chapter below is one source file; the document build assembles
the spec from these links.

### Front Matter
- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview
- [Block Inventory](ch01_overview/01_block_inventory.md) — the full tree, three tiers, with layer assignments
- [What Changes vs pumice](ch01_overview/02_what_changes_vs_pumice.md) — the marking set, and what the MAS adds to it
- [Clocks, Reset, and Gearing](ch01_overview/03_clocks_reset_gearing.md) — the two controller domains and the width wrapper

### Chapter 2: Functional Blocks
- [AXI4 Layer](ch02_blocks/01_axi4_layer.md) — the host-side macro: splitter, intakes, CAMs, return ring
- [Scheduler Layer](ch02_blocks/02_scheduler_layer.md) — the command macro: arbiter, timers, refresh, ZQ, init
- [DFI Layer](ch02_blocks/03_dfi_layer.md) — the PHY-side macro: command path, serdes, aligner, CDC
- [AXI Burst Chopper](ch02_blocks/04_axi_burst_chopper.md) — FSM-free address-channel splitter
- [Write Splitter](ch02_blocks/05_wr_splitter.md) — WLAST reframing and zero-strobe padding
- [Write Intake](ch02_blocks/06_wr_intake.md) — skid buffers, decoded push, ragged-burst reject
- [Write Data CAM](ch02_blocks/07_wr_data_cam.md) — the write scheduling window, snarf, rate-matched drain
- [Read Intake](ch02_blocks/08_rd_intake.md) — the snarf probe, two-stage admit, order FIFO
- [Read Command CAM](ch02_blocks/09_rd_cmd_cam.md) — the read scheduling window
- [Read Return Ring](ch02_blocks/10_rd_return_ring.md) — AR-order tickets over in-flight read data
- [Address Mapper](ch02_blocks/11_addr_mapper.md) — byte offset to {rank, bank, row, col}
- [Page Policy](ch02_blocks/12_page_policy.md) — open-page hit/miss classification
- [Bank Timer](ch02_blocks/13_bank_timer.md) — per-bank JEDEC spacing
- [Global Timers](ch02_blocks/14_global_timers.md) — shared spacing counters, in the fixed form
- [Command Arbiter](ch02_blocks/15_cmd_arbiter.md) — FR-FCFS pick with maintenance preemption
- [Refresh Controller](ch02_blocks/16_refresh_ctrl.md) — all-bank/per-bank rotor, elastic and TCR modes
- [ZQ Controller](ch02_blocks/17_zq_ctrl.md) — periodic ZQCS as maintenance traffic
- [Init Sequencer](ch02_blocks/18_init_sequencer.md) — RESET#, MR2-MR3-MR1-MR0, ZQCL
- [Mode Register](ch02_blocks/19_mode_register.md) — the MR0-MR3 images
- [Write Leveling Interface](ch02_blocks/20_wrlvl_ifc.md) — the interface, not the search
- [DFI Command Path](ch02_blocks/21_dfi_cmd_path.md) — pacing rules on the command stream
- [DFI Command Formatter](ch02_blocks/22_dfi_cmd_formatter.md) — op to DFI pins, the DDR3 encodings
- [DFI Write Serializer](ch02_blocks/23_dfi_wr_serializer.md) — t_phy_wrlat delay line to wrdata_en
- [DFI Read Aligner](ch02_blocks/24_dfi_rd_aligner.md) — rddata_en windows and capture credits
- [DFI Clock-Domain Crossing](ch02_blocks/25_dfi_cdc.md) — the one ctl/phy boundary, FIFO-only
- [The Dormant Pair](ch02_blocks/26_dormant_powerdown_and_pack.md) — powerdown_ctrl and dfi_signal_pack, kept on purpose

### Chapter 3: Interfaces
- [AXI4 Slave and APB CSR at Pin Level](ch03_interfaces/01_axi4_apb_pins.md) — the host-side contract
- [DFI v3.1 Pin-Level Table](ch03_interfaces/02_dfi_v31_pins.md) — every HAS ch04 signal at pin level

### Chapter 4: Signal Contracts
- [Core Signal Contracts](ch04_contracts/01_core_contracts.md) — terms, invariants, the anchor map, formal cross-references
