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

# andesite DDR4/LPDDR4 Family Controller — Micro-Architecture Specification Index

## Overview

**Version:** 0.1 (draft)
**Date:** 2026-10-03
**Purpose:** Micro-architecture specification — the HAS taken one level down:
per-block signal tables, cycle behavior, FSM policy, and the contract anchors
the generated kmap book cites, for the andesite DDR4/LPDDR4 memory controller
(`projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/`).

The MAS documents the changed and new blocks in depth. Inherited-unchanged
blocks are **referenced to scoria's books, not rewritten** — where each one
lives, and why its internals are not reproduced here, is stated in Chapter 1.

---

## Related Modules

Listed as paths, not links: the document build inlines every Markdown link in
this index, and these are companions, not chapters.

- **HAS** - `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_has/andesite_has_index.md` - the architecture this document takes one level down
- **PRD** - `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/PRD.md` - product requirements (this tranche is docs-only; the PRD rewrite is follow-on work)
- **Family docs** - `projects/components/mem-ctrl-ip/docs/` - the shared-core design and doctrine this book follows
- **scoria HAS** - `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/docs/scoria_has/` - the reuse pool; referenced for every inherited block
- **Kmap book** - `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/kmaps/` - the generated command-encoding workbook (generator, xlsx, `generated/*.md`)
- **CLAUDE.md** - `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/CLAUDE.md` - area facts for a session working here

---

## Navigation

**Note:** Every chapter below is one source file; the document build assembles
the spec from these links. ch02 entries activate as their pages land (the
link-ratchet rule — links only ever point at committed files).

### Front Matter
- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview
- [Block Inventory](ch01_overview/01_block_inventory.md)
- [What Changes vs scoria](ch01_overview/02_what_changes_vs_scoria.md)

### Chapter 2: Functional Blocks
- [Command Formatter](ch02_blocks/01_cmd_formatter.md) — ACT_n/BG encodings, LPDDR4 CA path
- [Init Sequencer](ch02_blocks/02_init_sequencer.md) — reset, MR order, gear-down
- [Mode Register](ch02_blocks/03_mode_register.md) — MR0-MR6 field maps
- [Address Mapper](ch02_blocks/04_addr_mapper.md) — bank-group decode
- [Scheduler and Arbiter](ch02_blocks/05_scheduler.md) — L/S policy
- [Refresh Controller](ch02_blocks/06_refresh_ctrl.md) — FGR on the inherited base
- [ZQ Controller](ch02_blocks/07_zq_ctrl.md) — MPC path
- [ODT Controller](ch02_blocks/08_odt_ctrl.md) — RTT_NOM/WR/PARK
- [Training Interfaces](ch02_blocks/09_training.md) — wrlvl/rdlvl/ca_train
- [DFI Datapath Blocks](ch02_blocks/10_dfi_datapath.md) — DBI

### Chapter 3: Interfaces
- `ch03_interfaces/01_dfi40_pins.md` — DFI 4.0 Pin-Level Table

### Chapter 4: Signal Contracts
- `ch04_contracts/01_core_contracts.md` — Core Signal Contracts
