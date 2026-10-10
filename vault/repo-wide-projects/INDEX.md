---
title: Repo-wide projects
summary: One knowledge note per RTL subsystem and per project, mirroring the repo tree.
---

# Repo-wide projects

A note per area, laid out to mirror the repo so the path you know in the code is
the path you know here. `rtl/amba` in the tree is `rtl/amba` in the vault.

This is **area context**, and it is the third of three things the vault holds:

| Vault area | Holds | Answers |
|---|---|---|
| [handbook](../handbook/INDEX.md) | method and practice | "how do we do X here?" |
| [Tasks](../Tasks/INDEX.md) | work items, with lifecycle | "what is in flight?" |
| repo-wide-projects (this) | per-area durable context | "why is *this block* like this?" |

Keep them apart. A rule that applies everywhere is a handbook note. A thing to
do is a task. Why `pumice`'s arbiter guards a bank for two cycles is an area
note — it belongs to that block and nowhere else.

## rtl/

- [rtl/amba](rtl/amba/INDEX.md) — AXI4/AXI5, APB, AXIS, monitors, monbus
  - amba sub-areas at v1.0 (2026-10-06), each tracked with the post-1.0 issue rule: `apb4`, `apb5`, `axi4`, `axi5`, `axil4`, `axil5`, `axis4`, `axis5`, `gaxi`, `monitor`, `shared`, `wb4`
  - `ace` is **not** at v1.0; it is deliberately excluded from this declaration
- [rtl/common](rtl/common/INDEX.md) — counters, arbiters, FIFOs, CDC, data integrity; v1.0 (2026-10-06)
- [rtl/cdc](rtl/cdc/INDEX.md) — synchronizers, handshake closures, async FIFO, gray counters; v1.0 (2026-10-06)
- [rtl/math](rtl/math/INDEX.md) — adders, multipliers, dividers; v1.0 (2026-10-06)
- `rtl/make` — shared area-makefile plumbing (`area.mk`), not a subsystem; no note by design

## projects/components/

- [apbx-xbar](projects/components/fabric-gen-ip/apbx-xbar/INDEX.md) — v1.0 (2026-10-06)
- `cache-ip` — amber-mesi-l1, jet-mesi-l1, onyx-ace-ccu coherent-cache studies; area exists in the repo, no context note written yet
- [bridge](projects/components/fabric-gen-ip/bridge/INDEX.md) — generated crossbar; v1.0 (2026-10-06)
- [converters](projects/components/utility-ip/converters/INDEX.md)
- [delta](projects/components/noc-ip/delta/INDEX.md)
- `ecc-ip/bch` — v1.0 (2026-10-06); area exists in the repo, no context note written yet
- `ecc-ip/reed-solomon` — v1.0 (2026-10-06); area exists in the repo, no context note written yet
- [dma-ip/rapids](projects/components/dma-ip/rapids/INDEX.md) — beats rearchitecture; v1.0 (2026-10-06)
- [dma-ip/stream](projects/components/dma-ip/stream/INDEX.md) — reference DV implementation; v1.0 (2026-10-06)
- [hive](projects/components/compute-eng-ip/hive/INDEX.md)
- [mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2](projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/INDEX.md) — board-validated
- [mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3](projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/INDEX.md)
- [andesite-ddr4-lpddr4](projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/INDEX.md)
- [misc](projects/components/utility-ip/misc/INDEX.md)
- [retro_legacy_blocks](projects/components/retro_legacy_blocks/INDEX.md) — PIC, PIT, HPET, IOAPIC, SMBus, UART, RTC, GPIO, PM/ACPI; v1.0 (2026-10-06)

## projects/fpga-systems/

- [bin](projects/fpga-systems/bin/INDEX.md) — the shared board + UART layer (uart_link, uart_axi_bridge, boards registry, sequence runner)
- [boards](projects/fpga-systems/boards/INDEX.md) — board definitions (nexys_a7_100t)
- `de25-nano/mem-ctrl-ip/andesite` — andesite on the DE25-Nano board; area exists in the repo, no context note written yet
- `docs` — fpga-systems MAS book (`FPGA_SYSTEMS_MAS_v1.0.pdf`); documentation area, no context note by design
- [rtl/mem_char_framework](projects/fpga-systems/rtl/INDEX.md) — shared memory-characterization harness used by pumice and scoria
- `Genesys2/ecc-ip/bch` — BCH board harness; v1.0 (2026-10-06); area exists in the repo, no context note written yet
- `Genesys2/ecc-ip/reed-solomon` — RS board harness; v1.0 (2026-10-06); area exists in the repo, no context note written yet
- `Genesys2/dma-ip/rapids` — RAPIDS board harness; v1.0 (2026-10-06); area exists in the repo, no context note written yet
- [Genesys2/dma-ip/rapids_beats](projects/fpga-systems/Genesys2/dma-ip/rapids_beats/INDEX.md) — RAPIDS board characterization; v1.0 (2026-10-06)
- `Genesys2/mem-ctrl-ip/scoria` — scoria board harness (LiteDRAM build); area exists in the repo, no context note written yet
- `Genesys2/dma-ip/stream` — stream board harness; v1.0 (2026-10-06); area exists in the repo, no context note written yet
- [NexysA7/misc-ip/cdc_counter_display](projects/fpga-systems/NexysA7/misc-ip/cdc_counter_display/INDEX.md) — CDC demo on Nexys A7
- [NexysA7/mem-ctrl-ip/pumice/ddr2-characterization](projects/fpga-systems/NexysA7/mem-ctrl-ip/pumice/ddr2-characterization/INDEX.md) — DDR2 board characterization campaign

## projects/asic-trials/

- [timing_characterization](projects/asic-trials/timing_characterization/INDEX.md)

## Adding an area

Mirror the repo path and add an `INDEX.md`. Do not invent a structure that the
code does not have — the whole value is that the two paths match.

**When the repo moves, move the note with it.** `projects/` was reorganised
under `fpga-systems/` and `asic-trials/`, and four notes stayed at their old
locations while their own `title:`, `repo:` and `Code:` links had already been
updated to the new paths — so every one of them described a path it did not sit
at. Nothing flagged it: the links still resolved, and the broken-link gate has
no opinion about a page filed in the wrong place. A mirror that quietly stops
mirroring is the exact failure this layout exists to prevent. Moving a note also
changes its depth, so re-count the `../` prefixes on the `Code:`, handbook and
Tasks links when you move one.
