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
- [rtl/common](rtl/common/INDEX.md) — counters, arbiters, FIFOs, CDC, data integrity
- [rtl/math](rtl/math/INDEX.md) — adders, multipliers, dividers

## projects/components/

- [apbx-xbar](projects/components/apbx-xbar/INDEX.md)
- [bridge](projects/components/bridge/INDEX.md) — generated crossbar
- [converters](projects/components/converters/INDEX.md)
- [delta](projects/components/delta/INDEX.md)
- [dmas/rapids](projects/components/dmas/rapids/INDEX.md) — beats rearchitecture
- [dmas/stream](projects/components/dmas/stream/INDEX.md) — reference DV implementation
- [hive](projects/components/hive/INDEX.md)
- [memory-controllers/pumice-ddr2-lpddr2](projects/components/memory-controllers/pumice-ddr2-lpddr2/INDEX.md) — board-validated
- [memory-controllers/ddr3-lpddr3](projects/components/memory-controllers/ddr3-lpddr3/INDEX.md)
- [memory-controllers/ddr4-lpddr4](projects/components/memory-controllers/ddr4-lpddr4/INDEX.md)
- [misc](projects/components/misc/INDEX.md)
- [retro_legacy_blocks](projects/components/retro_legacy_blocks/INDEX.md) — PIC, PIT, HPET, IOAPIC, SMBus, UART, RTC, GPIO, PM/ACPI

## projects/fpga-systems/

- [boards](projects/fpga-systems/boards/INDEX.md) — board definitions (nexys_a7_100t)
- [Genesys2/rapids_characterization](projects/fpga-systems/Genesys2/rapids_characterization/INDEX.md) — RAPIDS board characterization
- `Genesys2/stream` — area exists in the repo, no context note written yet
- [NexysA7/cdc_counter_display](projects/fpga-systems/NexysA7/cdc_counter_display/INDEX.md) — CDC demo on Nexys A7
- [NexysA7/pumice/ddr2-characterization](projects/fpga-systems/NexysA7/pumice/ddr2-characterization/INDEX.md) — DDR2 board characterization campaign

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
