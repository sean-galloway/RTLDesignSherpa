# Tasks

One place to see what is going on across every project in the repo. Each area
has its own directory with an `INDEX.md` and three lifecycle pages:

```
Tasks/<area>/
  INDEX.md    rollup: counts + the active/open shortlist
  active.md   in progress right now
  open.md     accepted, not started
  closed.md   done (completed; kept for history, not deleted)
  dropped.md  ended without completing (abandoned / superseded / won't do)
```

`closed` and `dropped` are both terminal but they are not the same thing:
`closed` means the work got done, `dropped` means we decided not to do it (or
something else made it moot). Keeping them apart is what makes the history
honest — a dropped task should never read as an accomplishment.

## The one rule

**All task tracking lives here.** Do not create a `TASKS.md`, `TODO.md`, or
`*_TODO.md` next to code — that scatter is exactly what this directory
replaces. A note-to-self about a file belongs in `Tasks/<area>/open.md`, not in
a new file beside the file.

## Lifecycle

A task moves `open → active → closed` (done) — or to `dropped` if it ends
without being completed — by **cutting** its block from one page and pasting it
into the next. Never copy: a task must exist in exactly one state. Keep the
task's `**Status:**` line current with a date and, when dropping, a one-line
reason. New tasks get the next `TASK-NNN` (or area-appropriate) id and start in
`open.md`.

## Reporting status

`Tasks/<area>/INDEX.md` is the human-readable rollup for that area; this file
is the cross-area map. When you finish or start work, update the area INDEX
counts so the one-place view stays true.

## Authority

[/GLOBAL_REQUIREMENTS.md](../GLOBAL_REQUIREMENTS.md) is the enforcement
authority and wins on any conflict. This directory tracks *work*; it does not
override requirements. Design/DV/FPGA *practice* lives in the
[handbook](../docs/handbook/INDEX.md).

## Areas

| Area | Status | Covers | Source (pre-migration) |
|---|---|---|---|
| [amba](amba/INDEX.md) | **migrated** | AXI/APB/AXIS, monitors, monbus | — |
| common | pending | rtl/common building blocks | [rtl/common/TASKS.md](../rtl/common/TASKS.md) |
| stream | pending | dmas/stream DMA | [TASKS.md](../projects/components/dmas/stream/TASKS.md), TODO_RFC_StageE |
| rapids | pending | dmas/rapids DMA (beats) | [TASKS.md](../projects/components/dmas/rapids/TASKS.md), rapids_beats_mas/TODO |
| bridge | pending | bridge crossbar generator | [TASKS.md](../projects/components/bridge/TASKS.md) |
| bch | pending | BCH ECC | [TASKS.md](../projects/components/bch/TASKS.md) |
| delta | pending | delta component | [TASKS.md](../projects/components/delta/TASKS.md) |
| hive | pending | hive component | [TASKS.md](../projects/components/hive/TASKS.md) |
| retro-legacy | pending | retro legacy blocks (ioapic, pm_acpi, smbus, pit, hpet) | [TASKS.md](../projects/components/retro_legacy_blocks/TASKS.md) + rtl/*/TODO |
| memory-controllers | pending | pumice / ddr3 / ddr4 | pumice, ddr3-lpddr3, ddr4-lpddr4 TASKS.md |
| nexysa7 | pending | board campaigns | timing_characterization/TASKS.md, cdc_counter_display CDC_DEMO_TODO |
| formal | pending | formal proof backlog | [formal/FORMAL_TODO.md](../formal/FORMAL_TODO.md) |
| coverage | pending | coverage backlog | [val/COVERAGE_TODO.md](../val/COVERAGE_TODO.md) |
| [tooling](tooling/INDEX.md) | **partial** | repo tooling/scripts/process | [TOOLING_TODO.md](../TOOLING_TODO.md) (backlog still there; area holds TOOL-001, the migration task) |

`pending` rows still track work at the linked source file; they will migrate
into `Tasks/<area>/` area by area. `amba` is the migrated reference shape.
