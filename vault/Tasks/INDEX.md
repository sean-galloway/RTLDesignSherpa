# Tasks

One place to see what is going on across every project in the repo. Each area
has its own directory with an `INDEX.md` and three lifecycle pages:

```
vault/Tasks/<area>/
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
replaces. A note-to-self about a file belongs in `vault/Tasks/<area>/open.md`, not in
a new file beside the file.

## Lifecycle

A task moves `open → active → closed` (done) — or to `dropped` if it ends
without being completed — by **cutting** its block from one page and pasting it
into the next. Never copy: a task must exist in exactly one state. Keep the
task's `**Status:**` line current with a date and, when dropping, a one-line
reason. New tasks get the next `TASK-NNN` (or area-appropriate) id and start in
`open.md`.

## Reporting status

`vault/Tasks/<area>/INDEX.md` is the human-readable rollup for that area; this file
is the cross-area map. When you finish or start work, update the area INDEX
counts so the one-place view stays true.

## Authority

[/GLOBAL_REQUIREMENTS.md](../../GLOBAL_REQUIREMENTS.md) is the enforcement
authority and wins on any conflict. This directory tracks *work*; it does not
override requirements. Design/DV/FPGA *practice* lives in the
[handbook](../handbook/INDEX.md).

## Sequencing (Sean, 2026-07-24)

**RTL area first, projects second.** The current structural cleanup -- doc
placement, the CDC reorg, filelist consistency -- is finished across `rtl/`
before any of it touches `projects/`. Tasks scoped to `projects/` wait behind
the RTL-area work. And within a running Kimi review, nothing that changes the
reviewed tree starts until the review is back and integrated.

## Areas

| Area | Status | Covers | Source (pre-migration) |
|---|---|---|---|
| [amba](amba/INDEX.md) | **migrated** | AXI/APB/AXIS, monitors, monbus | — |
| [common](common/INDEX.md) | **migrated** | rtl/common building blocks | — |
| [stream](projects/components/dmas/stream/INDEX.md) | **started** | dmas/stream DMA (nested to mirror repo path) | TASK-056 migrated from TODO_RFC_StageE; [TASKS.md](../../projects/components/dmas/stream/TASKS.md) (v1.0 complete) still to fold in |
| [rapids](projects/components/dmas/rapids/INDEX.md) | **started** | dmas/rapids DMA (beats, nested to mirror repo) | TASK-057 regmap hygiene (ported from STREAM); [TASKS.md](../../projects/components/dmas/rapids/TASKS.md) + rapids_beats_mas/TODO still to fold in |
| [bridge](bridge/INDEX.md) | **started** | bridge crossbar generator | [TASKS.md](../../projects/components/bridge/TASKS.md) (still to fold in; area holds BRIDGE-001) |
| delta | pending | delta component | [TASKS.md](../../projects/components/delta/TASKS.md) |
| hive | pending | hive component | [TASKS.md](../../projects/components/hive/TASKS.md) |
| [RLB](RLB/INDEX.md) | **migrated** | retro legacy blocks (ioapic, pm_acpi, smbus, pit, hpet) | remaining pre-migration rtl/*/TODO items still to fold in |
| [pumice](pumice/INDEX.md) | **migrated** | pumice DDR2/LPDDR2 controller | — |
| [docs-review](docs-review/INDEX.md) | **migrated** | Kimi doc review + humanization | rtl-doc-review/REVIEW_TODOS.md (off-repo) |
| memory-controllers | pending | ddr3 / ddr4 (pumice migrated above) | ddr3-lpddr3, ddr4-lpddr4 TASKS.md |
| nexysa7 | pending | board campaigns | timing_characterization/TASKS.md, cdc_counter_display CDC_DEMO_TODO |
| formal | pending | formal proof backlog | [formal/FORMAL_TODO.md](../../formal/FORMAL_TODO.md) |
| coverage | pending | coverage backlog | [val/COVERAGE_TODO.md](../../val/COVERAGE_TODO.md) |
| [tooling](tooling/INDEX.md) | **migrated** | repo tooling/scripts/process | [TOOLING_TODO.md](../../TOOLING_TODO.md) (historical backlog migrates via TOOL-001) |
| [site-audit](site-audit/INDEX.md) | **native** | site-wide audit umbrella: RTL correct, docs match, humanized, verification covers it | — (new 2026-07-28; subsumes DOCREV-009, folds in coverage/formal backlogs) |

`pending` rows still track work at the linked source file; they will migrate
into `vault/Tasks/<area>/` area by area (the migration itself is TOOL-001).
`amba` is the migrated reference shape.
