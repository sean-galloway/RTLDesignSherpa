# Tasks

One place to see what is going on across every project in the repo. Each area
has its own directory with an `INDEX.md` and its lifecycle pages:

```
vault/Tasks/<area>/
  INDEX.md    rollup: counts + the active/open shortlist
  active.md   in progress right now
  open.md     accepted, ready to start
  deferred.md accepted, deliberately PARKED - waiting on a named external
              condition (a consumer, a decision, a dependency), not on effort
  closed.md   done (completed; kept for history, not deleted)
  dropped.md  ended without completing (abandoned / superseded / won't do)
```

`closed` and `dropped` are both terminal but they are not the same thing:
`closed` means the work got done, `dropped` means we decided not to do it (or
something else made it moot). Keeping them apart is what makes the history
honest — a dropped task should never read as an accomplishment.

`open` and `deferred` are both pending but they are not the same thing
either: `open` means someone could start it today; `deferred` means starting
it today would be wrong — its block must NAME the condition that un-defers
it, so the parking is a recorded decision rather than quiet neglect (added
2026-08-11, Sean; COMMON-007's hierarchical-arbitration slice was the
motivating case — shaped, elaborated, and twice deliberately parked pending
a consumer, which `open` kept misrepresenting as ready-to-start work).
Areas create `deferred.md` when they first need it; an absent file means
nothing is parked.

## Task IDs are permanent — never recycle one

Each area's `INDEX.md` carries a **`Next ID:`** line near the top. Take that
number, use it, bump the line. **Never reuse a number because its task
closed.** A task ID is a permanent handle: `[[PUMICE-011]]` in a handbook
note, a commit message, or a session memory has to keep meaning one thing
five months later.

This is enforced, because it already went wrong. `PUMICE-010` and
`PUMICE-011` each name TWO unrelated tasks (per-worker sim_builds vs a
single-knob address map; HISTCH1 accounting vs LPDDR2 MR init), and
`PUMICE-008` exists as both a dropped task and a live open one — so a bare
link to any of them is ambiguous and has to be disambiguated by date. Six
such collisions exist across four areas.

`bin/check_task_ids.py` runs from the pre-commit hook whenever a
`vault/Tasks/**.md` file is staged, and BLOCKS on:

* a duplicate ID within an area (the six historical ones are grandfathered
  in `KNOWN_COLLISIONS` — do NOT add to that list to silence a new clash,
  renumber the new task instead);
* a missing or stale `Next ID:` line (<= the highest ID already in use).

It also WARNS, without blocking, when a task in `closed.md`/`dropped.md`
still says `**Status:** open`. That one is a warning by design: deciding
whether such a task is "closed with a stale line" or "still open and
misfiled" needs someone who knows the work, and auto-flipping the text would
launder open work into the closed pile. Eleven of those exist today — see
[[COMMON-024]].

    bin/check_task_ids.py                 # check everything
    bin/check_task_ids.py --next pumice   # -> PUMICE-016


## The one rule

**All task tracking lives here.** Do not create a `TASKS.md`, `TODO.md`, or
`*_TODO.md` next to code — that scatter is exactly what this directory
replaces. A note-to-self about a file belongs in `vault/Tasks/<area>/open.md`, not in
a new file beside the file.

## Lifecycle

A task moves `open → active → closed` (done) — or to `dropped` if it ends
without being completed, or `open ↔ deferred` when the blocker is an external
condition rather than effort — by **cutting** its block from one page and
pasting it into the next. Never copy: a task must exist in exactly one state.
Keep the task's `**Status:**` line current with a date and, when dropping or
deferring, the one-line reason (for deferred: the condition that un-defers
it). New tasks get the next `TASK-NNN` (or area-appropriate) id and start in
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
| [math](math/INDEX.md) | **native** | rtl/math arithmetic library (MATH-001: bf16 rounding decision) | — (new 2026-07-29) |
| [stream](projects/components/dmas/stream/INDEX.md) | **started** | dmas/stream DMA (nested to mirror repo path) | TASK-056 migrated from TODO_RFC_StageE; [TASKS.md](../../projects/components/dmas/stream/TASKS.md) (v1.0 complete) still to fold in |
| [rapids](projects/components/dmas/rapids/INDEX.md) | **started** | dmas/rapids DMA (beats, nested to mirror repo) | TASK-057 regmap hygiene (ported from STREAM); [TASKS.md](../../projects/components/dmas/rapids/TASKS.md) + rapids_beats_mas/TODO still to fold in |
| [bridge](bridge/INDEX.md) | **started** | bridge crossbar generator | [TASKS.md](../../projects/components/bridge/TASKS.md) (still to fold in; area holds BRIDGE-001) |
| delta | pending | delta component | [TASKS.md](../../projects/components/delta/TASKS.md) |
| [reed-solomon](projects/components/reed-solomon/INDEX.md) | **migrated** | future R/S ECC component (intent only, no RTL yet; holds RS-001) | successor to dropped COMMON-009 |
| hive | pending | hive component | [TASKS.md](../../projects/components/hive/TASKS.md) |
| [RLB](RLB/INDEX.md) | **migrated** | retro legacy blocks (ioapic, pm_acpi, smbus, pit, hpet) | remaining pre-migration rtl/*/TODO items still to fold in |
| [pumice](pumice/INDEX.md) | **migrated** | pumice DDR2/LPDDR2 controller | — |
| [docs-review](docs-review/INDEX.md) | **migrated** | Kimi doc review + humanization | rtl-doc-review/REVIEW_TODOS.md (off-repo) |
| memory-controllers | pending | ddr3 / ddr4 (pumice migrated above) | ddr3-lpddr3, ddr4-lpddr4 TASKS.md |
| [nexysa7](nexysa7/INDEX.md) | **started** | board campaigns + characterization flows | NEXYS-001 (consistent flow Makefiles); timing_characterization/TASKS.md, cdc_counter_display CDC_DEMO_TODO still to fold in |
| formal | pending | formal proof backlog | [formal/FORMAL_TODO.md](../../formal/FORMAL_TODO.md) |
| [coverage](coverage/INDEX.md) | **migrated** | coverage rollout (COV-001: last 3 areas off base tests.mk) | val/COVERAGE_TODO.md (folded in + deleted 2026-08-09) |
| [tooling](tooling/INDEX.md) | **migrated** | repo tooling/scripts/process | TOOLING_TODO.md (folded in + deleted 2026-08-09: TOOL-013 closed, TOOL-014 open, kmap item into TOOLING-KMAP) |
| [site-audit](site-audit/INDEX.md) | **native** | site-wide audit umbrella: RTL correct, docs match, humanized, verification covers it | — (new 2026-07-28; subsumes DOCREV-009, folds in coverage/formal backlogs) |

`pending` rows still track work at the linked source file; they will migrate
into `vault/Tasks/<area>/` area by area (the migration itself is TOOL-001).
`amba` is the migrated reference shape.
