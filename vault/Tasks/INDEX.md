# Tasks

One place to see what is going on across every project in the repo. Each area
has its own directory with an `INDEX.md` and its lifecycle pages:

```
vault/Tasks/<area>/
  INDEX.md    rollup: counts + the lane pointers
  task/       planned work          INDEX.md + open/active/closed/dropped
  bug/        defects               INDEX.md + open/active/closed/dropped
  issue/      undiagnosed problems  INDEX.md + open/active/closed/dropped

  # LEGACY task lane -- frozen, close out in place, do not add to:
  active.md   in progress right now
  open.md     accepted, ready to start
  deferred.md accepted, deliberately PARKED - waiting on a named external
              condition (a consumer, a decision, a dependency), not on effort
  closed.md   done (completed; kept for history, not deleted)
  dropped.md  ended without completing (abandoned / superseded / won't do)
```

## Three lanes: task, bug, issue (Sean, 2026-09-24)

Everything used to be a "task", which made the page useless for the question
people actually ask -- *is this broken, or is this work we chose?* The lanes
split that:

| Lane | What it is | Test for "does it belong here?" |
|---|---|---|
| **task** | planned work we decided to do: a feature, a refactor, a migration, a cleanup | It starts from INTENT. Nothing is wrong; we want something different. |
| **bug** | a defect with a reproduction | You can state the expected behaviour AND the observed one. If you cannot say what correct looks like, it is not a bug. |
| **issue** | an anomaly, risk, or open question not yet diagnosed | It RESOLVES INTO a bug, a task, or a recorded no-action. It is not a place to park things forever -- that is `deferred`. |

An issue that turns out to be a defect is closed as an issue and re-filed as a
bug, with each naming the other. Keeping the trail is the point: "we looked at
this and it was X" is worth more than a silently retyped entry.

**`known_issues/` beside the code is NOT this.** Those directories
(`rtl/amba/KNOWN_ISSUES/`, `projects/components/<name>/known_issues/`) are a
WON'T-FIX ledger -- defects we have accepted and are living with, recorded so
the next person does not re-diagnose them. A vault `issue` is something we
intend to resolve. If a vault issue ends in "we accept this", it closes here
and gets written up there.

### IDs

Each lane has its own sequence, and **the area is still the namespace** -- so
`BUG-001` in pumice and `BUG-001` in amba are different bugs, exactly as
`TASK-080` already names two different tasks in two areas. Do not invent
compound prefixes: `PUMICE-BUG-001` does not parse (the checker reads the
second hyphen as a separator and every bug collapses to one ID).

**`-000` is a reserved dummy in every lane of every area.** It is the template
entry and is never a real item. It exists so a lane page carries a recognised
ID from the day it is created: an empty page and a page the checker cannot
parse look identical in a passing run, and this repo has shipped that failure
more than once. Real items start at `-001`.

    bin/check_task_ids.py --next pumice/bug     # -> BUG-001
    bin/check_task_ids.py --area tooling/issue  # check one lane

The checker reports an area by its path under `vault/Tasks/` (`pumice/bug`,
not `bug`), because 18 directories now share each lane name.

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

## The AREA is the namespace — a task lives in its own component's files (Sean, 2026-09-14)

**A pumice task goes in `vault/Tasks/pumice/`. A converter task goes in the
converters area. Same for every component.** Not wherever it happened to be
found, and not in whichever area the person filing it had open.

**The same number in two areas is EXPECTED, not a collision.** `TASK-080` names
one task in amba and a different one in STREAM, and that is fine — the area
tells them apart. Do not renumber across areas, and do not invent per-area
prefixes to dodge it.

**When citing a task outside its own file, name the area:**

```
Pumice TASK-037          amba TASK-073          STREAM TASK-080
```

Duplicates only matter WITHIN an area, and `bin/check_task_ids.py` blocks on
exactly that case.

**The practical consequence, learned the hard way.** A task filed in the wrong
area is invisible to anyone reading the component it belongs to. `CONV-001`
("dwidth converter split-fold assumes in-order B across IDs") sat in
`amba/open.md` — an open RTL defect that nobody working on the converters would
ever have seen. `CDC-FORMAL-STALE` sat there too, filed under amba because CDC
used to live there before `AMBA-CDC-REORG` moved it to `rtl/cdc`; the task never
followed the code. Both moved 2026-09-14.

Moving one can expose a REAL duplicate, and that is the system working: the
converter task was `CONV-001` in amba where the number was free, and landed on
the converters' own `CONV-001`. It was renumbered to `CONV-010`, because inside
one area a number means one thing. amba still holds several misfiled CLOSED
entries (BRIDGE-, TOOL-, NEXYSA7-, FORMAL-) — lower value to move, but they are
the same mistake.

## Task IDs are permanent — never recycle one

Each area's `INDEX.md` carries a **`Next ID:`** line near the top. Take that
number, use it, bump the line. **Never reuse a number because its task
closed.** A task ID is a permanent handle: `[[PUMICE-011]]` in a handbook
note, a commit message, or a session memory has to keep meaning one thing
five months later.

This is enforced, because it already went wrong. `PUMICE-010` and
`PUMICE-011` each ONCE named TWO unrelated tasks (per-worker sim_builds vs a
single-knob address map; HISTCH1 accounting vs LPDDR2 MR init) — the reused
pair was renumbered to `PUMICE-019` / `PUMICE-020` on 2026-09-06. Also,
`PUMICE-008` DID exist as both a dropped task and a live open one; the live
one was renumbered to PUMICE-016 on 2026-08-28. The remaining collisions are
historical (both sides terminal), so a bare link to them must be
disambiguated by date. Five such collisions remain across four areas.

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
launder open work into the closed pile. Eleven of those exist today — see [[AUDIT-002]].

    bin/check_task_ids.py                 # check everything
    bin/check_task_ids.py --next pumice   # -> PUMICE-016


## Heading shape — every task is `## <ID>`, uniformly (Sean, 2026-09-14)

**A task entry is an `##` heading, and the ID is the heading.** Not `###`, not
a bare number, not a mixture:

```
## TASK-078: scrub the tests for completeness (amba)
## PUMICE-037 — concurrent read+write with reader gap >= 8 corrupts cells
```

**A subtask extends the parent's ID with a two-digit suffix, still at `##`:**

```
## TASK-078: scrub the tests for completeness (amba)
## TASK-078.01: the val/amba half
## TASK-078.02: the components half
```

Hierarchy lives in the ID, never in the heading level. That is what makes the
pages uniform and countable.

**Anything inside a task body is `###` or deeper** — "Root cause", "Residual",
"Definition of done" are prose sections, not subtasks, and must never be
promoted to `##`.

Numbers are assigned **per area and are stable once assigned**: a task keeps
its ID when it moves between `open.md`, `active.md` and `closed.md`, so each
page's sequence has gaps. That is correct and expected — the ID is a handle,
not a position.

**Why this is a rule and not a preference.** Before 2026-09-14 entries sat at
BOTH `##` and `###` across every area — 136 at one level, 103 at the other.
Any count that assumed a single level was wrong, so the rollup numbers in the
area INDEX pages drifted in both directions and nobody noticed. Worse, a scan
that read only `##` silently missed nine open items in amba alone, several of
them real defects, which is exactly how a "what is open?" answer came back
with about half the truth. 102 headings were promoted to `##` that day; the
count is now 235 at `##` and zero at `###`.

Note the 24 slug-style IDs that predate this (`AMBA-CDC-REORG`,
`BRIDGE-NEXYSA7-REGEN`, `PUMICE-CLEANUP`, ...). They are uniform in SHAPE now
— `## <ID>` like everything else — but they are not numeric, so they cannot
take a `.01` subtask suffix meaningfully. Renaming them would break 134
`[[ID]]` wikilinks plus commit history, so they stay until someone decides
otherwise. New IDs should be numeric.

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
| [cdc](cdc/INDEX.md) | **native** | rtl/cdc clock-domain crossing (gray/binary converters, async FIFOs, pointer synchronisers) | — (new 2026-09-04) |
| [misc](projects/components/misc/INDEX.md) | **native** | shared odds and ends: AXI4 interface observers, tally/slvmon register blocks, dma_address_gen | — (new 2026-09-04) |
| [stream](projects/components/dmas/stream/INDEX.md) | **started** | dmas/stream DMA (nested to mirror repo path) | TASK-056 migrated from TODO_RFC_StageE; [TASKS.md](../../projects/components/dmas/stream/TASKS.md) (v1.0 complete) still to fold in |
| [rapids](projects/components/dmas/rapids/INDEX.md) | **started** | dmas/rapids DMA (beats, nested to mirror repo) | TASK-057 regmap hygiene (ported from STREAM); [TASKS.md](../../projects/components/dmas/rapids/TASKS.md) + rapids_beats_mas/TODO still to fold in |
| [bridge](bridge/INDEX.md) | **migrated** | bridge crossbar generator | TASKS.md folded in 2026-09-10 (ledger in closed.md); nothing open since 2026-09-13 (BRIDGE-017 and 018 closed, WB4 gaps dropped by decision) |
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
