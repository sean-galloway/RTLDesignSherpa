# pumice — task rollup

**Next ID: PUMICE-051** — for the HISTORICAL flat pages only, and nothing
should need it: they take no new items. The highest still living here is 044,
but 045-050 were renamed into the lanes on 2026-09-24 and those numbers are
RETIRED, not free -- every commit message before that date still refers to
them.

**Each lane carries its own Next ID** — see the lane INDEXes
([task](task/INDEX.md), [bug](bug/INDEX.md), [issue](issue/INDEX.md)).
The flat pages below are historical and take no new items.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX.
**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Pick the lane before filing:

| Lane | For | Open |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | 8 |
| [bug/](bug/INDEX.md) | a defect with a reproduction | 1 |
| [issue/](issue/INDEX.md) | an anomaly/risk/question not yet diagnosed | 3 |

**IDs are per-lane sequences** (`TASK-001`, `BUG-001`, `ISSUE-001`), per the
convention. The open items were renamed on 2026-09-24 when they moved into the
lanes; the map below is kept because 176 references across 60 files, plus every
commit message before that date, use the old `PUMICE-NNN` names.

| Was | Is | | Was | Is |
|---|---|---|---|---|
| PUMICE-006 | [TASK-001](task/open/TASK-001.md) | | PUMICE-045 | [BUG-001](bug/open/BUG-001.md) |
| PUMICE-013 | [TASK-002](task/open/TASK-002.md) | | PUMICE-030 | [ISSUE-001](issue/open/ISSUE-001.md) |
| PUMICE-023 | [TASK-003](task/open/TASK-003.md) | | PUMICE-046 | [ISSUE-002](issue/open/ISSUE-002.md) |
| PUMICE-029 | [TASK-004](task/open/TASK-004.md) | | PUMICE-047 | [ISSUE-003](issue/closed/ISSUE-003.md) |
| PUMICE-034 | [TASK-005](task/open/TASK-005.md) | | PUMICE-048 | [ISSUE-004](issue/closed/ISSUE-004.md) |
| PUMICE-035 | [TASK-006](task/closed/TASK-006.md) | | | |
| PUMICE-039 | [TASK-007](task/open/TASK-007.md) | | | |
| PUMICE-049 | [TASK-008](task/open/TASK-008.md) | | | |
| PUMICE-CLEANUP | [TASK-009](task/open/TASK-009.md) | | | |

`PUMICE-NNN` numbers that are NOT in this table were already closed or dropped
and stay where they are, in the flat `closed.md` / `dropped.md` -- so an old
number still resolves to exactly one thing.

**The OPEN items moved into the lanes 2026-09-24.** `closed.md` and
`dropped.md` at this level still hold the flat historical entries -- that move
touched only open work, so history stayed where every existing link points.
See [the convention](../INDEX.md) for the full definitions.


DDR2/LPDDR2 memory controller (`projects/components/memory-controllers/pumice-ddr2-lpddr2/`).

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 0 | *(moved to the lanes)* |
| [closed](closed.md) | 31 |
| [dropped](dropped.md) | 5 |

## Active

(none running. The correctness backlog is NO LONGER empty: PUMICE-037 (P0) is
an open correctness defect found on the board 2026-09-14. The PUMICE-016
ACTIVE/"not urgent" contradiction that used to be noted here is gone: 016 was
investigated and DROPPED 2026-09-23.)

## Open shortlist

- **PUMICE-037** — P0, and the only correctness defect in this list.
  Concurrent read+write with the reader's gap at 8 or above returns wrong data
  and, when the two ranges overlap, leaves genuinely corrupted cells behind.
  Found on the board running PUMICE-036. Gap 0..7 is clean, so it does not
  invalidate the bandwidth work — but it must be reproduced in the
  char-framework sim to tell pumice from the harness read engine.
- **PUMICE-033** — one extra AXI ID bit takes the arbiter's pick cone from 13
  logic levels to 26 and 75 MHz from +1.100 to -6.602 ns. Measured at
  synthesis, so it is the netlist, not placement. Constrains pumice to a
  single master or to a fabric that keeps the index inside the master's own id
  width; the char harness works around it in the consumer.
- **TASK-005** — the paging predictors are 4,546 LUT / 3,341 FF built
  unconditionally for modes the board never selects, and they own most of the
  failing endpoints whenever a build stops closing. Gating them trades away
  "one bitstream characterizes every policy" — Sean's call.
- **TASK-006** — the bus meters say a cycle was not productive, not why, so a
  bandwidth report cannot attribute the missing percent to refresh, activate,
  turnaround or first-transaction latency. Needs a few scheduler counters.

- **TASK-002** — characterize + tune the modes (the big one: sweeps in sim
  and on the board, recommended defaults per workload family). Wants 008
  first for the reason above. NO LONGER gated on observer adoption:
  PUMICE-016 was dropped 2026-09-23 and the AMBA-HISTCH1 accounting error it
  was supposed to dodge is fixed at source, measured clean (multiid 64/64).

- **TASK-001** — mechanisms COMPLETE 2026-08-27, all three axes, every
  mode off by default and mutation-proven. Parked; reopens only if 013
  reports a gap.
- **TASK-009** — doc placement + filelist consistency. P2 hygiene.
- **PUMICE-KMAP** — blocked on [[TOOLING-KMAP]], whose SCOPE CHANGED
  2026-08-28: the deliverable is now a three-part CONTRACT TABLE (term list
  -> invariants -> decision table), not a Gray grid. See
  [[signal-contracts-and-kmaps]]. Not startable from the pumice side until
  the emitter learns the new form.

## Task-ID reuse — RESOLVED 2026-09-06

`closed.md` held an ORIGINAL series (PUMICE-009 gearing, -010 addr-map single
knob, -011 LPDDR2 MR init, -012 LPDDR2 write-AP dropped writes). A LATER series
had reused three of those numbers for unrelated work. All three are now
renumbered to unique IDs (never recycled), with every reference updated:

- "PUMICE-012" (structure trackers) -> **PUMICE-015** (2026-08-28)
- "PUMICE-010" (per-worker sim_builds / seed echo) -> **PUMICE-019** (2026-09-06)
- "PUMICE-011" (AMBA-HISTCH1 + multiid hist accounting) -> **PUMICE-020** (2026-09-06)

Code, DV, docs and session memory were updated in the same pass, and the pumice
grandfathers were removed from `bin/check_task_ids.py`. A bare `[[PUMICE-010]]`
/ `[[PUMICE-011]]` now unambiguously means the ORIGINAL addr-map / LPDDR2-init
task. The 008 observer renumber (-> PUMICE-016) stands; the only remaining
PUMICE-008 is the dropped deskew task. Do not recycle an ID.

## Reading order for someone picking this up

The correctness backlog is EMPTY — PUMICE-001 closed 2026-08-25 (board
re-validated, matrix 65/70 data-clean, soak 0/15). Everything open is
cleanup or a gated feature. The July task cluster is fully resolved:
PUMICE-002 (stale hand-packed CSR write), PUMICE-003 (bank_lsb=0 striping,
fixed fcafc435), and PUMICE-004 (refresh collision, fixed 38c8ae63 with the
detector armed + mutation-proven 2026-08-24) all closed — the ledger had gone
stale against landed fixes FOUR times (002/003/004/007), so measure before debugging. TASK-001's
entry gate is now the PUMICE-001 board trip + a tiny-tREFI re-soak on the
08-16 bitstream.

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.
