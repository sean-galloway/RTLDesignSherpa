<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# granite-ddr2-lpddr2 — issues

**Next ID: ISSUE-004** — never recycle a number, even when its item closed.

An anomaly, risk, or open question not yet diagnosed. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **ISSUE-003** -- the perf proxy is not run-to-run deterministic: the same
  build directory, seed and environment give cycle counts up to 0.4 percent
  apart (`col_ilv`), load-dependent; `incremental` identical, the rest moved by
  tens of cycles, which fits a start shifted against the refresh counter by a
  wall-clock-paced harness. Sets the floor under a one-run proxy delta. Filed
  2026-11-20 from memory-controllers MC-019. [open/ISSUE-003.md](open/ISSUE-003.md).

## Active

None.

## Closed

- **ISSUE-002** -- granite "does not come up on the Nexys at 100 MHz" (2026-11-09):
  the host ran the 75 MHz read-path pair (rddata_delay = t_rddata_en + 1) on a
  100 MHz board, where the a7ddrphy's data-vs-valid offset is 0; the 100 MHz
  pair had only ever been passed through TEST_* environment variables. The
  design was never implicated. Fixed in the host the same day (pair and JEDEC
  timings derived from BUILD_CLK_HZ, leveling falls back over the offsets);
  the committed 100 MHz bitstream passes init, write_read and the 128 MB
  memtest with no environment. Closed 2026-11-09.
  [closed/ISSUE-002.md](closed/ISSUE-002.md).

- **ISSUE-001** — same-id writes to different banks can return their B responses
  out of AXI order. Found by reading the store 2026-11-03; REPRODUCED 2026-11-05
  by the directed B-order test and re-filed as [BUG-001](../bug/closed/BUG-001.md).
  Closed 2026-11-06. [closed/ISSUE-001.md](closed/ISSUE-001.md).
