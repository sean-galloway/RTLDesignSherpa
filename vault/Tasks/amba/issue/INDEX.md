<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# amba — issues

**Next ID: ISSUE-005** — never recycle a number, even when its item closed.

An observed problem that is not yet a diagnosed defect or a decided piece of work: an anomaly, a risk, an open question. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **ISSUE-004** — `sdpram_core` serialises bursts: `awready` waits on
  `!r_wr_active && !r_b_pending` and `arready` on `!r_rd_active`, so one burst
  is in flight at a time and a master's `MAX_OUTSTANDING > 1` is inert. Measured
  ~2.0 cycles per write burst (backpressure) and ~1.6 per read burst
  (starvation) on the RS loop harness; affects every consumer of
  `sdpram_slave_axi4_axi4`, including the stream, rapids and rapids_beats
  harnesses. Not yet decided whether it is a defect or deliberate for a test
  memory.

## Closed

- **ISSUE-001** — monbus_axil4_axil4_group misses 10 ns on Artix-7 through the s1_beats_to_limit CARRY4 chain (found synthesizing the amba/monitor-lite TASK-001 lite fixture) -- CLOSED 2026-09-28 (fixed): planner stage split, path +3.46 ns on the same fixture; the fixture's new worst path is the lite's (monitor-lite ISSUE-002)
- **ISSUE-003** — PKG-PAGES — CLOSED 2026-08-31: the premise did not survive measurement
- **ISSUE-002** — cam_clear inside the reporter's emission window strands the completion packet under aggressive gating. CLOSED 2026-09-27, no-action: clearing outside idle is illegal (Sean); contract written on the clear ports and in monitor_system_architecture.md.
