<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# amba/monitor-lite — issues

**Next ID: ISSUE-004** — never recycle a number, even when its item closed.

An observed problem that is not yet a diagnosed defect or a decided piece of work: an anomaly, a risk, an open question. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open



## Closed

- **ISSUE-003** — axis_monitor_lite decides events and counts drops in one cycle: misses 10 ns on Artix-7 by 1.18 ns (16 levels into r_dropped) -- CLOSED 2026-09-29 (fixed): event stage added; Artix-7 -1.18 -> +1.65 ns, Kintex-7 +1.87 ns, 6 levels
- **ISSUE-002** — the latency-threshold event reaches r_dropped combinationally from the R handshake: 11.7 ns, 21 levels on Artix-7 at 10 ns -- CLOSED 2026-09-28 (fixed): compare moved a stage later with a held payload; the Artix-7 lite fixture meets, +0.443 ns
- **ISSUE-001** — which monitored instances should switch to the lite (all of them did; measured and validated on silicon, TASK-001 section 17)
