<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# amba — issues

**Next ID: ISSUE-006** — never recycle a number, even when its item closed.

An observed problem that is not yet a diagnosed defect or a decided piece of work: an anomaly, a risk, an open question. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 4 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **ISSUE-005** — no harness exercises a master's multi-outstanding path,
  because the slave they all use serialises bursts (ISSUE-004). `r_outstanding`
  in `rs_axi4_write_engine` can only ever hold 0 or 1 against it, so
  `MAX_OUTSTANDING(4)` is untested logic in shipped IP. Options: a pipelining
  slave variant for DV, drive the engines from the AXI4 BFM instead, or
  constrain the IP to depth 1.

## Closed

- **ISSUE-004** — `sdpram_core` serialises bursts: one in flight per direction,
  so a master's outstanding depth is inert and ~2.0 (write) / ~1.6 (read)
  cycles land at each burst boundary. CLOSED 2026-10-01, no-action: a single
  tracker per direction is the documented architecture and this is a test
  memory behind four harnesses; the cost amortises with burst length (RS went
  16 -> 64 beats for 97.0%/98.5%). The real gap was that nothing SAID so --
  `sdpram_core.sv` now documents the contract and the measured cost, and the
  coverage consequence went to ISSUE-005.
- **ISSUE-001** — monbus_axil4_axil4_group misses 10 ns on Artix-7 through the s1_beats_to_limit CARRY4 chain (found synthesizing the amba/monitor-lite TASK-001 lite fixture) -- CLOSED 2026-09-28 (fixed): planner stage split, path +3.46 ns on the same fixture; the fixture's new worst path is the lite's (monitor-lite ISSUE-002)
- **ISSUE-003** — PKG-PAGES — CLOSED 2026-08-31: the premise did not survive measurement
- **ISSUE-002** — cam_clear inside the reporter's emission window strands the completion packet under aggressive gating. CLOSED 2026-09-27, no-action: clearing outside idle is illegal (Sean); contract written on the clear ports and in monitor_system_architecture.md.
