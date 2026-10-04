<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# coverage — issues

**Next ID: ISSUE-002** — never recycle a number, even when its item closed.

An observed problem that is not yet a diagnosed defect or a decided piece of work: an anomaly, a risk, an open question. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Closed

- **ISSUE-001** — coverage data collection unwired repo-wide: RESOLVED 2026-10-04
  into the structural fix -- conftest_base now injects Verilator's --coverage
  flags centrally by wrapping cocotb_test.simulator.run (validated on
  converters, previously 0/23 wired: 96.3% line coverage with no per-file
  changes), plus a ratchet: coverage-report with 0 merged .dat exits 1.
  Optional follow-up recorded: strip the redundant per-file wiring in the 5
  hand-wired areas

