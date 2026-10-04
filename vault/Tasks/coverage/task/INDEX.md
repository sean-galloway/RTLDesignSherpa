<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# coverage — tasks

**Next ID: TASK-004** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 1 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Closed

- **TASK-002** — CLOSED 2026-10-04: the Makefile migration had already
  landed (71fe1ec5d, 76c6ff82b) but verification showed coverage data was
  never produced — the Verilator --coverage flags were unwired. Wired
  get_coverage_compile_args() into all 32 test runners of the three named
  areas (apbx-xbar 6, retro_legacy 16, asic-trials 10); clean-build
  COVERAGE=1 smokes now report Line 90.6/90.2/100.0%. Repo-wide remainder
  (converters, rapids, scoria, rs, stream, bch, ...) filed as ISSUE-001

- **TASK-001** — Coverage infrastructure consolidation (historical record)

## Dropped

- **TASK-003** — delta has five RTL files, no tests at all, and two copies of one module
