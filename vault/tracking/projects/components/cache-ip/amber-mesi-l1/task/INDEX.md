<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/amber-mesi-l1 — tasks

**Next ID: TASK-002** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a
cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

(none)

## Closed

- **TASK-001** — amber_pair_harness on `monbus_axil4_group_1wr` (the
  write-only group swap): drain tie-offs deleted, error window strapped to a
  dead null window, tally ingest unchanged. DV green modulo the pre-existing
  BUG-003 seed flake (2026-10-25)
