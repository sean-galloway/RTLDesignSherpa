<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/utility-ip/converters — tasks

**Next ID: TASK-005** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 4 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open



## Closed

- **TASK-004** — converters/README.md: three instantiation examples name parameters and ports the modules do not have -- CLOSED 2026-09-29: dnsize/apb4/peakrdl examples fixed against the headers; check_doc_examples 0, BASELINE 0
- **TASK-003** — converters placement pass: 2 loose analysis notes at the component root -- CLOSED 2026-09-29: DUAL_BUFFER note deleted (feature removed); APB analysis folded into MAS 3.4.12 and deleted
- **TASK-002** — scrub the tests for completeness (converters)
- **TASK-001** — upsize paths now support mid-wide-word INCR burst starts
