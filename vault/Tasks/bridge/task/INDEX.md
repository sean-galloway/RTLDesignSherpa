<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# bridge — tasks

**Next ID: TASK-013** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 7 | done (kept for history) |
| [dropped/](dropped/) | 4 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.
- **TASK-012** — bridge placement pass: 9 loose markdown files (generator design notes beside bin/, a bug write-up at the root)


## Dropped

- **TASK-009** — WB4 in the bridge is best effort -- the two known gaps stay open by decision
- **TASK-010** — Legacy TASK-012 — AXI burst optimization
- **TASK-011** — Legacy TASK-014 — APB3 to APB4 bridge
- **TASK-001** — trim method from `bridge/CLAUDE.md`; dropped, the file was already compliant and every row of its removal table was falsified by reading the text.

## Closed

- **TASK-002** — AMBA5 bridge support (AXI5 ports alongside AXI4)
- **TASK-003** — scrub the tests for completeness (bridge)
- **TASK-004** — AXI5-Lite and APB5 as MASTER protocols
- **TASK-005** — Master-unique transaction IDs: prepend the master index
- **TASK-006** — Legacy backlog carried over from projects/components/bridge/TASKS.md
- **TASK-007** — A native-AXI5 fabric
- **TASK-008** — Wishbone B4 as a bridge protocol, both sides
