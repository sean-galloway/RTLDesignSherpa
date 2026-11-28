<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/compute-eng-ip/hive — tasks

**Next ID: TASK-002** — never recycle a number, even when its item closed.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-000** — hive Phase 1 RTL: finish the five blocks and close the CN-04 rotation issue
- **TASK-001** — HIVE-C on peregrine (`CORE_FLAVOR=peregrine`), VexRiscv retired; moved from riscv-ip/peregrine-rv32im TASK-004
