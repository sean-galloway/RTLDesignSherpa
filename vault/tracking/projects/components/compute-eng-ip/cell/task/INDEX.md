<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/compute-eng-ip/cell — tasks

**Next ID: TASK-003** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-001** — slice 2: cell_credit (per-source owed counters + 64-cycle timeout + boot credit/set ads, class-0 sink space) + cell_packetizer (batch-X/flush, FLUSH_DEST/FLUSH_TAG, strap check) per cell MAS v0.12 ch04
- **TASK-002** — slice 3: cell_exec_fsm (pop -> issue -> push loop driving alu_infer_top) + cell_mem_out write path + MonBus observer leaf; the bring-up driver gatling later sequences (owner ruling 2026-10-19)

## Active

## Closed
