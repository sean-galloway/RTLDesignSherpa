<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# nexysa7 — tasks

**Next ID: TASK-008** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 7 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-001** — Consistent Makefiles across the stream characterization flows
- **TASK-002** — Rehome NexysA7 under projects/fpga-systems + split Genesys2-specific flows
- **TASK-004** — ddr2-char harness needs TWO bridges, 8 bank-targeted masters each
- **TASK-005** — One name per quantity — BYTES_PER_AXI_BEAT / BYTES_PER_DFI_BEAT / DRAM_BL
- **TASK-006** — RISC-V SoC on pumice, running memory-controller stress benchmarks
- **TASK-007** — Move ddr2_char_framework into pumice/ (the NEXYS-003 residue)
- **TASK-000** — reserved template; copy the file, do not file against it.

## Closed

- **TASK-003** — Migrate the remaining char flows onto the shared projects/fpga-systems/bin layer
