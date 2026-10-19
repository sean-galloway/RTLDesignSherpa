<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# utility-ip/converters — tasks

**Next ID: TASK-007** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 5 | parked pending a named condition |

## Open

- **TASK-000** — template; reserved dummy, never a real item

## Active

(none)

## Closed

- **TASK-001** — AXI3 converters (axi4_to_axi3 / axi3_to_axi4) — CLOSED 2026-10-11: tracking scaffolding for GitHub issue #96

## Deferred

- **TASK-002** — APB3 to AXI4 wrapper over `apb4_to_axi4` — DEFERRED: retro-legacy customer bridge
- **TASK-003** — Tag-based chopped-burst overlap in `axi4_to_axi3_rd` — DEFERRED: un-defer if f2h throughput is chunk-sequencing bound
- **TASK-004** — AXI3 monitor-lite observer for seam measurements — DEFERRED: needs board-leg measurement requirement
- **TASK-005** — Write-data interleaving support in `axi3_to_axi4_wr` — DEFERRED: only if upstream master exercises interleaved WID
- **TASK-006** — Quartus synthesis-compatibility check of queue-based converter FSMs — DEFERRED: required before DE10 leg-bridge
