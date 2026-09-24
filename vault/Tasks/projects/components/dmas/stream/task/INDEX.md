<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/dmas/stream — tasks

**Next ID: TASK-012** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 4 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 7 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.
- **TASK-001** — finish the STREAM workbook so its maps prove the decisions
- **TASK-002** — gate the monitor regfile on a parameter (present + decoded)
- **TASK-003** — scrub the tests for completeness (stream)

## Active

- **TASK-004** — RFC Stage-E — in-core R/W datapath perf monitors (retire `axi_bus_meter`)

## Closed

- **TASK-005** — RLB blocks brought under the .rdl regen gate
- **TASK-006** — .rdl regen gate extended from 1 block to 9
- **TASK-007** — .rdl edits are gated against their generated artifacts
- **TASK-008** — perf FIFO is read non-empty, pairing asserted
- **TASK-009** — Signal contracts + K-maps for the significant STREAM signals (prove-by-construction)
- **TASK-010** — Kick STREAM from its own registers — delete the sideband kick ports and the APB kick block
- **TASK-011** — Configurable decompression in `monbus_tally_axil` (LOW priority, future)
