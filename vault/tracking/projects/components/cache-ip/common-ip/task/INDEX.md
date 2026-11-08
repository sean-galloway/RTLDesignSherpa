<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/cache-ip/common-ip — tasks

**Next ID: TASK-002** — never recycle a number, even when its item closed.

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
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

(none)

## Closed

(none)

- **TASK-001** ([page](closed/TASK-001.md)) — FPGA microarchitecture review of the shared L1 core, amber and jet (2026-11-06..08): per-way tag array, LUTRAM LRU, block-RAM sync-read data array, beat-addressed reset-free payload stores, reset_sync REPLICATED_OUT. amber 98,033 -> 17,185 LUT, jet 108,429 -> 21,700 LUT, both at 100 MHz with margin, cycle-identical to the RTL. Closed 2026-11-08.
