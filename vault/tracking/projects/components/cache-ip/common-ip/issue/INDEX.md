<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/cache-ip/common-ip — issues

**Next ID: ISSUE-002** — never recycle a number, even when its item closed.

An anomaly, risk, or open question not yet diagnosed: it resolves INTO a bug, a task, or a recorded no-action.

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

- **ISSUE-001** ([page](closed/ISSUE-001.md)) -- the Vivado flow defines no `XILINX` macro; every `ifdef XILINX (* ram_style *)` was dead on the board. Filed 2026-11-08. **Closed 2026-11-10:** the guards are gone and the attributes are unconditional in all 25 files repo-wide; measured on four rigs and both cache-ip boards.
