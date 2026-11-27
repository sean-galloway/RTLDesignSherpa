<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/cache-ip/common-ip — bugs

**Next ID: BUG-002** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

- **BUG-001** ([page](active/BUG-001.md)) — the Genesys2 cache-ip rigs' dual sweeps never overlap the two injectors: the host starts them with two UART writes >= 16 ms (1.6M cycles) apart, longer than any cell runs. Found 2026-11-26 (onyx bin 7 hot set); every board dual result is two single-injector runs back to back; fixed 2026-11-27 with a harness GO (one write starts both); closes on the board re-runs

## Closed

(none)
