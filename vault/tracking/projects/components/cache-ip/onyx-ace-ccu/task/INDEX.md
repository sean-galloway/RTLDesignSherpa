<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/cache-ip/onyx-ace-ccu — tasks

**Next ID: TASK-002** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

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

- **TASK-001** ([page](active/TASK-001.md)) — onyx v1, the ACE coherency unit per the D rulings (PRD v0.7, 2026-11-20): N-port culsans-shape CCU decoding RNSD/RU/CU/WB/Evict, broadcast snoop, tagged gather from a transaction table, per-address scoreboard, adjudicated data source with the memory read alongside the snoop and a deferred-read mode, monlite taps behind USE_MONITOR; the existing ACE BFM (RDS-DV, 2026-10-05) verified on onyx's gather shapes first, then the core generalizing `jet_prime_pair_fabric` to N ports on real ACE signaling, the D7 adapter for jet-prime, a fabric-style formal argument, Pattern-B DV, the reference rig with two jet-primes and the Genesys2 sweeps. Done when PRD criteria 1-6 hold, the sixth being cycles per transaction equal to the pair fabric it replaces. Filed 2026-11-20.

## Closed

(none)
