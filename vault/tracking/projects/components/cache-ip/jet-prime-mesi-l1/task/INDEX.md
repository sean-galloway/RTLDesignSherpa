<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/jet-prime-mesi-l1 — tasks

**Next ID: TASK-003** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a
cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-002** ([page](open/TASK-002.md)) — the 2-cycle resident hit: jet-prime answers a hit in 3 cycles to HPDcache's 2, the one cycle per transaction left over HPDcache in the resident rows at depths 1-2 (and the 3.5 % depth-1 thrash margin); the v3 capture/classify split is a 100 MHz timing decision, so the cycle has to come from reading the set at capture or a hit-only early decision, measured first. Filed 2026-11-17 from TASK-001 step 5.

## Active

- **TASK-001** ([page](active/TASK-001.md)) — beat HPDcache: jet forked as jet-prime at 2be919254 (2026-11-12); step 1 measures jet-prime straight onto memory on the ref rig (REF_CACHE_SEL 2) to split jet's miss cost into pair fabric and cache; steps 2-4 are multiple outstanding fills, a pipelined fabric, and the DV/formal to carry them; step 5 (11-17) the single-miss path, which met the done criterion at every depth.

## Closed

(none)

## Dropped

(none)
