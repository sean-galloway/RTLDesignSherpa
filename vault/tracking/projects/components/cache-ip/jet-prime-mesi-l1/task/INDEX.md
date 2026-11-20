<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/jet-prime-mesi-l1 — tasks

**Next ID: TASK-004** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a
cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

(none)

## Closed

- **TASK-001** ([page](closed/TASK-001.md)) — beat HPDcache: jet forked as jet-prime at 2be919254 (2026-11-12); step 1 measures jet-prime straight onto memory on the ref rig (REF_CACHE_SEL 2) to split jet's miss cost into pair fabric and cache; steps 2-4 are multiple outstanding fills, a pipelined fabric, and the DV/formal to carry them; step 5 (11-17) the single-miss path, which met the done criterion at every depth. Closed 2026-11-18 on the control formal verdicts (safety prove PASS, covers PASS, step-3 liveness PASS; the step-5 liveness BMC still running, appended when it lands).
- **TASK-002** ([page](closed/TASK-002.md)) — the 2-cycle resident hit: jet-prime answers a hit in 3 cycles to HPDcache's 2, the one cycle per transaction left over HPDcache in the resident rows at depths 1-2 (and the 3.5 % depth-1 thrash margin); the v3 capture/classify split is a 100 MHz timing decision, so the cycle has to come from reading the set at capture or a hit-only early decision, measured first. Filed 2026-11-17 from TASK-001 step 5; closed 2026-11-19: hit floor 2 on the board (bin 7), the resident rows at HPDcache's numbers at depth 1 and within 0.05 cycles at depth 2, the depth-1 thrash margins widened to 7-11 %; a read hit answers from the port and a write hit acks in the classify cycle (delta 04).
- **TASK-003** ([page](closed/TASK-003.md)) — a tighter liveness environment for the jet-prime control and the liveness BMC run on the TASK-002 flat: the two 128-count bounds (`ap_age0/1`, `ap_snoop_progress`) are unproven on the step-5 and TASK-002 controls because the depth-192 run crawled (stopped at step 123 on 2026-11-18); derive the bounds from the environment's constants, tighten the step-5 assumptions, run at the depth they need, covers 7/7 and a mutation per change. Filed 2026-11-19 from TASK-001's stop note; closed 2026-11-20: age bound derived 68 and snoop bound 62, both asserted at 80, depth 192 -> 112, prove PASS in 1:07 (the 128 bounds had cost the step-5 run 15 h without finishing), covers 7/7, both mutants FAIL at the new bounds.

## Dropped

(none)
