<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/ecc-ip/bch — tasks

**Next ID: TASK-008** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 7 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Active

## Open

## Closed

- **TASK-005** — Implement the BCH decoder stages: closed 2026-10-03;
  `bch_key_equation_solver` (RIBM via the imported RS riBM), `bch_chien_search`,
  and `bch_decoder_core` landed with model-first DV, 16/16 clean gate configs,
  lint clean, MAS pages recording the landed RTL.
- **TASK-003** — BCH MAS v0.1 + signal-contract kmaps -- CLOSED 2026-10-08:
  the post-RTL re-point landed — every workbook citation now cites the landed
  RTL file:line behind the verify_citations drift gate, the kmaps follow the
  landed design (flip gating lives in the decoder core's r_release_apply,
  not the Chien fub), and all eight maps render VERDICT: IDENTICAL.
- **TASK-006** — BCH top wrappers + injector -- CLOSED 2026-10-08: landed
  2026-10-04; close condition re-verified (lint green on all 22 modules,
  wrappers exercised by the harness suites and both boards' batteries).
- **TASK-001** — Stand up the BCH component -- CLOSED 2026-10-08: the umbrella
  is realized (codec TASK-005, wrappers/gate DV TASK-006, math chapter
  TASK-004, both boards' harness validation TASK-007); the consumer question
  stays deferred exactly like reed-solomon TASK-003.
- **TASK-004** — BCH math chapter for novices -- CLOSED 2026-10-08: HAS ch07
  published with all five sections, worked numbers re-verified by
  `ch07_math_trace.py`, through the publication voice pass; the RS foundation
  is a sister chapter with cross-links rather than a single canonical copy
  (deviation recorded in the task file).
- **TASK-007** — BCH board loop bring-up -- CLOSED 2026-10-08: the Genesys2/
  ecc-ip/bch tree mirrors the RS area, G2 images board-validated 2026-10-04
  (`stable/MANIFEST.md`), A7 images re-run post-#89 (battery 7/7 + soak);
  PREBUILD drift check green and the 14-test UART harness suite (small
  profile, both IFACE values) re-run at close-out.
- **TASK-002** — Author the BCH HAS v0.1: closed 2026-10-03; the
  `docs/bch_has/` architecture specification mirrors the reed-solomon HAS,
  the v0.1 PDF builds, and every open item is tied to a PRD decision ID.

## Deferred
