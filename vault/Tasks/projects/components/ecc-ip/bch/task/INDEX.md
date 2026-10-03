<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/ecc-ip/bch — tasks

**Next ID: TASK-005** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 4 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Active

## Open

- **TASK-001** — Stand up the BCH component: references gathered and draft
  PRD v0.1 landed 2026-10-03; HAS, RTL + DV, board harness to follow. Runs
  the way reed-solomon TASK-001 ran — closes when the component exists and
  passes end to end.
- **TASK-002** — Author the BCH HAS v0.1: the `docs/bch_has/` architecture
  specification mirrors the reed-solomon HAS; closes when the v0.1 PDF builds
  and every open item is tied to a PRD decision ID.
- **TASK-003** — Author the BCH MAS v0.1 and signal-contract kmaps: the
  `docs/bch_mas/` micro-architecture specification plus
  `gen_bch_signal_contracts_kmaps.py` and `bch_signal_contracts.xlsx`; closes
  when every block is documented to signal level with FSM policy per block and
  the kmap contracts are re-pointed at RTL lines after the first RTL lands.
- **TASK-004** — Author the BCH math chapter for novices: from zero to the
  decoder math, hand-checkable GF(2^4) numbers, BCH-specific depth (minimal
  polynomials, the evenness shortcut, no Forney stage); the shared
  finite-field foundation is written once under reed-solomon TASK-004 and
  linked.

## Closed

## Deferred
