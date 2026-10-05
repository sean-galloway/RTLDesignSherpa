<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# andesite-ddr4-lpddr4 — tasks

**Next ID: TASK-017** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 10 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-016** — andesite macro integration + training/dfi/axi4 layer
  births: P1 init/mode-register rewiring, parked-suite re-derivation,
  `andesite_dfi_cmd_path`, `andesite_training_layer`, minors M-1..M-9,
  `andesite_dfi_layer`, `andesite_axi4_layer`, `andesite_core` + top
  suite. Plan: `docs/superpowers/plans/2026-10-04-andesite-macro-integration.md`.

## Closed

- **TASK-010** — BFM DFI 4.0 gap closure (G1-G5): closed 2026-10-04; landed
  in the RTLDesignSherpa-DV repo as commit 61a27d8fee3b (+30 tests, 1538
  unit passing); HAS ch06 gap table annotated with the commit and known
  omissions.
- **TASK-009** — verification reference models: closed 2026-10-04; HAS ch06
  now names three counterparties (BFM, DRAMsim3, CA round-trip tests).
- **TASK-008** — LPDDR4 book reconciliation: closed 2026-10-04; inline CKE
  and per-command CA cycle detail in the MAS; bank-count conflict resolved
  by owner ruling (index corrected in place).
- **TASK-007** — PB-REF evaluation: closed 2026-10-04; DEFER WITH NAMED
  CONDITION recorded as HAS ch06 Q7.
- **TASK-006** — CA parity / `alert_n` recovery sub-FSM: closed 2026-10-04;
  3-state recovery FSM specified in the MAS init_sequencer page.
- **TASK-005** — DFI 4.0 spec study + BFM gap analysis: closed 2026-10-04;
  every clause citation confirmed against the on-disk spec, five corrections
  recorded in-book, gap list filed as TASK-010 and now closed there too.
- **TASK-001** — advanced scheduling / refresh modes survey: closed
  2026-10-04; Bhati 2016-cited dispositions (adopt / evaluate-at-bring-up /
  model-only), PB-REF delegated to TASK-007.
- **TASK-004** — author the andesite kmap book: closed 2026-10-04; six
  generated tables (DDR4 command decode, LPDDR4 CA, address decode, MR0-MR6,
  ODT, FGR) with the citation gate green and MAS/HAS citing them; the docs
  tranche is complete with this close.
- **TASK-003** — author the andesite MAS v0.1: closed 2026-10-04; the
  `andesite_mas/` book is complete at v0.1 and owner-reviewed, with the DFI
  4.0 pin table and the contract anchors the kmap book cites.
- **TASK-002** — author the andesite HAS v0.1 and the family docs seed:
  closed 2026-10-04; the `andesite_has/` book is complete at v0.1 and
  owner-reviewed, and the `mem-ctrl-ip/docs/` family seed is committed.