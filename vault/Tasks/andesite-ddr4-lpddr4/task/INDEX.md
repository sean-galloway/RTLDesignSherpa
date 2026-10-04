<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# andesite-ddr4-lpddr4 — tasks

**Next ID: TASK-011** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 5 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 5 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-006** — CA parity / `alert_n` recovery sub-FSM (3-state, out of the
  bank machine), from the ddr4 research index.
- **TASK-007** — per-bank-group refresh accounting (PB-REF, tRFC per bank
  group); evaluation against Bhati 2016, decision recorded in HAS ch06.
- **TASK-008** — LPDDR4 book reconciliation: inline CKE on the CA bus and
  per-command CA cycle detail (bank-count conflict resolved by owner ruling
  2026-10-04; the research index was corrected in place).
- **TASK-009** — verification reference models: DRAMsim3 cross-check + BFM
  `lpddr4_ca.py` encoder round-trip tests, recorded in HAS ch06.
- **TASK-010** — BFM DFI 4.0 gap closure (G1-G5 from the TASK-005 study:
  LPDDR4 CA map, 1600 CSVs, gear-down behavior, CA-VREF training, per-slice
  read leveling); work lands in the RTLDesignSherpa-DV repo.

## Closed

- **TASK-005** — DFI 4.0 spec study + BFM gap analysis: closed 2026-10-04;
  every clause citation confirmed against the on-disk spec, five corrections
  recorded in-book, gap list filed as TASK-010.
- **TASK-001** — advanced scheduling / refresh modes survey: closed
  2026-10-04; Bhati 2016-cited dispositions written into the file (adopt /
  evaluate-at-bring-up / model-only), PB-REF delegated to TASK-007.
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