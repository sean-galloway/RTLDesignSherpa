<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# scoria-ddr3-lpddr3 — tasks

**Next ID: TASK-009** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 4 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 4 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-001** — advanced scheduling / refresh modes survey.

- **TASK-006** — two formal/scoria proofs are weak and the 9-block tally hides
  it: dfi_cdc has 2 live assertions of 7 and wr_data_cam's data-integrity
  property is guarded off. 81 live / 6 disabled area-wide.

- **TASK-007** — four runtime assertions sit inside functional scoria RTL,
  against the standing no-assertions rule; three now have a mutation-verified
  formal proof to move to, the fourth (rd_aligner) needs a proof or a
  documented exception. BLOCKED on the owner's (a)/(b) decision recorded in
  the item.

- **TASK-008** — reconcile the HAS to a 1.0: choose `tWLMRD`'s maximum policy
  value, confirm-or-correct every INHERITED / MODIFIED / NEW marking against
  the landed RTL, finalize the CSR map from the RDL. Filed at TASK-002's
  close-out.

## Closed

- **TASK-005** — the three DFI v3.1 surface names presented (`dfi_reset_n`
  rename + the two data-phase selects driven); HAS text landed in v0.8 Ch 4.1.
  Multi-rank drive-from-granted-rank requirement stated for a future build.

- **TASK-002** — the scoria HAS authored and reconciled (v0.8), and the PRD
  stub replaced by PRD v1.0. D1-D3 settled, Q1-Q5 resolved; the remaining
  1.0 items are filed as TASK-008.

- **TASK-004** — `RD_EN_CYC` PLUMBED (not deleted): scoria_core passes
  ceil(DRAM_BL/DFI_RATE), the same expression scoria_top floors tRTW on. No
  change at the shipping point; the narrow case is now correct.

- **TASK-003** — the two uninstantiated FUBs stay dormant, on measured parity
  with LiteDRAM's working Genesys 2 core; each header now says so and why, and
  that the parity argument is DDR3-only.
