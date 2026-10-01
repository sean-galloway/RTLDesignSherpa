<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# scoria-ddr3-lpddr3 — tasks

**Next ID: TASK-008** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 4 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
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
  documented exception.

- **TASK-005** — scoria claims DFI v3.1 but does not present `dfi_reset_n`,
  `dfi_wrdata_cs_n` or `dfi_rddata_cs_n` under those names; the first is a
  rename, the other two are a real multi-rank gap.

- **TASK-002** (ACTIVE) — author the scoria HAS. v0.1 is written; the PRD stub says it
  is waiting on a locked HAS. Starts from `docs/design-requirements.md`, the delta
  analysis against JESD79-3F / JESD209-3C / DFI v3.1, and closes when the three open
  decisions in it (DFI revision, write-leveling ownership, package split) are settled

## Closed

- **TASK-004** — `RD_EN_CYC` PLUMBED (not deleted): scoria_core passes
  ceil(DRAM_BL/DFI_RATE), the same expression scoria_top floors tRTW on. No
  change at the shipping point; the narrow case is now correct.

- **TASK-003** — the two uninstantiated FUBs stay dormant, on measured parity
  with LiteDRAM's working Genesys 2 core; each header now says so and why, and
  that the parity argument is DDR3-only.
