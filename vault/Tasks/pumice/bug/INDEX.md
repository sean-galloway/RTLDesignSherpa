<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — bugs

**Next ID: BUG-021** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 19 | done (kept for history) |
| [dropped/](dropped/) | 1 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open


- **BUG-000** — TEMPLATE — copy this file, never file against it

## Closed

- **BUG-019** — DV wrappers had no depth axis; one profile now drives gate/func/full
  and the regression goes 376 -> 580 passed

- **BUG-020** — 35 undriven `OBS_*` registers: `OBS_ROW_HIT[8]` wired (the only
  sound row-hit count), the other 27 removed with their addresses left as holes
  (0 registers moved); docs synced

- **BUG-004** (was `PUMICE-001`) — Runtime-config axes corrupt data (board + sim)
- **BUG-005** (was `PUMICE-002`) — test_pumice_top_csr wr_rd roundtrip returns zero read beats
- **BUG-006** (was `PUMICE-003`) — test_ddr2_char_char_families integrity fail (bank_interleave/incremental_bl8)
- **BUG-007** (was `PUMICE-004`) — Refresh collides with an open row (arbiter registered-feedback hazard)
- **BUG-008** (was `PUMICE-012`) — LPDDR2 write-auto-precharge dropped writes
- **BUG-009** (was `PUMICE-019`) — top-tier shared sim_build races under clean parallel runs
- **BUG-010** (was `PUMICE-020`) — multiid read-return accounting: hist total != txn_count (data clean)
- **BUG-011** (was `PUMICE-025`) — read bandwidth was pinned at 48.7% of peak (FIXED: now 95%, write parity)
- **BUG-012** (was `PUMICE-027`) — write responses leave pumice out of AW order; the char write bridge routes B by position
- **BUG-013** (was `PUMICE-031`) — REG_LEVEL never reached pumice's TBs; the medium tier had never run
- **BUG-014** (was `PUMICE-037`) — concurrent read+write with reader gap >= 8 returns bad data AND corrupts cells
- **BUG-016** (was `PUMICE-041`) — the char sim never BUILT BL4 (title was wrong; one-line harness bug)
- **BUG-017** (was `PUMICE-042`) — mc_clk timing is not preserved across the CDC to the DFI
- **BUG-018** (was `PUMICE-043`) — batching residue at the aggressive watermark

- **BUG-003** — an arbiter pick rejected by its own final safety gate
  (`w_out_safe==0`) was pushed to the cmd FIFO and executed by the DRAM, while
  `w_fire_out` withheld `evt_*` so the bank timers never saw it — FIXED
  2026-09-27, one line in `pumice_cmd_arbiter.sv`
- **BUG-001** — one unattributed mismatched beat, seen once in 1008 matrix cells
- **BUG-002** — close-page below its command-bus ceiling — FIXED 2026-09-25,
  62.8% -> 85.7% via bank-timer lookahead + final-stage timing authority
  (silicon-confirmed +32.8%); residual is the in-order pick pipeline, the
  documented design point

## Dropped

- **BUG-015** (was `PUMICE-038`) — the reader's ADDR_HASH compare is inert in the char sim build
