<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — issues

**Next ID: ISSUE-017** — never recycle a number, even when its item closed.

An anomaly, risk, or open question not yet diagnosed. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 4 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 10 | done (kept for history) |
| [dropped/](dropped/) | 3 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **ISSUE-016** — `DFI_PHASE.gear_ratio`, `DFI_PHASE.bl` and `MR0.VAL` reset to a
  1:4/BL8 geometry on a 1:2/BL4 build; every soft_reset reverts them and the
  driver re-programs. A script that forgot once measured nothing, cleanly

- **ISSUE-015** — `init` programs the read path as wrlat=1/rden=6/delay=7 and
  levels against it; `char` then re-programs 1/1/2 underneath that leveling.
  Both are on the clean diagonal, so it works -- with unmeasured margin

- **ISSUE-014** — the RDL's `hits = col_ops - ACT` derivation goes negative
  under background-close paging; the board clamps it and blames a window
  boundary, but it reproduces inside one quiescent window (re-activation race)

- **ISSUE-000** — TEMPLATE — copy this file, never file against it

## Closed

- **ISSUE-005** (was `PUMICE-017`) — CAM->arbiter pick cone does not close timing: CLOSED (stale)
- **ISSUE-006** (was `PUMICE-021`) — paging_sched_cross in_order floor: MISCALIBRATED FLOOR, not an RTL stall
- **ISSUE-007** (was `PUMICE-024`) — ORDER_MODE overlays miss 75 MHz: CLOSED by shortening the pre-pick stage
- **ISSUE-008** (was `PUMICE-028`) — the pumice sim has never run the board's DRAM geometry
- **ISSUE-009** (was `PUMICE-032`) — three coverage gaps behind green runs
- **ISSUE-011** (was `PUMICE-036`) — every published board number predates the 2026-09-13/14 harness rewrite
- **ISSUE-012** (was `PUMICE-040`) — read alignment wastes 5 cycles of latency

- **ISSUE-002** — close-page modes reach only ~63% of their own command-bus ceiling
- **ISSUE-003** — SCHED_WR_WM.wr_batch_max may clobber the whole register on write
- **ISSUE-004** — the +25-30% batching gain was measured with the broken drain

## Dropped

- **ISSUE-010** (was `PUMICE-033`) — one extra AXI ID bit doubles the arbiter's pick cone
- **ISSUE-013** (was `PUMICE-044`) — read eye is 10 taps: IDELAY is the only read knob

- **ISSUE-001** — read latency is ~2x LiteDRAM's, and it caps small-burst reads
