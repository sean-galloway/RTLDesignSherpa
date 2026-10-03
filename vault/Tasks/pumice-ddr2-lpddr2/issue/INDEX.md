<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — issues

**Next ID: ISSUE-021** — never recycle a number, even when its item closed.

An anomaly, risk, or open question not yet diagnosed. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 16 | done (kept for history) |
| [dropped/](dropped/) | 3 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **ISSUE-020** — the paging perf assertions (sweep exact-100% claim at
  default geometry, pref_row_first floor, ISSUE-002 floors at board
  geometry) are calibrated against pre-compliant tFAW/tRRD window
  behavior; pumice's gate fails on them in combinations. Re-pin the
  baselines (Sean's call, ISSUE-002 process) or fund a skid/bypass so
  fire-stage holds stop head-of-line blocking. Surfaced while closing
  BUG-021; all numbers measured there.



## Closed

- **ISSUE-019** — CLOSED: `pumice_cmd_history_checker` now carries GLOBAL tRRD
  and tFAW checks on a per-rank ACT history, armed from the live config in both
  macro suites (171 passed at tRRD=2; proved live by inflating the window to 30,
  which fires and reports the real 10-cycle tightest spacing). The checking gap
  is filled; unreachability is evidence, not proof — see TASK-035 tier 1. The two
  RTL comments that claimed the check was at the fire stage are corrected.

- **ISSUE-018** — FIXED: `global_timers` derives its next state once and feeds
  both the counter flops and the readiness flops from it, so the outputs are no
  longer a cycle stale; the formal proof now assumes only what they publish and
  every JEDEC window holds. Board gates green, WNS +0.031 (was +0.029)

- **ISSUE-015** — measured: both read-path tuples give an IDENTICAL 10-tap eye
  (same bitslip, same tap), so the choice costs no margin; the real hazard,
  drifting off the `rddata_delay = t_rddata_en + 1` diagonal, is now guarded

- **ISSUE-017** — `PUMICE_SYS_75` defaults ON, so `make bitstream` builds the
  board's 75 MHz design point; the frequency is announced in a banner and the
  board's own clock is checked before any sequence runs

- **ISSUE-014** — row hits now come from `OBS_ROW_HIT[8]`; the old `col_ops - ACT`
  derivation undercounts by 2.06% on silicon (239,084 vs 234,257)
- **ISSUE-016** — `program_geometry()` reads geometry from the hardware
  (`BUILD_CONFIG`) instead of `BOARD_*` env constants; needed no decision

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
