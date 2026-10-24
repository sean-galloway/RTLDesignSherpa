<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# bridge — bugs

**Next ID: BUG-027** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 26 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open



## Closed

- **BUG-026** — a slave narrower than the fabric address was decoded on its own addr_width (`20'h30000000`; the upper bound dropped) — CLOSED 2026-10-23: decode sized to the fabric address width; generator unit test; 0 of 733 generated files changed
- **BUG-025** — bridge_2x2_lite_req concurrent AXI4-Lite write timed out at SEED=65563 — RESOLVED 2026-10-22: `axil_to_axi4_wide_align_wr` overwrote a held B when the master was slow to take it; `m_axi_bready` now waits for the register; new unit test fails before, passes after

- **BUG-024** — crossed-W deadlock between a CDC (lane) slave and a slot slave — RESOLVED 2026-10-22: per-path live-W counts toward lane slaves hold the master's other AWs; board 150/150 (reorder 3/3 on every build)

- **BUG-023** — a path's W destination FIFO overflowed when a width converter issued several AWs per master burst — RESOLVED 2026-10-22: FIFO full-checked and the full flag gates the AW; board 150/150

- **BUG-019** — unaligned INCR bursts kept their start misalignment past the first beat — RESOLVED 2026-10-22: every converter steps INCR from the aligned start; downsize start-lane accounting; board 150/150 with no path limits

- **BUG-018** — width-converted paths emitted illegal AXI for FIXED, WRAP, narrow and unaligned bursts — RESOLVED 2026-10-22: dwidth converters rewritten (PACK / PASS / EXPAND modes), BFMs fixed in RDS-DV 1.2.9, `path_caps` workaround removed; board 150/150 on all five stress builds

- **BUG-022** — AXI5 sideband on a rate-buffered width-converted path had two drivers (the buffer and a tie) — RESOLVED 2026-10-20: ties moved to the buffer input; bridge_bs_xmix 60 MULTIDRIVEN -> 0

- **BUG-021** — a monitored port reported false ORPHAN errors past 8 outstanding — RESOLVED 2026-10-20: every monitor gets MAX_TRANSACTIONS = its port's max_outstanding; board clean 3/3, narrow 300/300 with zero records

- **BUG-020** — a slave that waits for WVALID before AWREADY deadlocked the bridge — RESOLVED 2026-10-20: owner bypass in bridge_cdc_slave_arb, axi4_to_axil4_wr registers every AW; stress-slave W_FIRST gate; board w_first 20/20, CDMA with no AW skid

- **BUG-017** — read bandwidth below the perf floors once R interleaving landed — RESOLVED 2026-10-18: the interleaving slave BFM's scheduling, not the fabric; perf suite uses contiguous slaves, BFM VALID-drop race fixed in RDS-DV 1.2.8

- **BUG-016** — FULL-level: 14 tests fail with AXI4 write B-timeouts — RESOLVED 2026-10-04: converter B-CAM age-compare boundary swallowed every 32nd downsize B; best_age widened one bit, FULL suite green

- **BUG-001** — Generator emits NUM_SLAVES as a body localparam used in the port list
- **BUG-002** — All six *_mon_monitor stress tests fail (pre-existing)
- **BUG-003** — three 1x2_wr_*_mon_monitor stress tests fail at init
- **BUG-004** — generated xbar had no request arbiter: concurrent multi-master traffic OR-merged
- **BUG-005** — the test generator reverts hand-fixes to its own output
- **BUG-006** — the two slave BFMs disagree about an out-of-range access
- **BUG-007** — an out-of-range address hangs the master forever; the docs promise DECERR
- **BUG-008** — slave-port response routing assumes in-order completion, and nothing says so
- **BUG-009** — Response-tracking FIFOs overflow silently (HIGH)
- **BUG-010** — trace is not echoed on B/R when the slave lacks trace; the AXI5 checker calls that a violation
- **BUG-011** — in the _mon variants the subtractive slave's monitor is built and left unconnected
- **BUG-012** — Out-of-order slave tracking (enable_ooo) could not elaborate
- **BUG-013** — REGEN — the five NexysA7 char-framework bridges cannot be regenerated in place
- **BUG-014** — STRESS — three _mon monitor stress tests fail on a memory-bounds read
- **BUG-015** — APB/AXIL slave adapter FIFO tracking deadlock (historical record, resolved 2026-05-13; filed from the loose root write-up 2026-09-29)
