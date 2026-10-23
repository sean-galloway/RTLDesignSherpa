# pumice DDR2/LPDDR2 — area facts

Area facts for this component. **Method lives in `vault/handbook/`** — this
file links to it rather than restating it.

Was `vault/tracking/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/task/open/TASK-004.md`, a "task" marked *informational;
do not close*. A work item that cannot be closed is not a work item, and a
handover parked in the task tracker is read by nobody who is not already
reading the tracker. Sean, 2026-09-25: *"if a task can't be closed, that means
it is a rule that should be elsewhere."*

## Where it landed

Nexys A7, 75 MHz / DDR2-300 / BL4 on x16, **peak 600 MB/s**:

| workload | measured | of peak |
|---|---|---|
| streaming read (open page, row_major) | 572.3 MB/s | 95.4% |
| streaming write | 570.3 MB/s | 95.1% |
| concurrent read+write, bus total | ~570 MB/s | 95% (2.00x LiteDRAM, identical harness) |
| close page (`close_page` reference corner) | 45.0 MB/s | 7.5% |

`defaults` (power-on, nothing programmed) measures identical to `open_page` to
+-0.0 MB/s — build default is OPEN page
(`localparam PAGE_POLICY_BUILD_DEFAULT = PAGE_POLICY_OPEN` in `pumice_top`).

Board build: `PUMICE_SYS_75=1 make bitstream` in `build-perf`. **Without that
define you get 66.67 MHz and every number is wrong.**

Area: `pumice_top` is 12 224 LUT / 7 878 FF, ~5x LiteDRAM's controller+PHY for
equal streaming bandwidth. That is the deliberate research-controller trade.

## Traps that have cost real sessions here

1. **The default sim geometry is not the board's.** The core suite defaults to
   BL8 / 64-bit beat / device == beat, so one DRAM burst is FOUR bus beats and
   a per-sub-command rate limit is divided by four before an assertion sees it
   — that is how a 2x read throttle once shipped green. Board geometry is
   `TEST_DRAM_BEAT=32 TEST_DRAM_BL=4 TEST_DRAM_DEVICE_W=16`. If a board number
   and a sim number disagree, suspect this FIRST. Two sweeps in one session on
   2026-09-25 were invalidated by comparing across geometries.

2. **The host does not measure the clock; it is TOLD.** `--clk-mhz` defaults to
   66.667 while the shipping bitstream is 75 MHz, and
   `_bw_mb_s = (bytes/cycles) * clk_mhz` — so the default silently scales every
   MB/s by 0.889 and mis-states the peak as 533. `pumice_char.resolve_clk_mhz()`
   reads `clk_hz` from the bitstream's own BUILD_CLK_HZ; pass `--clk-mhz 75`
   or let it resolve. Same class of error in the other direction once reported
   open_page reads at 123% of what the port can physically carry.

3. **`baseline` is now `close_page`.** The old name read as "the shipping
   default", which it never was — it is the deliberately pessimal reference
   corner, and its ~45 MB/s was repeatedly quoted as pumice's default
   performance. The shipping default is `defaults` / `open_page` at 95.4%.

4. **Check a parameter is actually PASSED before believing the flow sets it.**
   `ddr2_char_macro` did not thread `RD_RET_DEPTH` (board default is now 64 via
   `PUMICE_RD_RET_DEPTH`), and `ddr2_char.num_gen` defaulted to 1 while the
   board carries 2+ per direction — call `sync_gen_config()`, never trust a
   hardcoded count.

5. **Stall attribution is priority-ordered and has no category for pipeline
   serialisation.** A high `actlimit` share proves tFAW/tRRD was UNSATISFIED,
   not that relieving it would help: on `static_close` it reads 70.4%, yet
   relaxing tFAW/tRRD 6/2 -> 1/1 leaves throughput and the counter
   bit-identical. Confirm every stall verdict by moving the knob.

6. **The page policy's idle-timeout close is on at reset (policy_mode 3,
   tr_init 2) and, until BUG-030's veto, closed rows that queued bursts still
   needed: one ACT per 8-column burst from three interleaved threads up,
   307 / 354 MB/s on FR-FCFS instead of 554 / 553, on every address family.
   Two knobs mislead here: the perf proxy's `TEST_PAGE_POLICY` writes the
   LEGACY `REFRESH_TUNING.page_policy_or` (the engine is `PAGE_POLICY_CFG.
   policy_mode`; use `TEST_PAGE_MODE` / `TEST_TR_INIT`), and the page stats
   counted those closes as conflict MISSES. Any "the policy is not it" claim
   needs the ACT count with `TEST_TR_INIT=0` beside it.

## Scheduler shape

Two pick cores behind `pumice_core`'s `SCHED_CORE` parameter (mc_common_pkg
`MC_SCHED_*`; the tb tops, `pumice_top_geared` and the ddr2_char harness
forward it; the perf proxy takes `TEST_SCHED_CORE`). **Owner ruling,
2026-10-22: pumice (research) carries FR-FCFS by default; granite (the
product) carries BANK_PICK.** The Phase 2 default of BANK_PICK on pumice
lasted one day; every harness / tb / proxy default followed the flip.

- **BANK_PICK (`SCHED_CORE=1`; granite's default, selectable here):**
  `mc_bank_pick` on the storage plane's REGISTERED per-bank head records.
  Decode (per bank) -> round-robin arbiter -> fire, every stage fed by flops;
  `BANK_LA` = 2 = the pipe depth, so a request reaches the fire stage the
  cycle its timer opens. A one-cycle pop shadow, a next-op hint (hop ==
  pipe depth) and register-only speculation on the held winner (hop <
  pipe depth) land the dependent hops of a row walk on the JEDEC floor
  (col_major inter-row gap 6 rd / 8 wr at the board timings). The pick
  register loads every cycle; a winner waiting on a timer holds through a
  registered mux in front of the fire stage, bounded by its bank's
  lookahead bit, and its own stale request is masked out of the pick for
  the TWO cycles the request register still describes a fired entry
  (Phase 3, 2026-10-22: no fire-cone arc reaches a register's load enable;
  the record carries its hit, classified at the storage edge. The second
  mask cycle, same day: without it a free slot per burst went to the
  idle-timeout close of another generator's row, 461 vs 567 MB/s with four
  generators per direction).
  The order modes / row-col selectors / QoS CSRs are no-ops on this core.
- **FRFCFS (`SCHED_CORE=0`, pumice's DEFAULT):** flat FR-FCFS arbiter with a
  3-stage pick pipeline (STAGE-1a snapshot -> STAGE-1b arg_sel -> pre-pick
  -> output); select-to-fire is 4 registered stages. The pre-pick is in-order
  (speculative issue blocks the command behind it, [[BUG-002]]). Dependent
  hops (column behind its ACT, ACT behind its PRE) classify against the
  command being PICKED this cycle, not the registered bank image, and the
  fire stage is the only JEDEC authority (live row match for columns,
  bounded holds for tRCD / tRP / tRC / an AP drain) -- TASK-044, which
  took col_major from 24 to 13 / 15 cycles per row (the floor). The class
  priority PREPARES BANKS (TASK-045, `access_pref` 0): after a column a
  ready row command takes the slot, inside that column's tCCD, after a row
  command columns -- the next bank's ACT rides inside the current run
  (col_interleave 12 -> 9 slots per row; `access_pref` 1 is the old
  column-first, 2 row_first, 3 precharge_first). Close-on-drain
  (`CLOSE_ON_DRAIN`, default 1 again) is decided AT THE FIRE STAGE from the
  live window (`w_ap_last`: no same-row entry anywhere, valid or pending,
  either direction -- promote as well as demote; the pre-pick's
  age-youngest candidate is only a hint, and was wrong whenever a row
  command interposed) and ARMED PER BANK by the page policy's predictor
  (`drain_close_ok_o`): a bank whose ACTs change rows after a short row or
  after a demand precharge closes on its last visible column, a bank whose
  closed row gets reopened stays open; nothing arms outside the fixed_open
  timer mode, and a bank's first ACT is no evidence. The
  sched_order / paging_sched_cross / close_drain cells pin this core
  explicitly (redundant with the default, kept as the statement of the
  dependency). Perf of the two cores on the same harness: Phase 3 report
  §5.1 / §5.5 (pumice FR-FCFS vs granite BANK_PICK vs LiteDRAM, 1/2/4/8
  threads); section 5.6 has TASK-045 and the `mixed` family where the
  window matters (FR-FCFS 311 MB/s vs BANK_PICK 82 at eight generators).
  Isolated bench for the pick core: `dv/tests/top/test_pumice_core_bankprep.py`
  (40 s; cycles per row, explicit PREs, per-cycle arbiter trace with the
  fire-stage siblings). Design note: `vault/handbook/design/dependent-hops-forward-the-pick.md`.

One plane-level trap both cores share: a signal that must mean "the command
being granted" (the REFpb rotor mirror's `grant_was_pb_i`) has to come from
the core's output in the grant cycle, not from the command FIFO head
([[BUG-029]]).

## Method — do not restate it here

- Running regressions, clean-all discipline, levels: `vault/handbook/dv/running-regressions.md`
- **The char-framework sim is the board gate before any pumice RTL commit:**
  `vault/handbook/dv/running-regressions.md` (was TASK-003)
- PeakRDL regeneration: `vault/handbook/design/regenerating-peakrdl-blocks.md`
- Reset/clock naming: `vault/handbook/design/reset-and-clocking.md`

## Work items

`vault/tracking/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/` — task/bug/issue lanes. Bug and issue lanes are empty as
of 2026-09-25.
