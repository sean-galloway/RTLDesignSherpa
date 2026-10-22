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

## Scheduler shape

Two pick cores behind `pumice_core`'s `SCHED_CORE` parameter (mc_common_pkg
`MC_SCHED_*`; the tb tops, `pumice_top_geared` and the ddr2_char harness
forward it; the perf proxy takes `TEST_SCHED_CORE`):

- **BANK_PICK (default since 2026-10-22, mem-ctrl recovery Phase 2):**
  `mc_bank_pick` on the storage plane's REGISTERED per-bank head records.
  Decode (per bank) -> round-robin arbiter -> fire, every stage fed by flops;
  `BANK_LA` = 2 = the pipe depth, so a request reaches the fire stage the
  cycle its timer opens. A one-cycle pop shadow, a next-op hint (hop ==
  pipe depth) and register-only speculation on the held winner (hop <
  pipe depth) land the dependent hops of a row walk on the JEDEC floor
  (col_major inter-row gap 6 rd / 8 wr at the board timings). The pick
  register loads every cycle; a winner waiting on a timer holds through a
  registered mux in front of the fire stage, bounded by its bank's
  lookahead bit, and its own stale request is masked out of the pick
  (Phase 3, 2026-10-22: no fire-cone arc reaches a register's
  load enable; the record carries its hit, classified at the storage edge).
  The order modes / row-col selectors / QoS CSRs are no-ops on this core.
- **FRFCFS (`SCHED_CORE=0`, research):** flat FR-FCFS arbiter with a
  3-stage pick pipeline (STAGE-1a snapshot -> STAGE-1b arg_sel -> pre-pick
  -> output); select-to-fire is 4 registered stages. The pre-pick is in-order
  (speculative issue blocks the command behind it, [[BUG-002]]) and lookahead
  beyond select-to-fire is unactionable (the LA sweep saturates at 3). The
  sched_order / paging_sched_cross / close_drain cells build this core.

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
