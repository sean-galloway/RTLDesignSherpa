# pumice DDR2/LPDDR2 — area facts

Area facts for this component. **Method lives in `vault/handbook/`** — this
file links to it rather than restating it.

Was `vault/Tasks/pumice/task/open/TASK-004.md`, a "task" marked *informational;
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

Flat FR-FCFS arbiter with a 3-stage pick pipeline (STAGE-1a snapshot ->
STAGE-1b arg_sel -> pre-pick -> output). Select-to-fire is 4 registered stages.
Two consequences worth knowing before changing it:

- **The pre-pick is in-order.** A selected command occupies the slot until it
  fires, so speculative issue does not help — it blocks the command behind it
  (measured: close-page 30.77% -> 28.57%). See [[BUG-002]].
- **Lookahead beyond select-to-fire is unactionable.** `bank_timer` exports
  advisory `safe_*_la_o` and the final stage enforces the live `safe_*`;
  `BANK_LA` above the pipeline depth predicts readiness later than the command
  arrives, so it is dropped. The LA sweep saturates at 3 for this reason.

## Method — do not restate it here

- Running regressions, clean-all discipline, levels: `vault/handbook/dv/running-regressions.md`
- **The char-framework sim is the board gate before any pumice RTL commit:**
  `vault/handbook/dv/running-regressions.md` (was TASK-003)
- PeakRDL regeneration: `vault/handbook/design/regenerating-peakrdl-blocks.md`
- Reset/clock naming: `vault/handbook/design/reset-and-clocking.md`

## Work items

`vault/Tasks/pumice/` — task/bug/issue lanes. Bug and issue lanes are empty as
of 2026-09-25.
