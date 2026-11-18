# The ACT spacing was a count, not a pipeline: mc_global_timers N -> N (memory-controllers BUG-004, 2026-11-18)

**Question (owner):** "bank inter-leave sucking this badly seems wrong. why is
that?" -- the granite SKU's `bank_interleave` preset at 238 MB/s of an 800 MB/s
peak on the board, and the model 15 percent under even that (MC-021 step 1).

**Answer (board-confirmed: 238 -> 387 MB/s, model 388, proxy 387):** the RTL spaced activates 3 MC cycles apart, 30 ns, on a part whose
tRRD is 10 ns. In close page every 8-byte column needs its own ACT, so the ACT
rate is the throughput; and the DUAL_ISSUE row lane, which fires only beside a
column that lands at ACT + tRCD = 2, was never timer-ok on a column slot. Both
come from one count: `mc_global_timers` enforced a programmed window N as N+1
cycles. Fixed as BUG-004; this note is the model and proxy evidence. The board
record is in the BUG-004 file and `board_bug004_*` when it lands.

## 1. The measurement that answered it

| | value | source |
|---|---|---|
| ACT-to-ACT gap, proxy bank_interleave run | min 3, 52,028 of 65,810 gaps = 3 | `dram_p8_bi_close.json` (2026-11-17) |
| ACTs fired beside a column (the lane) | 0 of 65,810 | same trace |
| lane state over the 64-cycle pick probe | held pair 7 (bank 3 ACT) all 64 cycles; `w2_timer_ok` and `w_col_fire_now` never high together | `pick_p9.json` |
| part tRRD (MT47H64M16 x16, 2 KB page) | 10 ns = 2 CK = 1 MC cycle at 100 MHz | JESD79-2F Table 42 |
| host `ddr2_timings_mc_cycles` tRRD | ceil((10 + 5 ns phase margin) / 10) = 2 | `pumice_device.py` |
| RTL enforced | 3 (= 2 + 1) | `mc_global_timers.sv` readiness `== 0 / <= 1` |

The host's margin is correct (a lane ACT on phase 1 then a main ACT on the next
cycle's phase 0 are 5 ns apart, so 2 cycles is the floor while the lane exists).
The block's extra cycle is the loss. Ceiling at 3 cycles: 8 B / 30 ns = 267 MB/s;
the board's 238 is that minus the stale re-picks of MC-021 step 1.

pumice TASK-034 (closed 2026-09-29) had found the N+1 by formal, documented it as
the CSR contract and kept it, calling the prize "much smaller than the tRTW
cliff". It was measured on a pumice 1+1 disjoint-bank point where the ACT rate
does not bind. The bank timers were made exact on 2026-10-17 (MC-003); the
global timers were not. MC-021 step 1 then carried the N+1 into the model as
`rank_ok_lag 1` because it matched the RTL.

## 2. Priced before the RTL was touched

`scratchpad/mc021/rrd.py`: the model on `bi_close incremental_bl8`, ACT spacing
set three ways (SKU_RRD2 = the SKU preset with nRRD 2 CK):

| ACT spacing | wr / rd MB/s | lane ACTs |
|---|---|---|
| 3 cycles (RTL then: nRRD 4 CK + rank ok one slot late) | 199 / 202 | 0 |
| 2 cycles, the counter's +1 dropped (rank_ok_lag 0) | 388 / 388 | 130k |
| 2 cycles, the host's margin dropped instead (nRRD 2, late ok) | 389 / 389 | 130k |
| 1 cycle, bare JEDEC (nRRD 2, ok on time) | 390 / 390 | 131k |

Either +1 removed doubles the cell; the lane engages (every ACT rides beside a
column); below two cycles buys nothing because the pipeline then runs one
column per two cycles. The SKU open-page cell does not move (778 / 781).

## 3. The fix, and the proxy after it

Fifteen compare constants in `mc_global_timers.sv` (`ok_nxt = event ? reload <= 1
: count <= 2`; tFAW slot-free `<= 2`; L/S outputs `<= 1`; the `obs_*` debug
flags `> 1` so they stay on the gate's cycle), the golden copy the same, formal re-pinned at exactly N (`c_*_exact` covers), host `rtw_guard` 6 ->
7 so the PHY-measured tRTW spacing (21 cycles on DQ) does not move, model
`rank_ok_lag` default 0 and preset nRTW 42 CK. The RTL proxy
(`test_granite_char_perf`, `TEST_DUAL=1`, pool 16, 100 MHz, the board's exact
pairs) on the three board presets, before (2026-11-17 runs) and after:

| preset (scheme, policy) | family | before wr / rd | after wr / rd | board 2026-11-16 |
|---|---|---|---|---|
| bank_interleave (2, close) | incremental | 235.0 / 229.6 | **386.8 / 384.7** | 234 / 233 |
| bank_interleave (2, close) | col_major | 234.9 / 226.7 | **386.5 / 386.1** | 238 / 233 |
| close_page (1, close) | incremental | 81.9 / 92.5 | 81.8 / 92.4 | 82 / 92 |
| close_page (1, close) | col_major | 80.3 / 89.4 | 80.3 / 89.4 | 80 / 90 |
| scheme 2, open page | incremental | 757.9 / 751.4 | 759.0 / 756.2 | |
| scheme 2, open page | col_major | 236.3 / 225.9 | **386.5 / 380.1** | |

bank_interleave trace after: ACT-to-ACT gap 2 (65,606 of 65,660), lane fires
43,624 of 65,844 ACT cycles. The single-bank close_page chain is unchanged (one
bank, tRC-bound: tRRD never binds). The model said 388; the RTL does 387.

## 4. The model's prediction for the board re-run

`compare_model_bug004_vs_board_prefix_sku100def_2026-11-18.md` puts the model
with the fixed default beside the PRE-fix board set (40 in / 17 out): this is
what the board should move to, not a residual.

| preset | cells | prediction |
|---|---|---|
| defaults / open_page (the SKU) | 30 | unchanged: incremental 778 / 781, col_major 283 / 390, mixed 284 / 284 (union 569, +4.7 vs 543), random 734 / 749 |
| bank_interleave | 12 | +40 .. +67 percent: row-hit cells 388 / 388, col_major 333, col_major_interleaved_bl8 371 |
| close_page single bank | 9 | unchanged (83 / 93, 78 / 87, 82 / 92) |
| close_page interleaved | 3 | col_major_interleaved_bl4 370 / 370 (+58), bl8 287 / 320 (+35 / +46), bl16 184 / 217 |
| close_page row_thrash / random | 2 | 250 / 275 (+21 / +40), 217 / 240 (+15 / +16) |
| close_page mixed | 1 | 54 / 54 (union 107) against the board's 73 / 152 (union 145): the model's close-page mixed turn moved DOWN with the lag gone. **The board confirmed it: 56 / 56 (union 111).** The one cell the fix costs; see the board record |

## 5. Gates

| gate | result |
|---|---|
| `formal/mc_common/mc_global_timers` prove / cover | prove PASS (depth 32; the first draft failed Family 2 `a_obs_trrd`: the obs_* flags had to move with the gate), cover PASS, all 11 covers reached incl. the five `c_*_exact` and `c_tfaw_exact` at step 6 |
| `formal/mc_common/mc_global_timers` equiv (tournament vs serial gold, both at N) | running at commit time: depth-32 BMC of the tournament against the serial gold with anyconst timings, 40 minutes in and stalled on step 22 of 32 (the MC-011 note recorded the same solver stall near step 23 for half an hour); both copies carry the identical fifteen edits, prove and cover pass. The result is appended to this record when it lands (BUG-004 record) |
| granite top `run-all-full` | 29 passed, 5 skipped, 1 xfailed |
| pumice `run-all-func-both` | 220 passed / 4 skipped, both geometries |
| scoria `run-all-func` | 187 passed; 16 failed = 10 stale bank-timer cases (`t_rcd_i`, a port renamed in MC-007) + `column_pick_smoke` (undriven `*_ready_la_i`) + the scheduler-plane cases (`u_arbiter`, renamed) -- pre-existing stale TBs -- and the 6 `scoria_global_timers` cases that asserted N+1, rewritten to exact N: **10 passed** on rerun; `scoria_dram_configs.prog` was `spacing - 1` (N+1 compensation, already under-spacing the bank windows since MC-003) -> `spacing`; consistency test 12 passed |
| andesite fub / macro / top | the same stale TB classes (bank timer, arbiter, `u_arbiter`, a TB compile error in `andesite_core_tb.sv`); `andesite_global_timers` rewritten the same way: **12 passed**; `andesite_dram_configs.prog` -> `spacing` |
| vendor Ramulator tests / char_model tests | 217 / 36 passed |
| granite lint (`make lint`) | clean |
| `GRANITE_SYS_100=1 make bitstream` | WNS **+0.029** under the 0.2 ns budget, 0 failing endpoints, 37,297 LUT / 32,918 FF (11-16: 37,357 / 32,918, +0.012) |
| board, `--profile every` on `ddr2_char_granite_sku100_bug004_2026-11-18.bit` | smoke ALL PASS (memtest 32 / 32); 68 cells, 0 mismatched; **bank_interleave 238 -> 387 MB/s** on every row-hit cell, close_page col_major_interleaved_bl4 235 / 232 -> 379 / 387, SKU and single-bank cells within 0.2 percent; model vs this set 45 in / 3 out; final RTL rebuilt and re-run (every within 0.4 percent, windows: close_page row_thrash +18 / +28, random +8 / +13, **close_page mixed 73 / 152 -> 56 / 56**, SKU flat), model vs the complete set 53 in / 4 out (`board_bug004_granite_sku100_2026-11-18.md`) |

## Files

- RTL: `projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_global_timers.sv`
- formal: `formal/mc_common/mc_global_timers/{formal_global_timers.sv,mc_global_timers_gold.sv,Makefile}`
- host: `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/build-perf/host/pumice_device.py` (`rtw_guard` 7)
- model: `references/ramulator2/overlay/.../granite_sku_controller.cpp`, `.../dram/ddr2.py`, `bin/char_model.py`, tests
- model CSVs: `model_ramulator2_ddr2_granite_sku100{,_bi,_close}_bug004_2026-11-18.csv`
- CSR text: `pumice_csr.rdl`, `scoria_csr.rdl`, `granite_csr.rdl` (+ regenerated docs), pumice MAS / HAS
- DV: scoria / andesite `test_*_global_timers.py`, `*_dram_configs.py`, `test_scoria_dram_config_consistency.py`
- tracker: memory-controllers BUG-004 (closed), MC-021 step 2, pumice TASK-034 addendum
- handbook: `design/global-windows-revalidate-at-issue.md`, "The fifth"
