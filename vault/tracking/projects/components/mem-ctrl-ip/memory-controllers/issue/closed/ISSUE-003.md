# ISSUE-003: close_page pays ~2.5 MC cycles per dependent hop the SKU model does not (board 82-92 MB/s against the model's 104-119)

> Source: memory-controllers MC-018, 2026-11-17. `granite_sku100_close` (every
> column auto-precharging, the board's `close_page` preset) lands 25-30
> percent above the board on the one-bank families (`incremental`, `row_major`,
> `col_major`: model 98-119 MB/s against 78-92) and 30-60 percent above on the
> bank-parallel ones (`col_major_interleaved`, `row_thrash`, `random`: 289-312
> against 180-240), while the same model is within 1 percent of the board on
> every open-page cell of the same families.

> 2026-11-17 (ISSUE-004 closed): with the store's admission terms in the model
> the bank-parallel `close_page` rows moved further from the board --
> `col_major_interleaved` bl4 / bl8 312 -> 389 (board 235 / 213-219), bl16 289 /
> 312 -> 271 / 290 (180 / 240), `row_thrash` 312 -> 377 / 389 (208 / 197),
> `random` 281 / 293 -> 303 / 315 (188 / 207); the one-bank chains are
> unchanged (`incremental` 104 / 119 against 82 / 92, `row_major` 98 / 112
> against 78 / 87). The per-hop cost this issue asks about is now measured
> against a model whose own hop cost is the tRRD bound.

**Priority:** P3 -- `close_page` is the experiment's reference preset, not a
shipped point; but the gap is the pipeline's per-hop cost made visible, and it
is the same cost MC-013 saw as the one-slot ceiling before the lane.
**Status:** CLOSED 2026-11-17 -- measured: the un-hinted hop fires two MC cycles after its timer opens; resolved into MC-021 (a `hop_lag` model term, then the RTL question)
**Owner:** TBD

## The arithmetic

One 8-byte beat under close_page is ACT -> RD(A) -> (tRTP + tRP) -> ACT: the
model's chain is tRCD 2 + 1 + 3 = 6 MC cycles under tRC 7, so a one-bank
stream moves 8 B per 7 cycles = 114 MB/s, which is the model's cell. The board
moves 8 B per ~9.5 cycles. The extra ~2.5 cycles per beat are what the
decode -> fire pipeline and the next-op hint do not recover when EVERY column
is a dependent hop (the hint lands one hop per fire; a chain of three hops per
beat has two it cannot pre-arm). On open-page streams the hops are one per
burst or per row and the cost is below the model's error bar.

## What settles it

`PERF_PICK_PROBE` on the granite proxy under `close_page` for ~200 cycles of
`incremental`: the cycle each ACT / RDA fires against the cycle its timer
opened. If each hop lands one cycle late, the model gains a `hop_latency`
term (a request's next command no earlier than its last fire + N slots) and
the RTL question is whether the hint can pre-arm the second hop. A recorded
no-action is acceptable: the shipped SKU is open-page.

## Resolution (2026-11-17)

The probe this issue asked for was run (`PERF_PICK_PROBE` + `PERF_DRAM_TRACE`
on the granite proxy under `close_page`, 64 cycles of steady-state
`incremental`; `char_results/model_knob_grid_2026-11-17.md` section 3):

- ACT -> column lands at tRCD exactly on 99 percent of beats: the next-op
  hint pre-arms the column.
- The ACT after the auto-precharge fires two cycles after
  `bank_act_ready_i` rises: the timer opens at cycle 13, the decode's `r_req`
  shows the pair at 14, the winner register and the fire at 15. Every period.
  ACT -> ACT is 10 cycles on writes (88 percent of the pass) and 9 on reads,
  against the model's 7.7 / 6.7: RTL minus model +2.1 / +1.95 cycles per
  beat, the ~2.5 this issue estimated.
- On eight banks (the `bank_interleave` preset, which is also close page --
  ISSUE-002) the same two cycles show against the rank timer: ACT -> ACT 3
  against `t_rrd` 2 (the registered `trrd_ok`), plus two empty select slots
  after each column pair; 3.4 cycles per beat against the model's 2.0.
- The proxy reproduces the board on this preset (81.9 / 92.5 and 80.3 / 89.4
  against 82 / 92 and 80 / 90), so the cost is the RTL's, not the board's.

The model gains the `hop_latency` term this issue named, as **MC-021**
(`hop_lag`, 2 slots, for the hops the hint does not cover), followed by the
RTL question of whether the lookahead can reach the post-precharge and
rank-level timers. The knob grid of the ISSUE-004 terms moves no close_page
cell into tolerance (best 1 / 15), as expected for a missing term.

## Re-read against the MC-021 step-7 model (2026-11-19)

The `hop_latency` term this issue named was not the mechanism; the two cycles
per hop decomposed into the pick pipeline's registers (MC-021 step 1: the
request register, the winner register with its hold, the one-cycle hint,
`pick_la` 2), the ACT spacing count (step 2, BUG-004), the record's hit lag
(step 4) and the store's write record fill gate (step 6). Every close_page cell
this issue named is inside tolerance in
`char_results/compare_model_sku_vs_board_sku100s4_s7_2026-11-19.md`: the one-bank
chains `incremental` 82 / 93 against 82 / 92, `row_major` 78 / 87 against 78 /
87, `col_major` 79-82 / 88-92 against the same; `col_major_interleaved` bl4 /
bl8 / bl16 388 / 389, 254 / 334, 172 / 239 against 386 / 387, 250 / 361, 171 /
238; `row_thrash` 242 / 316 against 238 / 314; `random` 205 / 258 against 203 /
258. The RTL question the issue raised (can the lookahead reach the
post-precharge timers) was answered in its measured shape: no (`ap_act_la`
false), and the one RTL change that bound was step 5's. Nothing of this issue
remains.
