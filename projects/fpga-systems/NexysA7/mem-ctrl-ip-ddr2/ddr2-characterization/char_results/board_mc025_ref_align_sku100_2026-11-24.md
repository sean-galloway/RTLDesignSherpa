# MC-025: refresh alignment -- a launch-timed tREFI reload makes board runs repeat to the cycle

> memory-controllers MC-025, 2026-11-24. The owner's question after MC-024's
> board run: "can we have a test signal that comes from the TB/harness that
> resets the refr counters? ... We want to most accurately compare nearly
> identical runs to sus out minor flaws in the uarch. If the refr noise
> dominates, we are blind." Granite SKU, 100 MHz, Nexys A7.

## 1. Why runs differed

The stimulus is deterministic: generator seeds are an FNV hash of the
scenario name, and the row-hit cells are fixed walks. The controller's tREFI
countdown (`mc_xddr2_refresh_ctrl.r_refi_cnt`) free-runs from init, and the
host's GO arrives over UART at an arbitrary point in it. Where the refreshes
land in the traffic decides the mixed cell's mode (ISSUE-005, MC-023 item 4)
and the bank_interleave row-hit level (ISSUE-007). So every board run was a
draw on the refresh phase, and any A/B smaller than that draw was invisible.

The DRAM keeps its own refresh row counter: each REFab refreshes the next
row index in all 8 banks (8,192 per 64 ms on the MT47H64M16). The
controller's refresh state is only the countdown and the pending count.
Granite ties refresh postpone and pull-in off, so after one reload of the
countdown no refresh state carries over from earlier traffic.

## 2. What was built

- `granite_top_geared.refi_reload_i` (aclk, one-cycle pulse): a test input
  for the reload that `mc_xddr2_refresh_ctrl` already had
  (`if (!enable_i || refi_reload_i) r_refi_cnt <= w_refi_eff`). A product
  ties it 0; granite's own TBs and `mc_ocelus_tb` drive it 0.
- `chargen_regs.REF_ALIGN @ 0x618`: `en[0]` (reset 0), `offset[31:16]`
  (reset 0). The regblock was deleted and regenerated through
  `bin/peakrdl_generate.py -o`; the diff is the one register.
- `char_engine_block.refi_reload_o`: when `en` is set, every launch (the
  chargen GO pulse, any write or read bit, already in mc_clk through the APB
  shim) loads the offset, and the reload pulses at launch + offset + 1. That
  is cycle-exact against GO, unlike anything the host can time over UART.
  `granite_char_macro` wires it to `granite_top_geared`. The pumice
  (`ddr2_char_macro`), scoria, LiteDRAM (`char_engine_harness`) and
  fabric-benchmark (`fb_harness`) consumers connect it empty.
- Host: `DDR2CharDriver.set_ref_align(offset)` (None = off).
  `TEST_REF_ALIGN=<offset>` in `pumice_char.run_matrix` and in the proxy
  (`test_granite_char_perf`). It is written only when set: an unconditional
  write would itself shift GO on every unaligned run.
- Proxy check (`_ref_align_probe`): on every launch, the reload fires at
  launch + offset + 1 and the countdown reads tREFI after it.

## 3. Proxy: the MC-024 GO-shift case

`test_granite_char_perf`, 100 MHz, `TEST_DUAL=1`, 4 generators, `mixed`
bl8, `TEST_TXN=512`, `open_page`, tREFI 781. Write / read MB/s; 0
mismatched on every run.

| alignment | extra `dir_mode = 0` write before GO | result |
|---|---|---|
| off (MC-024) | no | 300.3 / 506.7 |
| off (MC-024) | yes | 279.6 / 281.7 (GO moved) |
| offset 0 | no | 279.7 / 281.7, wr_cycles 46,862, rd_cycles 46,537 |
| offset 0 | yes | identical in every field |
| offset 200 | no | 302.2 / 580.0 (fast mode) |
| offset 400 | no | 279.8 / 281.9 |

With alignment on, the extra register write no longer changes the result,
and the offset selects the mode the way the tREFI phase did.

## 4. The 100 MHz bitstream

| build | placement | WNS | failing endpoints | LUT |
|---|---|---|---|---|
| A | default | -0.255 ns | 19 | |
| B | `PLACE_DIRECTIVE=ExtraTimingOpt` | **+0.001 ns** | 0 | 37,280 |

Build A's failures were 14 on MC-022's pick-core cone (`r_self_stale` /
`r_is_col` -> `r2_pair` / `r_win_cls`), past the band MC-022 recorded
(+0.003 .. -0.159), and 5 on the chargen read-back mux (`r_cmd_paddr` ->
`r_rsp_prdata`, worst -0.162, ~82 percent route). None of the failing paths
go through the reload logic. Build B is the board bitstream
(`ddr2_char_granite_sku100_mc025b_2026-11-24.bit`). This is placement noise
on MC-022's knife edge, not closure. A fallback if the read-back mux binds:
make `REF_ALIGN` write-only, which takes it out of the read mux.

## 5. Board repeatability at offset 0

Wr / rd cycle counts, every row, against a repeat of the same suite:

| suite | rows | rows that differ | mismatched |
|---|---|---|---|
| `windows` x3 (`sku100mc025a0`, `a0w2`, `a0w3`) | 9 | **0** | 0 |
| `every` x2 (`sku100mc025a0`, `a0e2`) | 68 | **0** | 0 |
| unaligned MC-024 `windows` x3, for comparison | 9 | 9 (-129 .. +322 cycles) | 0 |

Compare runs on `wr_cycles` / `rd_cycles`. The `util` columns divide by a
denominator taken from perf meters that the host freezes, so they jitter in
the fourth decimal even on cycle-identical runs.

> 2026-11-25 (MC-022): a rare one-cycle draw survives alignment. One row in
> 263 across the aligned runs so far wrote a cycle longer (`defaults
> row_major_bl4`, 269,754 vs 269,753). Filed as ISSUE-008; until it is found,
> treat a lone one-cycle difference on one row as noise and repeat it.

## 6. Offset sweeps: the spread, now on demand

`windows` at offsets 0 .. 700 (`sku100mc025a{0..700}_windows`), mixed_bl8 wr / rd:

| offset | `defaults` | `open_page` | `close_page` |
|---|---|---|---|
| 0, 100, 200, 400, 600 | 277 / 276 | 280 / 280 | 73 / 121 |
| 300, 500, 700 | 277 / 277 | **303 / 593 .. 594** | 73 / 121 |

`open_page` is in the fast mode at 3 of 8 offsets (unaligned it drew fast 2
of 20 times). `defaults` and `close_page` are one mode at every offset.

`every` under `bank_interleave` at offsets 0 .. 700
(`sku100mc025bi_a{0..700}_every`, 17 cells), wr / rd:

| cell | 0 | 100 | 200 | 300 | 400 | 500 | 600 | 700 |
|---|---|---|---|---|---|---|---|---|
| incremental_bl8 | 577/566 | 583/566 | 582/566 | 583/565 | 582/583 | 582/566 | 583/566 | 582/583 |
| row_major_bl4 | 519/566 | 580/582 | 582/566 | 583/582 | 581/582 | 582/566 | 583/566 | 583/583 |
| row_major_bl8 | 517/566 | 581/583 | 582/566 | 583/583 | 581/583 | 582/566 | 518/566 | 581/566 |
| row_major_bl16 | 517/565 | 582/583 | 583/565 | 583/583 | 583/583 | 582/583 | 583/565 | 582/583 |
| col_major_bl8 | 583/566 | 583/583 | 583/566 | 583/583 | 583/583 | 582/566 | 583/566 | 583/583 |
| col_major_bl4 | 443/516 | 443/516 | 445/516 | 433/516 | 442/518 | 445/516 | 443/516 | 443/516 |
| col_major_interleaved_bl4 | 356/361 | 356/361 | 356/361 | 356/361 | 356/361 | 356/361 | 356/361 | 355/361 |
| col_major_bl8_gap | 376/400 | 376/400 | 376/400 | 376/400 | 376/400 | 376/400 | 376/400 | 376/400 |

The CSVs have the rest; 0 mismatched on all 136 rows. ISSUE-007's three
levels (583 / 566 / ~518) all appear and are set by the offset. Each cell has
its own launch, so at one offset different cells sit at different levels.
The cells that are not row-hit streams (col_major_bl4, the interleaved bl4
walk, the gap cell) do not move.

## 7. How to use it

- **A/B a microarchitecture change:** run both arms at the same
  `TEST_REF_ALIGN`; the difference is the change, to the cycle.
- **Judge a change across refresh placement:** sweep the offsets (8 points
  over 0 .. 700 at tREFI 780 here) on both arms and compare per offset.
- **Leave it unset** to reproduce the free-running (product-like) draw.

## 8. Regressions (after `make clean-all`)

granite 29 passed; framework 228 passed; pumice 117 + 525 passed; scoria's
failures are its known stale unit TBs (`bank_timer`, `cmd_arbiter`,
`scheduler_plane`), none in a connected char macro.

fabric-benchmark passed 16 / 16 only after 3 reruns (`fb_harness[pulp-full]`
once, `[xbar-full]` twice). A no-rerun repeat failed both legs again on
`k3_2ch_4desc_64KB w4`: every byte moved (2048 AW / B / AR, 32,768 beats each
way), "the run timer never stopped". The cause is the harness, not MC-025:

- The STREAM runner's completion poll (`characterization.py`,
  `CHAR_POLL_TIMEOUT_S`, default 120 s) is host wall-clock, sized for the
  board. The full chain's two 64 KB workloads (162k cycles) take about 120 s
  of simulator wall time, so each run passes or times out depending on
  machine load. In the failing run the poll gave up at 120.0 s and the
  snapshot a few seconds later showed every channel idle.
- A three-tree bisect of that one chain (pulp, seed 20698, run concurrently):
  the working tree and HEAD~1 (no MC-025) passed, HEAD failed. A superset
  tree passing where its subset fails is a timing draw, not a code
  difference; the same seed also gave cycle counts differing by a few
  cycles between trees.
- Fix: `test_fb_harness` now sets `CHAR_POLL_TIMEOUT_S` 900 and
  `TB_MAX_DURATION_MIN` 120 for the simulation, as the STREAM monitor tests
  already do. The board budget is unchanged.
