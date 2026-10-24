# TASK-053: DFI plane -- the clock-domain crossing is a generate (DFI_CDC_EN); same-clock form for the DDR2 boards

> Source: owner, 2026-10-24, on the per-plane area table of report 5.12:
> "it seems like the dfi-plane cdc cells should be a generate thing (cdc on)
> otherwise skip the cdc fifos." Both Nexys A7 macros tie dfi_clk to mc_clk
> (granite_char_macro line 367, ddr2_char_macro line 538), so every one of
> the five Gray-pointer async FIFOs in mc_dfi_cdc crossed between one clock
> and itself. Related: TASK-052 (the area table), handbook `design/cdc.md`.

**Priority:** P2
**Status:** closed 2026-10-24 (board +0.367 ns, 0 failing endpoints; granite_core 6 105 -> 6 090 LUT, 4 572 -> 4 417 FF; reads 6 cycles shorter per burst, writes cycle-identical; the async form byte-identical in behaviour, formal PASS)
**Owner:** TBD

## What landed

- **`mc_dfi_cdc` parameter `DFI_CDC_EN`** (default 1). 1 = the existing
  five `gaxi_fifo_async` crossings, untouched inside `g_async`. 0 =
  `g_sync`: the same four data / token FIFOs as `gaxi_fifo_sync` at the
  same depths (they still decouple the scheduler from the command path's
  hold, stage write bursts ahead of their WR, and absorb read return), the
  init_start / init_complete tokens as plain sticky levels. Same ports,
  same data / staged-token coupling (`wd_ready = data_ready && tok_ready`),
  so the write-staged invariant holds as before. Legal only when the two
  clock inputs are one net; the header says so. `mc_dfi_cdc.f` gained the
  sync FIFO's closure.
- **Plumbed** through `mc_dfi_2p1_plane` / `3p1` / `4p0` (default 1),
  `granite_core`, `pumice_core`, `pumice_top`, `pumice_top_geared`,
  `granite_top_geared` (default 1), and the granite board chain: the char
  macro and harness default **0** (the macro is where the clocks are tied),
  `granite_char_top` honours `GRANITE_DFI_CDC_EN`, the UART tb top and the
  perf proxy default 0 (`TEST_DFI_CDC_EN`), both `create_project.tcl` hooks.
  The component suites keep 1: `test_granite_core` / `test_granite_top_geared`
  drive dfi_clk at twice aclk (6.67 vs 13.34 ns, `board_clock_periods`), so
  only the async form is legal there; the whole-harness proxy is the sim
  that matches the board.

## Measured

| | async crossing (TASK-052 text) | same clock, `DFI_CDC_EN = 0` |
|---|---|---|
| granite_core, board (LUT / FF) | 6 105 / 4 572 | 6 090 / 4 417 |
| u_dfi_plane / u_cdc, board | 397 / 332, 347 / 210 | 353 / 177, 304 / 55 |
| WNS at 75 MHz | +0.268 ns | +0.367 ns, 0 / 109 139 |
| granite_core, ASAP7 (comb cells / flops) | 24 337 / 4 699 | 24 078 / 4 525 |
| u_cdc, ASAP7 | 560 / 228 | 304 / 54 |
| proxy, 1 thread, rd cycles (inc / row_major / col_ilv / col_major) | 2 165 / 2 147 / 2 723 / 3 435 | 2 159 / 2 141 / 2 717 / 3 429 |
| proxy, 1 thread, wr cycles | 2 162 / 2 131 / 2 666 / 3 949 | identical |
| proxy, 8 threads std / random / mixed / 2-beat row_thrash | grid | std 8 threads: wr identical, rd 557.4 / 557.4 / 543.8 / 458.4 vs grid 555.3 / 557.2 / 525.9 / 457.7 (col_ilv reads +3.4 percent) / random 8 threads: 442.1 / 453.0 (grid 442.1 / 452.9), rd 21 697 cycles (was 21 703) / mixed 8 threads: 98.1 (grid 98.1), 200290 / 200293 cycles (was 200290 / 200299) / row_thrash 2-beat: 128.7 / 163.4, rd 1 880 cycles (was 1 886) |

**The lesson is in the second row.** The crossing's pointer logic was never
the FPGA cost: the five FIFOs' synchronizers and Gray counters are 43 LUT
and 155 FF; the other 300 LUT of u_cdc are the FIFO storage (rd 32 x 67,
wd 32 x 73, cmd 8 x 34 bits) as LUTRAM, and the depths did not change.
On ASAP7, where every pointer flop and gate is a cell, the same change is
half of u_cdc. The next DFI lever is the depths in the same-clock form:
the read FIFO is sized to the whole read-return window (`RD_RET_DEPTH x
BURST_WORDS`) for a consumer that may never deassert ready, and the write
FIFO to 32 words for a burst that leads its command by `CMD_DELAY_EFF`
cycles. A measured lane, not done here.

Reads shorten by six cycles per family at one thread: the crossing's
N_FLOP_CROSS + 1 in each direction, as predicted. Bandwidth moves by 0.2 to
0.6 MB/s. The crossing-on cell (`TEST_DFI_CDC_EN = 1`) reproduces the
committed grid to the cycle, so the async branch is unchanged.

## Gates

granite suite 6 / 1 xfailed (async form, two test clocks); pumice
`run-all-func-both` 218 / 218 both geometries; andesite `dfi_plane_smoke` 1 / 1 and scoria `test_scoria_core` 4 / 4 after the
pin fix; formal `mc_common/mc_dfi_cdc` prove + cover PASS (async
form); lint 0 errors: granite_core and pumice_core at both values, the
whole granite harness at both values, scoria_core and andesite_core (3p1
and 4p0 planes carry the parameter). Board md5 == working text.

**Found and fixed on the way:** the scoria and andesite DFI planes had not
built since e95df1694 (2026-10-15) added `rd_ret_busy_o` to the read
aligner without connecting it in `mc_dfi_3p1_plane` / `mc_dfi_4p0_plane`
(fatal PINMISSING in every test that elaborates them). Tied off with a note
that the 2p1 plane exports it to the core's return window and these two do
not carry that window yet. After the fix: andesite `dfi_plane_smoke` 1 / 1,
scoria `test_scoria_core` 4 / 4. Still failing and not this change: scoria
bank-timer (8 cells) and scheduler-plane (14), andesite scheduler-plane
(10), all on timing checks with no DFI in their closure; left to those lanes.
