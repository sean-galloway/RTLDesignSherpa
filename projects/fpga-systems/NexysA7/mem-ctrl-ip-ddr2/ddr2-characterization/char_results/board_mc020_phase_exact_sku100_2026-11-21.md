# The slot was not the tax: the one-CK phase margin in the host's JEDEC derivation was (memory-controllers MC-020), 2026-11-21

MC-020 was filed on the SKU model's `slot1` variant: a command slot every CK
gives `col_major` +14.6 / +9.5 / +5.3 percent, so the one-slot-per-MC-cycle
rule must be costing the single-bank RDA -> ACT -> RD chain, and the task
named two forms of an idle-slot row fire to recover it. Both forms were
priced, both gain nothing, and the thing `slot1` was measuring turned out to
be in the host, not the pick core. The recovered form is a host derivation
change, validated on the board the same day: **no RTL change.**

## 1. The two slot forms: 0.0

`GraniteSKU` gained `lane_idle` (1 = the lane also fires into a main slot
with no command, the live idle-slot fire MC-014 cut; 2 = the lane fires
alone one slot after a registered idle, the main's row winner yielding that
slot). On the `every` suite both are 0.0 against the SKU on every cell,
`col_major` included: on a one-bank chain the main slot fires the ACT the
slot its MC-cycle timer opens, and the lane has nothing to add. `slot1` on
the same (hybrid) model is +6.9 / +4.7 / +2.6 on `col_major` -- the model's
whole pipeline at CK granularity, including hops no RTL form can halve.

## 2. Where the CK went

The host derives the controller's MC-cycle timing CSRs
(`pumice_device.ddr2_timings_mc_cycles`) with a PHASE MARGIN of one CK on
every ns-derived minimum, because an MC-cycle counter cannot tell which of
the two DFI phases a command sits on. But the phases are fixed: RD / WR on
phase 0, every row command (ACT / PRE / REF) on `row_phase` 1 since the lane
build. A hop from a command on phase a to one on phase b of a later cycle m
cycles on is 2 m + (b - a) CK, so the count it needs is
ceil((n_ck - (b - a)) / 2), not ceil((n_ck + 1) / 2). tRTP already had this
(TASK-003); the rest did not. At 100 MHz on the SKU's phases:

| counter | margin | phase-exact | why |
|---|---|---|---|
| tRC | 7 | 6 | ACT -> ACT, same phase: 12 CK >= 60 ns |
| tWR (WR cmd -> PRE) | 4 | 3 | phase 0 -> phase 1: 2 x 3 + 1 = 7 CK = WL + BL/2 + 3 |
| tWTR | 4 | 3 | WR -> RD, same phase: 6 CK = WL + BL/2 + 2 |
| tRRD | 2 | 1 | ACT -> ACT, same phase: 2 CK >= 10 ns |
| tRFC | 14 | 13 | REF -> ACT, same phase: 26 CK >= 127.5 ns |
| tRCD, tRP, tRAS, tFAW, tRTP, tCCD, tRTW | - | unchanged | already exact on these phases, or PHY-bound |

`ddr2_timings_mc_cycles(phase_exact=True)` derives this when rd_phase,
wr_phase and row_phase are all known (any unknown keeps the margin);
`jedec_timings_for` reads the three phases back from DFI_PHASE and
`JEDEC_PHASE_EXACT=1` turns it on for the board flow, `TEST_PHASE_EXACT=1`
for the proxy. **The default is unchanged** (the margin): the SKU is the
configuration, and the host's default timings are part of it.

## 3. Priced, then checked at the CK

The model preset `DDR2_GRANITE_SKU100_PX` is the phase-exact set in CK
(`test_px_preset_is_the_phase_exact_host_derivation` pins it to the host
function and to the JEDEC minima on the SKU's phases); `sku_px` runs the SKU
on it. On the `all` suite: `col_major` writes 283 / 418 / 542 -> 312 / 448 /
568 (+10 / +7 / +5), reads 390 / 520 / 624 unmoved; everything else +0.1 to
+1.1; `mixed` 274 / 274 -> 310 / 571 (the fast mode at GO 0: the counters
move the race).

The proxy (the RTL), same directory, `TEST_PHASE_EXACT` 0 then 1, 4 generators:
every family up 0.4 to 1.2 percent, `mixed` into its fast mode, `mismatched`
0. One generator on one bank (the board's `col_major` shape): writes +11.1 /
+7.2 / +5.2 at AxLEN 4 / 8 / 16, reads -0.5 / -0.1 / -0.2, as the model said.

Legality: the controller's timers count MC cycles and the DRAM model's
checker compares CK counts at the wrong clock (tens of thousands of "soft
violations" on every run, demoted since 2026-10), so neither says whether a
stream is legal to the CK. The proxy's DRAM trace now carries each command's
DFI phase, and `bin/jedec_ck_check.py` checks CK = 2 x cycle + phase against
the part's minima, with an auto-precharge as a PRE at the DRAM's internal
close time: 208,121 commands of the phase-exact 4-generator run and the
three one-bank runs, **no violations** (nor on the margin runs). The phases
in the trace are what the derivation assumes: ACT and PRE on 1, RD / WR / AP
on 0.

## 4. The board

The step-5 bitstream (HEAD's RTL), `JEDEC_PHASE_EXACT=1`. Smoke: init PASS,
write_read PASS, memtest PASS 32 / 32 chunks over 128 MB -- at tWR 4, not 3:
the smoke's `A7Leveling` derives its timings before the DFI phase is
programmed and read `row_phase` 0, which is the conservative side (legal; a
derivation-order tidy, noted below). The char configs program the phases
first and derived the full set (`tRC=6 tWR=3 tRRD=1 tRFC=13 tWTR=3`).
`--profile windows` 9 cells and `--profile every` 72 runs: **0 mismatched
beats in every cell** (`char_granite_sku100px_{windows,every}_2026-11-21.csv`).

Against the step-5 margin run on the same bitstream
(`compare_board_sku100px_vs_sku100s4_2026-11-21.md`, 77 cells, 48 moved by a
percent or more):

| preset | cells | margin | phase-exact | delta |
|---|---|---|---|---|
| defaults / open_page | row hits, col_major_interleaved, row_thrash, random | 765-778 / 762-778 | 768-777 / 766-779 | +0.1 .. +0.7 % |
| defaults / open_page | col_major bl4 / 8 / 16 | 283 / 389, 416 / 520, 541 / 623 | 311 / 389, 446 / 520, 565 / 623 | **+10.1 / 0, +7.1 / 0, +4.5 / 0** (the model's 312 / 390, 448 / 521, 568 / 627) |
| defaults | mixed_bl8 | 272 / 273 | 277 / 276 | +1.6 / +1.3 (one mode) |
| open_page | mixed_bl8 | 311 / 522 (a fast-mode run) | 280 / 280 (a slow-mode run) | the mode, not the counters |
| close_page | single-bank cells (9) | 78-82 / 87-92 | 87-92 / 87-93 | **+11 .. +12.6 / 0** |
| close_page | col_major_interleaved bl4 / 8 / 16 | 386 / 387, 250 / 361, 171 / 238 | 534 / 574, 344 / 402, 232 / 246 | **+38 / +48, +38 / +11, +36 / +3** |
| close_page | row_thrash, random, mixed | 238 / 314, 203 / 258, 56 / 59 | 344 / 351, 270 / 281, 60 / 66 | +45 / +12, +33 / +9, +7 / +11 |
| bank_interleave | 15 of 17 cells | 387 / 387 | 583 / 583 (566 on some read sides) | **+50 %** |
| bank_interleave | col_major_bl4, col_major_interleaved_bl4 | 283 / 388, 243 / 317 | 442 / 442, 356 / 356 | +56 / +14, +47 / +12 |
| any | col_major_bl8_gap | 376 / 400 | 376 / 400 | 0 (gap-bound) |

The two close-page presets are where the margin lived: every column closes,
so every column is an ACT, and tRRD 2 -> 1 doubles the ACT rate a
bank-interleaved stream can sustain -- the `bank_interleave` preset goes from
387 to 583 MB/s on fifteen of seventeen cells. The open-page SKU gains the
col_major write chain (WRA -> ACT 6 -> 5 MC) and half a percent elsewhere.

## 5. The model at the phase-exact counters: 51 in / 6 out, and what the six are

`compare_model_sku_vs_board_sku100px_px_2026-11-21.md` (the model on
`DDR2_GRANITE_SKU100_PX`, one board run per cell). Three of the six are the
mixed cells' modes (the model fast at GO 0 on `defaults` and `open_page`,
the board slow this run; `close_page mixed` +21 on the union). The other three
and a systematic drift inside tolerance are one thing: the model's preset
takes the auto-precharge path's ACT at the CK-exact distance (ras 9 + rp 3 =
12 CK = 6 MC from the ACT), where the RTL still sequences its two MC
counters -- tRAS 5 then the SAME tRP 2 -- for 7. So the model's close-page
reads (ACT -> RDA -> self-close -> ACT) are +12 .. +14 over the board's
(93 / 105, 87 / 97 ...), and `bank_interleave col_major_bl4` reads 520
against 442, `col_major_interleaved_bl4` 402 against 356,
`row_major_bl16` write 585 against a board 521 that its neighbours (583)
say is a mode or a draw. The board's close-page READ sides did not move at
all with the counters (92 -> 93, 361 -> 402 is the interleave's ACT rate),
which is the same fact from the other side.

That is MC-020's one remaining RTL item, and it is small: the bank timer's
auto-precharge self-close already loads a distinct value (`ld_rp1_i`,
f_ld(t_rp, 1)) -- give it its own CSR field, derived as the exact distance
from the DRAM's internal close to an ACT on row_phase. Per path: after an
RDA the internal close is at RD + 2 CK and the ACT may follow at + 3; after a
WRA at WR + 7 CK (tWR 3 MC is 6, the phase gives the 7th), so the write path
needs rp_ap 2 where the read path needs 1 -- two fields (RD / WR), or one at
2 and no read gain. The model prices the read gain at +12 .. +14 on every
close-page cell and +13 .. +17 on the two bank_interleave bl4 cells.

## 6. Decisions and record

- Owner's: adopt the phase-exact derivation as the host's default (every
  board number of the SKU's close-page presets moves by +35 .. +50 percent,
  the open-page ones by under one), or keep it behind `JEDEC_PHASE_EXACT=1`.
  The 81-cell board run and the memtest are the data; a soak at the new
  counters is the one check not run.
- Owner's: the auto-precharge tRP as its own CSR field (section 5), the RTL
  step this task would take next.
- A tidy: `A7Leveling` / `PumiceMaster` derive their JEDEC set at construction,
  before `program_geometry` sets the DFI phases, so the smoke runs the
  margin-side tWR under `JEDEC_PHASE_EXACT`; derive after the phases are
  programmed.
- Files: `pumice_device.py` (`phase_exact`, `wr_phase`, `get_dfi_phase` with
  row_phase), `ddr2_char.py` (the phases read back, `JEDEC_PHASE_EXACT`),
  `test_granite_char_perf.py` (`TEST_PHASE_EXACT`, the phase in the DRAM
  trace), `bin/jedec_ck_check.py`, the model (`lane_idle`, `sku_laneidle`,
  `sku_laneidle_reg`, `sku_px`, `DDR2_GRANITE_SKU100_PX`,
  `GRANITE_TIMING_PRESET`), the model CSVs `model_ramulator2_ddr2_granite_sku100{,_open,_bi,_close}_px_2026-11-21.csv`
  and the open config's GO-480 run, the board CSVs, the two compares.
