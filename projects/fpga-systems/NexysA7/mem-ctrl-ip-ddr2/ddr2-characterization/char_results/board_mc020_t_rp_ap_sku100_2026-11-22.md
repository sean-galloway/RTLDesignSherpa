# The auto-precharge tRP as its own field per column path (memory-controllers MC-020 decision 2), 2026-11-22

The RTL step MC-020 left to the owner after decision 1: the bank timer's
auto-precharge self-close reloaded the explicit PRE's tRP, so on the
phase-exact counters the one-bank chain ACT -> RDA -> ACT paid tRAS 5 + tRP 2
= 7 MC where the CK-exact distance is 6 (tRC), and every close-page read side
sat 12 .. 15 percent under the model. The owner's instruction was the
recommended order: the RTL's sequencing into the model first, so the compare
is honest; then the field, priced as a variant; then the RTL, the host and
the board.

## 1. The term: the model took the DRAM's distance where the RTL sequences counters

The SKU model's auto-precharge path was the DRAM spec's RDA / WRA -> ACT term
(BL/2 + tRTP - 2 + tRP, WL + BL/2 + tWR + tRP CK). The RTL's bank timer
(`mc_bank_timer.sv`) fires the self-close the MC cycle both its counters reach
zero -- tRAS from the ACT, tRTP / tWR from the column -- and reloads tRP for the
ACT: `ap_seq` in `granite_sku_controller.cpp` is that sequence, in slot units
(the lane's odd-tick ACT counts in its slot, as the RTL's counters do), with
the reload value a knob per path, `t_rp_ap_rd` / `t_rp_ap_wr`. The bank
counters it sequences are the host's on the SKU's phases (a column -> row-phase
hop is ceil((n - 1) / 2) with the lane on): tRAS 5, tRTP 1, tWR 3 at the
phase-exact preset, tWR 4 at the margin's.

- The term OFF (`sku_noapseq`) reproduces the morning's four CSVs cell for
  cell: 60 / 60 identical (`model_ramulator2_ddr2_granite_sku100*_pxd_2026-11-22.csv`).
- The term ON at the RTL's shared tRP (`sku_rpshared`, 2 / 2; run on the four
  SKU configs with `GRANITE_SKU_PARAMS="t_rp_ap_rd=2,t_rp_ap_wr=2"`) against
  the morning's board baseline (`sku100pxd`, windows x3 + every):
  **55 in / 2 out** of 57, from 51 / 6 with no RTL change
  (`compare_model_sku_rpshared_vs_board_sku100pxd_2026-11-22.md`). The two
  auto-precharge cells land: bank_interleave col_major_bl4 446 / 446 against
  the board's 445 / 442, col_major_interleaved_bl4 355 / 358 against 356 / 356;
  close_page col_major_bl4 92 / 92 against 92 / 92, row_thrash 349 / 352
  against 344 / 344. And two of the three cells filed under the direction
  register's modes were this term: `defaults mixed_bl8` 290 / 343 (union 581)
  against the board's 553 x3 (in at +5), `close_page mixed_bl8` 60 / 66
  against 60 / 66 x3 (exact). Left out: `open_page mixed_bl8` (the model fast
  at both GO phases, 617, the board slow x3, 559: ISSUE-005, which stands) and
  `bank_interleave row_major_bl4` (the board's per-pass level 519 / 566 on
  that run: ISSUE-007).
- The field as the host derives it (`t_rp_ap_rd` 1, `t_rp_ap_wr` 2, the SKU
  config's default from this commit): the prediction for the RTL step,
  `compare_model_sku_vs_board_sku100pxd_rpap_pred_2026-11-22.md`, 51 / 6
  against the shared-tRP board as it must be. It prices the read sides of
  every close-page cell +11 .. +15 percent (row_major_bl16 87 -> 97,
  col_major_bl4 92 -> 105, row_thrash 344 -> 395, random 281 -> 311), the two
  bank_interleave bl4 reads +13 / +18 (356 -> 402, 442 -> 520), the
  `defaults` mixed union 581 -> 619 and the `close_page` mixed union 120 ->
  146; the open-page col_major chain is tRAS-bound (5 + 1 = 6 = tRC) and does
  not move.

## 2. The derivation

`pumice_device.ddr2_timings_mc_cycles` carries `tRP_AP_RD` / `tRP_AP_WR`. The
DRAM starts its internal precharge at the CK the column's recovery (or tRAS)
ends and takes the next ACT nRP CK later; the RTL's fire counter lands in the
MC cycle of that close, so the reload is the hop from that cycle to an ACT on
the row phase, less the counter that fired, per path (the read's close is BL/2
+ tRTP - 2 CK after the RD, the write's WL + BL/2 + tWR after the WR), each
the larger of its column-bound and tRAS-bound case. At 100 MHz on phases
0 / 0 / 1: RD 1, WR 2 (the RDA's close at RD + 2 CK = the fire cycle's phase
0, the ACT 3 CK later on phase 1 of the next cycle; the WRA's close at WR +
7 CK = the fire cycle's phase 1, the ACT 3 CK later two cycles on). Under the
margin both are tRP (5 + 2 is the margin tRC 7 already). At row_phase 0 (the
lane off) RD 2, WR 1. `set_jedec_timings` programs `TIMINGS_RP_AP` where the
regmap has it and skips the group on pumice. Pinned in
`test_pumice_device.py` and against the model config in `test_char_model.py`.

## 3. The RTL

- `mc_bank_timer.sv`: the self-close reloads `ld_rp1_rd_i` or `ld_rp1_wr_i`
  by the pending column's direction (`r_ap_wr`, set with `r_ap_pending`); the
  LA_AP lookahead sum takes the path's tRP (`t_rp_ap_rd_i` / `t_rp_ap_wr_i`
  replace `t_rp_i`); in the ZF_REG form the counters' own sum is registered
  once per path and selected at the read by the flop, so the D inputs stay
  register-only.
- `mc_bank_timers.sv`: `t_rp_ap_rd_i` / `t_rp_ap_wr_i` in, the two `f_ld(t, 1)`
  reloads and the two sums registered once for every bank.
- `mc_scheduler_plane.sv`: the two ports through to the timers (the fast-release
  scan does not take them: a legal set has each at most tRC - tRAS).
- `granite_core.sv` / `granite_top_geared.sv`: from `TIMINGS_RP_AP`
  (`granite_csr.rdl` @ 0x050 -- 0x078 / 0x07C are documented holes; reset 15
  = tRP's reset, so an unprogrammed register is the shared tRP); FIXED_TIMINGS
  builds use T_RP for both. Regenerated through `bin/peakrdl_generate.py`.
- `pumice_core.sv`, `scoria_scheduler_plane.sv`, `andesite_scheduler_plane.sv`:
  both tied to `t_rp_i` (no register; the behaviour before).
- The granite core tests (`test_granite_core.py`, the two bankfifo tests)
  drive the two ports at 2: they drive the timing ports by name, and a new
  port is undriven (0) until they do.

## 4. Formal (`formal/mc_common/mc_bank_timer`, clean first)

The golden copy carries the same per-path reload in its live-compare form with
a dated note (with both fields at tRP it is the 821b5c164 form exactly). The
prove harness gained `t_rp_ap_rd` / `t_rp_ap_wr` free of `t_rp` (1..4), the
assertion `a_trp_ap` (no ACT within the armed path's tRP_AP of the self-close's
fire) and the covers `c_trp_ap_rd_exact` / `c_trp_ap_wr_exact` /
`c_trp_ap_differ` (the ACT permitted exactly at N with the field apart from
tRP, both paths); the equiv harness the two free fields and `c_ap_rp_rd`.

| task | result |
|---|---|
| prove (bmc 22) | PASS |
| cover | PASS, 11 / 11 reached (the three new in step 6) |
| equiv (ZF_REG against the gold, SET_LAG 1, bmc 40) | PASS |
| equiv_live (SET_LAG 0) | PASS |
| mutation: the write path reloading the read path's value | `a_trp_ap` FAILS at step 6 (the flat rebuilt; a first run on the stale flat "passed" -- see the handbook) |

Two harness notes: `a_trp_ap`'s counter had to be seeded from the fire cycle
(ap_pending with preblk and ras at zero), not from the drop of ap_pending one
cycle later, or the window is one short (it failed at t = 2 as written first).
And the Makefile's prove / cover targets now depend on the golden flat, which
`bank_timer.sby` lists for every task (a clean tree ran them first and failed
on the missing file).

## 5. The sys100 build does not close under the budget, on the fire cone, twice

`GRANITE_SYS_100=1 make bitstream` on this RTL, the flow's default placement
(AltSpreadLogic_high / Explore) and a second (PLACE_DIRECTIVE=ExtraTimingOpt),
both under the 0.2 ns setup uncertainty the owner budgets (0.280 ns
effective with the clock's own jitter):

| build | WNS | failing endpoints | LUT / FF | the paths |
|---|---|---|---|---|
| A (default placement) | **-0.052 ns** | 15 | 37,387 / 32,972 | pick select: `r_req` -> `r2_cls` / `r2_pair`, `r_is_col` -> `r_win_cls`, `r_win_pair` -> `r_self_stale`; store: the head record's `hit` -> a bank queue's RAM WE (x8) and the page policy's idle CE |
| B (ExtraTimingOpt) | **-0.054 ns** | 25 | 37,387 / 32,972 | pick select: `r_req` -> `r2_pair`; `u_bank_timers/r_wr_le1` (the CSR-derived `t_wr <= 1` flag) -> the DFI CDC command FIFO's RAM WE (x24, three RAM slices) |
| the step-5 build (2026-11-19) | +0.080 | 0 | 37,389 / 32,926 | |
| the report in the tree this morning | +0.014 | 0 | | |

None of the failing paths is in the changed logic (the 200 worst paths carry
no `r_ap_wr`, `r_ap_le`, `ld_rp1` or `rp_ap` cell); they are the design's
fire cone -- the pick core's select stage and the store's fire -> pop -- which
sat at +0.014 .. +0.080 across the last builds, and the change's 46 flops
(the per-bank `r_ap_wr` and the second registered sum, the two derived
reloads and the register) moved its placement by about 0.065 ns the wrong
way on both directives. Build B's second class is the CSR-derived flag the
bank timers register once (MC-007): static during traffic by the same
contract the TIMINGS_* false paths rest on, but not in the XDC's false-path
set (the registered copies are one flop downstream of `field_storage_reg`).

By the owner's rule (2026-11-08: WNS near zero is placement noise, not
closure; the budget is the 0.2 ns; fix structurally when it fails) this RTL
has NOT closed at 100 MHz: two of two placements fail by 50 ps, where the
RTL before it passed by 14 and 80. That is the owner's decision 3 (section 7).
The board runs below are on build A, labelled as such -- 52 ps under a 280 ps
uncertainty is a bitstream that runs, and the data on the field's effect does
not depend on which placement ships -- and they are not the SKU's record.

## 5b. Build C: the bank timers' CSR-derived registers false-pathed, and the build closes by two picoseconds

The owner's "continue" (2026-11-22, later). The XDC's false-path set was
extended to every register directly in `u_bank_timers` -- the TIMINGS_*
derivatives the block registers once for all banks (`r_ld_*`, `r_*_le1`,
`r_*_la`, `r_*_w1`, `r_t_rp_ap_*`; MC-007 row 6), one flop downstream of
`field_storage_reg` and static under the same idle-write contract the owner
accepted for the TIMINGS_* false paths on 2026-10-31 (the per-bank counters
below them in `g_bank[*].u_bt` stay timed). The default placement with it:

| build | WNS | failing endpoints | LUT / FF | worst path |
|---|---|---|---|---|
| C (default placement + the false path) | **+0.002 ns** | **0** | 37,320 / 32,962 | `u_bank_pick/r_is_col_reg[15]` -> `r_win_cls_reg[0]` (the main select) |

Closed by the rule -- WNS >= 0 under the 0.2 ns budget, zero failing
endpoints -- and the knife edge the rule's own text warns about ("a design
that lands at zero here has no margin and the fix is structural, not another
placement"): the pick select is the worst path at +2 ps. So the SKU bitstream
with the field is build C
(`fpga/bitstream/ddr2_char_granite_sku100_mc020d2c_2026-11-22.bit`), the
board record below is re-taken on it (section 6c), and the structural item
is filed as **memory-controllers MC-022** with the three path classes of
builds A and B, the candidates to price in the model first (an exact rotor
restructuring, the pop a cycle after the fire, a request-stage split), and the
XDC's own record that floorplanning this cone made it worse three times.
Floorplanning and directive sweeps are how the band is measured, not closed.

## 6. The board on build A: the field pays where the chain is column-bound, not where it is tRAS-bound

Nexys A7-100T, build A (`fpga/bitstream/ddr2_char_granite_sku100_mc020d2_2026-11-22.bit`,
WNS -0.052 under the budget, section 5), the host default (`TIMINGS_RP_AP`
programmed 1 / 2 by the char configs, 2 / 1 by the smoke at the reset state's
row phase 0 -- the init log shows both). Smoke: init PASS, write_read PASS,
memtest PASS 32 / 32 chunks over 128 MB. Char: `windows` x3 (9 cells, the
three runs identical to the decimal, 0 mismatched), `every` x1 (68 cells, 0
mismatched): `char_granite_sku100rpapA{,w2,w3}_windows_2026-11-22.csv`,
`char_granite_sku100rpapA_every_2026-11-22.csv`.

Against the morning's baseline (`sku100pxd`, the same RTL without the field,
the shared tRP), 54 of 68 cells within one percent; what moved:

| preset | cell | board before (wr / rd) | board with the field | model predicted | read |
|---|---|---|---|---|---|
| close_page | mixed_bl8 | 60 / 66 (union 120) x3 | **73 / 121 (union 146)** x3 | 73 / 121 (146) | +21 percent on the union, exactly the prediction |
| bank_interleave | col_major_bl4 | 445 / 442 | 442 / **516** | 446 / 520 | +17 percent read, the prediction |
| bank_interleave | col_major_interleaved_bl4 | 356 / 356 | 356 / 361 | 355 / 402 | +1 where the model said +13 |
| close_page | col_major_bl4 | 92 / 92 | 92 / 95 | 92 / 105 | +3 where the model said +14 |
| close_page | col_major_bl8 (and gap, multiid) | 89 / 89 | 89 / 91 | | +1.5 |
| close_page | row_thrash_bl8 | 344 / 344 x3 | 344 / 354 x3 | 349 / 395 | +3 where the model said +15 |
| close_page | random_bl8 | 270 / 281 x3 | 270 / 283 x3 | 272 / 311 | +1 where the model said +11 |
| bank_interleave | the per-pass levels (row_major_bl4/8/16, col_major_bl8/16, incremental, multiid) | 583 / 566 / 519 | 583 / 566 / 518, other cells | | ISSUE-007's draw, as every run |
| defaults, open_page | every cell | | unmoved (0.0 .. 0.1) | unmoved | the open-page col_major chain is tRAS-bound: 5 + 1 = 6 = tRC either way |

The model's prediction against this board: **52 in / 5 out**
(`compare_model_sku_vs_board_sku100rpapA_2026-11-22.md`): the two mixed
modes (ISSUE-005 -- `defaults` 553 x3 and `open_page` 559 x3 slow on the
board, the model fast on both GO phases) and two ISSUE-007 draws, plus one
cell the field was priced for and did not deliver: `bank_interleave
col_major_interleaved_bl4` (+11.5). The close-page read sides it priced at
+11 .. +15 are IN only by the family's 15 percent tolerance: the board gave 1
.. 3.

So the field does what it was derived for exactly where the next ACT's
request is already armed when the self-close fires -- the bank_interleave
col_major_bl4 chain (the next column is a different bank's, and its ACT waits
on the closed bank's tRP alone) and the close_page mixed cell -- and nearly
nothing where the next head is the same bank's: close_page col_major (the
same row, re-opened after its own auto-precharge) and the multi-bank
close-page streams (row_thrash, random, the bl4 interleave) where the head
behind the fired column is the same bank's next row. On those the one MC
cycle the field removes from the timer is spent again in the pick pipeline:
the head's ACT request is not armed until the bank's row image clears at the
fire + 1 and the record and the request register follow, so the ACT lands
where it did. The model takes the request as armed by the lookahead (the
LA_AP term) or at the timer (`same_row`, no lookahead) and so prices the full
cycle. That is the model's next term -- the auto-precharge close's row-image
path, the `close_lag` the explicit PRE already carries (MC-021 step 8), on
the self-close -- measured on the proxy below before it is written.

## 6b. The proxy, cycle for cycle: where the field's slot goes

The proxy (the framework's `test_granite_char_perf`, `TEST_PAGE_POLICY=2`, 100
MHz, lane on) on three close-page cells with the field (the host default,
1 / 2) and with the shared tRP (`JEDEC_OVERRIDE="tRP_AP_RD=2,tRP_AP_WR=2"`),
the DRAM trace of each through `bin/jedec_ck_check.py`:

| cell | proxy, shared (wr / rd) | proxy, field | board, shared -> field | CK check |
|---|---|---|---|---|
| col_major_bl4, one generator | 91.2 / 91.3 | 91.2 / 94.6 | 92 / 92 -> 92 / 95 | 24,667 / 24,625 commands, no violation |
| row_thrash_bl8 | 343.6 / 349.2 | 343.6 / 353.0 | 344 / 344 -> 344 / 354 | 197,313 / 197,037, none |
| random_bl8 | 268.6 / 265.3 | 268.6 / 267.4 | 270 / 281 -> 270 / 283 | 197,069 / 197,071, none |

The proxy is the board to a percent on every cell both ways, and the traces
say why the field moves so little (`spacing.py` over the trace: the same
bank's ACT -> ACT in MC cycles, and the self-close's fire -- max(ACT + 5, RD + 1
/ WR + 3), the RTL's counters -- to the bank's next ACT):

- col_major_bl4, shared: ACT -> ACT **9** on 6,081 chains, 7 on 2,028; fire ->
  ACT 4 on 6,081 (RD and WR alike), 2 on 2,028. With the field: 9 on 6,053, **6
  on 1,023, 7 on 1,014**; fire -> ACT 4 on 6,053, **1 on 1,023 (RD), 2 on 1,014
  (WR)**. Every self-close here is tRAS-bound (the RDA at ACT + 2 closes at RD
  + 1 = ACT + 3, before tRAS at ACT + 5).
- row_thrash_bl8, field: 9 on 59,039 of ~65,700 chains; fire -> ACT 4 on
  59,039, 1 on 2,142, 2 / 3 / 5 on ~3,000. Shared: 9 on 60,262, fire -> ACT 4
  on 60,262, 2 on 2,986.
- random_bl8: the same shape, 9 on 53,400 of 65,700 either way.

So on nine of ten same-bank chains the next ACT lands FOUR cycles after the
self-close fires whether the timer reopens the bank at one (the field) or two
(the shared tRP): the head's class only turns to ACT when the bank's row image
clears, the cycle after the fire, and the record and the request register
follow -- the pipeline MC-021 measured as `close_lag` on an explicit PRE,
here on the self-close, with no PRE -> ACT hint to arm it. The field pays only
on the chains the pipeline had already armed (the one in FOUR that take the
exact 6 -- positions 3 and 7 of every eight columns, the chain after the last
column of each four-column AXI burst -- and the 2,142 of 65,700 in
row_thrash), and in full where the next ACT
is another bank's whose request was up before the close (bank_interleave
col_major_bl4, the mixed cells). The cycle the field removes from the timer is
real -- the trace's 1,023 chains at exactly tRC say so -- but the pick
pipeline spends it again on the rest.

The model with the field priced the full cycle because its decode sees the
head as an ACT candidate from the RDA's issue (Ramulator closes the bank at
the issue) and requests it at the timer (`same_row`, no lookahead) or ahead
of it (`pick_la`): the honest term is the self-close through the record's hit
path, with whatever arms the fourth chain. Two probes, both left in the
controller off by default: a flat decode gate from the fire (`ap_close_lag`)
does not reproduce the mixture -- 1 slot gives 97 / 390 / 307 against the
board's 95 / 354 / 283 (+3 / +10 / +8), 2 slots 87 / 347 / 277 (-8 / -2 /
-2); and the hypothesis "the heads present at the fire take the close_lag
path, a head landing after it takes the lookahead" (`ap_close_rec`) gives 87 /
348 / 277 with the field AND with the shared tRP, i.e. four cycles on every
chain -- so the next burst's head is already queued when the close fires and
something else arms it (the burst boundary in the store's two-head record is
the candidate). That measurement is the next model step; until it lands the
model with the field is +11 .. +15 optimistic on these cells.

## 6c. The board on build C, the SKU bitstream

The same host, build C programmed. Smoke: init PASS, write_read PASS, memtest
PASS 32 / 32 chunks over 128 MB. Char: `windows` x3 + `every` x1, 95 cells,
**0 mismatched beats** (`char_granite_sku100rpap{,w2,w3}_windows_2026-11-22.csv`,
`char_granite_sku100rpap_every_2026-11-22.csv` -- the SKU's record; build A's
`sku100rpapA` set stays as the unclosed bitstream's). Against build A: 64 of
68 `every` cells within one percent; the four that moved are bank_interleave
per-pass levels trading places between 583 / 566 / 518 (ISSUE-007's draw,
as on every run). The windows runs: identical to build A's to the decimal on
eight of nine cells each run; `open_page mixed_bl8` took its fast mode on the
third run (303 / 594, the 2026-11-22 morning's one-in-three), slow on the
other two (280 / 280) -- ISSUE-005's modes, unchanged by the field.

The model (the field, `rpap`) against build C: **54 in / 3 out**
(`compare_model_sku_vs_board_sku100rpap_2026-11-22.md`): the two ISSUE-005
mode cells and `bank_interleave col_major_interleaved_bl4` (board 361, model
402 -- the field's one undelivered cell, section 6b). The close-page read
sides the model over-prices by 11 .. 15 are IN by the family's 15 tolerance.

## 7. Decisions and record

Decision 2 is built, proved, measured, and lands at the owner's third decision:

- **Done.** The field exists end to end: `TIMINGS_RP_AP` (0x050, reset =
  tRP's), the bank timer's per-path reload with the equivalence and the
  spacing proof, the host deriving and programming it (1 / 2 at the SKU's
  point, the shared tRP under the margin and on pumice), the model's
  sequenced self-close as a term (55 / 2 against the morning's board with no
  RTL change) and the field as its default. Every regression at its baseline
  (section 8), the board with 0 mismatched beats on 95 cells and the memtest,
  every proxy trace legal at the CK.
- **What it bought on the board**: close_page mixed_bl8 +21 percent on the
  union (exactly the prediction), bank_interleave col_major_bl4 read +17
  (the prediction); +1 .. +3 on the other close-page read sides, where the
  model had priced +11 .. +15, for the reason in 6b. The shipped `defaults`
  preset does not move (its chain is tRAS-bound). The RTL's cost: 46 flops
  (the per-bank direction flop and second registered sum, the two reloads and
  the register) and one mux on the reload.
- **The SKU bitstream: build C, closed by the rule at +2 ps** (section 5b),
  after builds A and B missed the budget by 52 and 54 ps on the fire cone
  (section 5) and the owner's "continue". The margin item is MC-022. What
  the three options were before build C:
  1. a structural item on the fire cone -- the pick core's select stage
     (`r_req` -> `r2_cls` / `r2_pair`, `r_is_col` -> `r_win_cls`) and the
     store's head-hit -> queue-pop -- as its own task, after which this RTL
     ships: filed as memory-controllers MC-022 (the owner's "continue"), with
     the candidates priced in the model first and the note that an exact
     rotor restructuring alone cannot close it (the store class is untouched
     by it); or
  2. ship without the field in the SKU: revert the RTL step (the host's
     derivation and the model term stay -- they are correct about the RTL
     either way) and record the +21 / +17 as the price of the knife edge; or
  3. the false-path set extended to the bank timers' CSR-derived registers
     (`r_wr_le1` and its siblings, static by the same contract the TIMINGS_*
     false paths rest on), which takes build B's second class out but not the
     pick-select paths of either build -- not closure on its own. Done in the
     XDC on 2026-11-22 (every register directly in `u_bank_timers`); build C,
     the default placement with it, is in section 5b.
- **The model's next term** (6b): the self-close through the record's hit
  path with whatever arms the chain after each AXI burst's last column (one
  in four; not "it lands after the close" -- that probe gives four cycles on
  every chain), target = these traces. Until it lands the model with the
  field is +11 .. +15 optimistic on the same-bank close-page read sides and
  the compare against board A reads 52 in / 5 out.
- **The RTL question behind the small gain**: arming the ACT of a head on an
  auto-precharging bank before the row image clears (the lookahead the LA_AP
  term already computes, into the decode's class) is MC-021's `ap_act_la`
  question; it is what would let the field pay the priced +11 .. +15 on
  those streams. Not this task's.
- Files: `mc_bank_timer.sv`, `mc_bank_timers.sv`, `mc_scheduler_plane.sv`,
  `granite_core.sv`, `granite_top_geared.sv`, `pumice_core.sv`,
  `scoria_scheduler_plane.sv`, `andesite_scheduler_plane.sv`,
  `granite_csr.rdl` + `regs/generated/*`, the three granite core tests,
  `formal/mc_common/mc_bank_timer/{mc_bank_timer_gold.sv,formal_bank_timer.sv,formal_bank_timer_equiv.sv,Makefile}`,
  `pumice_device.py` + `test_pumice_device.py`, `granite_sku_controller.cpp`,
  `ddr2.py`, `char_model.py` + `test_char_model.py`, this record, the two
  model compares and the board compare, the model CSVs (`_rps_`, `_rpap_`),
  the board CSVs (`sku100rpapA{,w2,w3}_windows`, `sku100rpapA_every`), the
  bitstreams `ddr2_char_granite_sku100_mc020d2{,b}_2026-11-22.bit` (untracked,
  unclosed).

## 8. Regressions on the decision-2 RTL (clean-all first, every suite)

| suite | result | baseline |
|---|---|---|
| `formal/mc_common/mc_bank_timer` prove / cover / equiv / equiv_live | 4 / 4 PASS, 11 covers reached, `a_trp_ap` mutation-checked | |
| ddr2_char_framework `run-all-func-parallel`, no knob | 226 passed, 2 xfailed, 0 errors, 0 reruns (46 min) | 226 / 2 |
| ddr2_char_framework, TEST_DUAL=1 / TEST_DUAL=0 | 222 passed, 2 xfailed, 48 errors each (the pumice char test's guard on the foreign knob), 0 reruns | 222 / 2 / 48 |
| granite top `run-all-full-parallel` | 29 passed, 5 skipped, 1 xfailed (a first pass had 1 rerun: the new ports undriven by the Python-named drive lists; driven, no rerun) | 29 / 5 / 1 |
| pumice top / macro / fub | 525 passed 4 skipped / 117 / 32 | the same |
| scoria top / macro / fub | 4 passed / 7 failed 12 passed / 10 failed 195 passed 1 skipped -- every failure the recorded stale TB (`u_arbiter`, `t_rcd_i`, `column_pick_smoke`) | the same |
| andesite top / macro / fub | 4 failed / 10 failed 8 passed / 12 failed 213 passed -- the recorded classes (`andesite_core_tb` compile, `u_arbiter`, `t_rcd_i`, its own arbiter) | the same |
| model tests / host tests | 45 / 34 | 43 / 32 before the new ones |
| `GRANITE_SYS_100=1 make bitstream`: A (default placement), B (ExtraTimingOpt) | WNS -0.052 / -0.054 under the 0.2 ns budget, 15 / 25 endpoints | +0.014 / +0.080 |
| build C: default placement + the bank timers' CSR-derived registers false-pathed | **WNS +0.002, 0 failing endpoints**, 37,320 LUT / 32,962 FF -- the SKU bitstream | |
| the board on build C | 95 cells + memtest, 0 mismatched; the model 54 in / 3 out | |
| the proxy, six traces through `jedec_ck_check.py` | 24,625 .. 197,313 commands each, no violation | |

## 9. Addendum (2026-11-23): the model CSVs of section 6 predate the finished term

Re-running the committed model (c10ce1ef9) on `granite_sku100_bi col_major_bl4`
gives 446 / 446 with the field and 446 / 446 with the shared tRP, where
`model_ramulator2_ddr2_granite_sku100_bi_rpap_2026-11-22.csv` says 446 / 520;
`granite_sku100_close mixed_bl8` is 73 / 117 against the CSV's 73 / 121. The
four `_rpap_` / `_rps_` CSVs were written 14:28 .. 14:37 on 2026-11-22, the
controller's last edit (the finished `ap_seq` term) at 16:44; `ap_seq=false`
reproduces the CSV's 520. So in section 6's table the bank_interleave
col_major_bl4 line "model predicted 446 / 520" and the compares' 54 / 3 and 52
/ 5 are the pre-term model's; against the committed model that cell is OUT
(-13.6 on the read) and the count is 53 / 4. The board's +17 on the cell is
the RTL's and stands. The term's defect on this chain, and the record-path
term of section 7, are memory-controllers MC-023 (filed 2026-11-23, with
the mechanism of the "one in four": the col_major walk's row step -- the head
after a burst's last column is of the next row, a miss from its first record,
and the lookahead arms it).

## 10. Correction to section 9 (2026-11-23, memory-controllers MC-023 item 2)

Section 9's cause was wrong. The CSVs did not predate the finished term; the
finished term carried a defect. Its lookahead guard,
`m_clk - m_ap_fire_clk[b] < ap_close_lag * slot`, was meant to be off at
`ap_close_lag` 0, but `m_ap_fire_clk` holds the self-close's FUTURE fire
cycle while the close is pending, so the difference is negative and the
compare true: every ACT request lost its lookahead across a pending
self-close, and the bank_interleave bl4 read chain ran 7 MC where tRC
allows 6. With the guard gated on `ap_close_lag > 0` the committed model
reproduces all eight `_rpap_` / `_rps_` CSVs of section 6 to the cycle (120
of 120 cells), so section 6's "the model priced 446 / 520", and the
compares' 54 / 3 and 55 / 2, stand. The 53 / 4 of section 9 is withdrawn.
