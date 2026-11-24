# MC-023 item 4: the mixed cell's mode is decided by where the refresh walks, and the model's first ACT after a refresh was three slots early

> memory-controllers MC-023 item 4 (ISSUE-005's fidelity gap), 2026-11-24. The
> proxy (`test_granite_char_perf`, 100 MHz, `TEST_DUAL=1`, phase-exact default,
> 4 generators, `mixed` bl8, `TEST_TXN=512`) against the SKU model on the same
> cell. Ends with one model term, `rfc_block`, now the SKU default.

## 1. The proxy shows both modes, chosen by the refresh phase

tREFI moved a cycle at a time (`PERF_DIR_FLIPS` per run):

| preset | 778 | 779 | 780 | 781 | 782 |
|---|---|---|---|---|---|
| `open_page` (`TEST_PAGE_POLICY=1`) | 280.7 / 282.7 | 280.5 / 282.4 | 286.7 / 330.8 | **300.3 / 506.7** | 285.2 / 308.9 |
| `defaults` (power-on hybrid) | **299.0 / 514.3** | 280.3 / 282.2 | 280.0 / 282.0 | 277.0 / 278.8 | 279.3 / 281.4 |

The board: `open_page` slow 8 / 10, `defaults` slow 10 / 10. The model before
this record: fast on 40 / 40 GO phases of both presets.

## 2. The race is the one ISSUE-005 named, on the RTL

`PERF_PICK_PROBE_FLIP=23` on 779 (slow) and 781 (fast), the first cap turn the
two runs take differently. At 781 the reads' ownership PRE on bank 0 fires at
the cap flip itself, the reads re-ACT bank 0 at idle 3, the write's PRE fires
at idle 8 -- the slot the hold expires (`w_xdir_ok`) -- and a bank-1 read
column takes the bus back: a zero-column write turn. At 779 the last read
column fires at the flip, the write's PRE at idle 7 resets the idle counter,
and the writes run 255. The fixed model reproduces the 781 sequence slot for
slot at its own first zero-column turn (CK 57560); its slow turns match the
RTL's shape too (reads hold ~311 MC, writes ~401, both sides).

## 3. What decides it: whether the refresh walk reaches the read cap

Each read turn is 256 columns, 16 rows of 16, so the reads' row switch lands
on the cap every turn and the race is never armed -- until a turn overruns.
Only a refresh landing in the last few columns of a read turn does that (the
781 turn of 270 columns, the model's of 264), after which the row phase is
off the cap and the ownership PRE coincides with the flip.

The refresh lands ~36 columns later each read turn (the turn pair is ~732 MC
against tREFI 780). On the RTL that walk is **stationary**: 779 lands at 40,
75, 110, 144, 181, 223 and steps over the cap into the write turn, the same
six columns every cycle of 16 turns (the 16-turn sum 11,699 ~ 15 x 780); 781's
walk is 22 .. 216, 253 -- into the window. So each phase either always or
never escapes: a draw per run, as the board shows. The model's walk drifted
cycle to cycle (52 .., 39 .., 45 .. 250) and reached the window on every
phase.

The drift is the refresh's cost by where it lands. RTL: a refresh in a write
turn costs a constant +18 MC (392 -> 410); the model's +20 / +15
alternating. The probe across one write-turn refresh (779, cycle 195848):

| | RTL | model before |
|---|---|---|
| refresh requested -> REF granted | 2 | (PREab +4, REF +2) |
| REF grant -> tRFC counter loaded | +1 (13) | -- |
| counter zero -> request -> fire | +2 | -- |
| REF -> first ACT | **16** | **13** (the device's tRFC, with the lookahead) |

`mc_bank_pick` loads `r_rfc_cnt` with the CSR tRFC the cycle after
`refresh_grant_o` and holds every demand request and fire
(`w_rfc_dmd_block`) while it is non-zero; the model let the ACT fire at the
DRAM's tRFC.

## 4. The term: `rfc_block`

`granite_sku_controller.cpp`: after a REFab at slot G no demand request
decodes and nothing fires before G + 1 + tRFC (tRFC = a row -> row hop of
nRFC, 13 at the SKU's point = the CSR). The first ACT then fires at G + 16, the
RTL's slot (debug trace, MC 16382 -> 16398). `ModelConfig.rfc_block` True on
the SKU; `sku_norfcblock` is the model before.

Against the SKU board set (`compare_model_sku_rfcb_vs_board_sku100rpap_2026-11-24.md`):
**57 in / 0 out**, from 54 / 3 -- the first model with no cell OUT. Cells it
moves by more than one percent: the two mixed cells, and twelve close_page /
bank_interleave directions by 1.0 .. 2.1 percent, eleven down and one up
(row_thrash, the interleaved col walks, the bank_interleave row-hit cells
584.6 -> 572 .. 579, bank_interleave col_major_bl16's write +1.0), all within
their tolerance. bank_interleave col_major_interleaved_bl4's
read 402 -> 394 (board 361) is now in.

The 40-phase GO sweeps (`model_mc023_rfcb_go_sweep_<config>_2026-11-24.csv`):

| config | modes x phases | board |
|---|---|---|
| `granite_sku100` (`defaults`) | 278 / 278 x27; 303 .. 308 / 618 .. 622 x13 | 277 / 276 x10 |
| `granite_sku100_open` | 289 .. 291 / 366 .. 369 x40 | 280 / 280 x8; 303 / 594 x2 |

So `defaults` now has the board's mode as its majority, and the model's fast
mode reads within 5 percent of the board's `open_page` fast mode (619 / 606
union). `open_page` is in an intermediate mode on every phase, one the board
does not show: the walk still drifts on that preset (the next term), or the
intermediate mode is a short-run blend the proxy's 512 transactions cannot
separate from the board's 32,000.

## 5. What is left (MC-023 item 4)

- `open_page`: the intermediate 290 / 367 on 40 / 40 phases. Read its walk
  per cycle as in section 3 and find the next refresh-cost difference (the
  read-turn refresh, +18 .. +25 on the RTL by landing column, not yet
  compared slot for slot).
- `defaults`: 13 / 40 fast where the board is 0 / 10.

## 6. Record

- Proxy runs: TXN 512, `TEST_TREFI` 778 .. 782 under both presets; the pick
  probe at flip 23 on 779 / 781 and from cycle 195835 on 779 (60 cycles each).
  The probe gained the refresh episode's signals (`refresh_req_i`,
  `refresh_grant_o`, `r_rfc_cnt`, `w_ref_safe`, `w_any_active`,
  `w_all_act_ready`, `r_actfire0`, `w_rdret_gate`, `bank_act_ready_i`);
  the DRAM trace carries no REF.
- Model tests 46 / 46; the MC-021 close-lag test is pinned to
  `rfc_block=False` (the model its two modes were measured on; with the block
  the margin cell reads ~307 at both phases).
