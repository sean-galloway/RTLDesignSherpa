# The SKU model's admission knobs against the board, every setting on every preset (2026-11-17)

**Question (owner, 2026-11-17):** after ISSUE-004 the two board presets that
were already out of tolerance moved further out. Run the knob settings as a
grid and say whether one setting wins, or whether different situations want
different settings.

**Answer.** One setting, and it is the SKU default. The three ISSUE-004 terms
(`cap_per_beat`, `admit_lag`, `req_bank_timing`) move only the `mixed` cell of
the shipped configuration; every single-direction cell is identical under all
28 combinations. On the two presets no combination lands a single cell in
tolerance, and the setting that reads "best" there (`req_bank_timing` off)
is better by accident: it adds waiting that happens to resemble a cost the
model does not carry. That cost is now measured in the RTL proxy (section 3)
and is a missing term, not a knob. Separately, the model's `bank_interleave`
preset was configured wrong -- the board's preset is the interleaved map AND
close page -- and that error, not the RTL, was ISSUE-002's factor of three.

Files: `model_ramulator2_ddr2_knob_grid_2026-11-17.csv` (1680 cells: 4 preset
configurations x 28 knob settings x the 15 board-measured scenarios),
`model_ramulator2_ddr2_granite_sku100_bi_grid_2026-11-17.csv` (the corrected
preset through the CLI), `compare_model_sku_vs_board_sku100def_grid_2026-11-17.md`.

## 1. The grid

Knobs: `cb` = cap_per_beat (1 = the mixed cap checked at every push), `lag` =
admit_lag in MC cycles (0..6), `rbt` = req_bank_timing (1 = the decode's
request on the bank's timers only, the rank timers holding the fire). SKU
default `cb1_lag4_rbt1`; the MC-018 form `cb0_lag0_rbt0`. Delta = the direction
with the larger |pct| against the board cell (mixed: the union); tolerances are
board-compare's (2 / 3 / 5 / 10 percent by family, 10 / 15 for the presets).

### The SKU (board `defaults` + `open_page`, 30 cells)

Every one of the 28 settings has all 14 single-direction cells within 0.7
percent of the board, identical to the digit. Only `mixed_bl8` moves:

| setting | mixed wr / rd | union delta | | setting | mixed wr / rd | union delta |
|---|---|---|---|---|---|---|
| `cb1_lag3_rbt0` | 275 / 276 | +1.4 % | | `cb1_lag4_rbt1` (default) | 286 / 286 | +5.5 % |
| `cb0_lag4_rbt1` | 283 / 285 | +4.3 % | | `cb0_lag0_rbt0` (MC-018) | 296 / 417 | +8.9 % |
| `cb1_lag5_rbt1` | 284 / 284 | +4.7 % | | `cb1_lag2_rbt1` | 310 / 310 | +14.2 % |
| `cb1_lag3_rbt1` | 219 / 219 | -19.6 % | | `cb1_lag6_rbt1` | 207 / 207 | -23.9 % |

Board 272 / 272, union 543. Read the `lag3` pair: the same lag lands +1.4
percent with one request form and -19.6 with the other. That is the admission
cliff ISSUE-004 found (two beats of slack flip the turn structure), and a
setting that sits on it is not a prediction. The default sits one step past
the cliff on the side the RTL is on (the RTL's push -> head is four cycles)
and gives the same +5.5 under both request forms. It stays.

### The presets (board `bank_interleave` 12 cells, `close_page` 15 cells)

| preset | setting | in / cells | mean abs delta | worst cell |
|---|---|---|---|---|
| bank_interleave (close page, corrected) | any with `rbt0` | 0 / 12 | 38 % | col_major_bl4 +60 % |
| bank_interleave (close page, corrected) | any with `rbt1` (default) | 0 / 12 | 72 % | col_major_bl4 +100 % |
| bank_interleave as committed (open page) | all 28 | 0 / 12 | 178 - 215 % | col_major_interleaved_bl4 +296 % |
| close_page | `rbt0` settings | 0 - 1 / 15 | 32 - 35 % | row_thrash_bl8 +58 % |
| close_page | `rbt1` settings (default) | 0 - 1 / 15 | 40 - 43 % | row_thrash_bl8 +98 % |

`cap_per_beat` and `admit_lag` do nothing on either preset (identical cells
across all 14 settings of each `rbt`): they are mixed-window terms and these
are single-direction passes. `req_bank_timing` is the whole spread. With it on
(the RTL's decode) the model issues a bank-ready ACT the cycle the rank
timers open; with it off the request waits for the rank timers too and then
takes the pipeline's slots, which costs about half a cycle per hop. That half
cycle is in the right direction and is not the RTL's mechanism (section 3).

## 2. The preset that was wrong

`pumice_char.py`'s `ControllerConfig("bank_interleave", scheme=SCHEME_BANK_INTERLEAVE,
page_policy=PAGE_POLICY_CLOSE, ...)` is what the board ran. The model's
`granite_sku100_bi` encoded the map and left the page open; every bank was a
row hit and the model's 778 MB/s was the open-page number against a close-page
board. The RTL proxy under the host's exact pair (TEST_ADDR_SCHEME 2,
TEST_PAGE_POLICY 2) reproduces the board; under the open-page pair it
reproduces the model:

| proxy run (100 MHz, TXN 2048) | incremental wr / rd | col_major wr / rd | board |
|---|---|---|---|
| scheme 2 + policy 2 (the preset) | 235.0 / 229.6 | 234.9 / 226.7 | 234 / 233, 237 / 235 |
| scheme 2 + policy 1 (open interleave) | 757.9 / 751.4 | 236.3 / 225.9 | not measured |
| scheme 1 + policy 2 (`close_page`) | 81.9 / 92.5 | 80.3 / 89.4 | 82 / 92, 80 / 90 |

`char_model.py` now sets `page_close=True` on `granite_sku100_bi`, with a
guard test that reads the host's preset table
(`test_board_presets_are_what_the_host_programs`). Corrected, the preset's
model cells are 389 / 389 on every family against the board's 232-238
(+63 .. +67 percent; +100 on the two bl4 cells where the board's write side
drops to 195). The ISSUE-002 gap is now the same gap as ISSUE-003's: a
close-page chain the model runs at the timers and the RTL does not.

## 3. The chain, measured in the RTL

Two proxy runs with `PERF_DRAM_TRACE` (every command, MC cycle, bank) and
`PERF_PICK_PROBE` (the pick core per cycle) in steady state.

### Eight banks, close page (the `bank_interleave` preset), incremental writes

16,251 beats over 55,248 MC cycles: 3.40 cycles per beat (reads 3.48). The
model with the default setting: 2.0 (389 MB/s), the tRRD bound of the host's
timings (t_rrd 2 MC cycles). The pick probe at cycle 60000 shows the period
for two beats on banks a, b:

```
cycle  main slot                      lane (r2)
  0    ACT a fires                    holds pair c (ACT), tim_ok 0
  1    (ACT b wins; held: trrd_ok 0)
  2    (held)                         tim_ok 1 but no column fires -> no ride
  3    ACT b fires (trrd_ok)          tim_ok 0
  4    COL a fires (ready since 2)
  5    COL b fires
  6    select CDIR: nothing valid     tim_ok 1, no column fires
  7    select ROW: ACT c wins
  8    ACT c fires
```

Three costs the model does not have, each read off the RTL:

1. **ACT -> ACT is 3 cycles, not t_rrd = 2.** `mc_global_timers` registers
   `trrd_ok` (`w_trrd_ok_nxt` -> `trrd_window_ok_o`): the counter installs 2
   at the fire, reads <= 1 one cycle later, and the ok is seen the cycle after
   that. 80 percent of the pass's ACT -> ACT gaps are exactly 3 (13,006 of
   16,251). JEDEC tRRD for this part is 10 ns, one MC cycle; the host
   programs 2 and the RTL pays 3.
2. **A winning ACT that waits for the rank timer blocks the ready column.**
   The main winner register holds the ACT while the lookahead says its timer
   opens within the pipe depth; the column of the previous ACT, ready at
   +tRCD, fires two cycles late (40 percent of ACT -> COL gaps are 4, the rest
   the exact 2). This reorders the pair, it does not lengthen the period.
3. **Two empty slots after each column pair.** With the alternation, the
   select after a column tries the column class first (CDIR, finds only
   stale pairs), takes the row class the next cycle, loads the winner, and
   fires the cycle after: 2 slots per period in which nothing fires though
   an ACT request is pending (`r_req` has it; `req_ok` has it).

The lane carried none of these ACTs: `w2_fire = w2_ok && w2_timer_ok &&
w_col_fire_now` needs a column fire and an open tRRD in the same cycle, and
under this cadence the columns fire at +1 and +2 after an ACT, inside the
tRRD window. The lane held pair c (bank 3 write) for the whole 64-cycle window
with `tim_ok` and `colf` never both 1; the main slot took every ACT, three
cycles apart, and the held pair's bank was skipped for a round (the pass has
2,058 ACTs on every bank, so this is a rotation delay, not starvation).

### One bank, close page (the `close_page` preset), incremental

Writes: 9.77 cycles per beat (ACT -> ACT exactly 10 in 88 percent of the
pass); reads 8.65 (9 in 88 percent). ACT -> column is tRCD 2 on 99 percent
of beats: the next-op hint pre-arms the column and it fires the cycle the
bank opens. The ACT after the auto-precharge is the un-hinted hop, and the
probe times it against the bank's own timer (`bank_act_ready_i[6]`, pair 13):

```
cycle  row_active  act_ready  r_req[13]  fire
 12    0           0          0          -        (the AP's tWR + tRP run out)
 13    0           1          0          -        the bank is ACT-ready
 14    0           1          1          -        the decode's registered request
 15    0           1          1          ACT      the winner register, then the fire
 16    1           0          1          -
 17    1           0          0          WR(AP)   tRCD exactly: the hint pre-armed it
```

The ACT fires two cycles after its timer opens, every period. The model
fires it at the timer: 7.7 cycles per write beat (104 MB/s against the
board's 82), 6.7 per read (119 against 92); measured RTL minus model is
+2.1 and +1.95 cycles per beat. In the eight-bank run the same two cycles
show against the rank timer: at cycle 6 the winner's bank is ACT-ready
(`bank_act_ready_i` bit 5 = 1) and it fires at 8, tRRD (2) plus the
registered ok.

### What the two runs say together

A dependent command the next-op hint pre-arms (ACT -> its column) fires at
its timer in the RTL as in the model. A dependent command the hint does not
pre-arm (the ACT after a precharge, the ACT after another bank's ACT under
tRRD) fires about two slots after its timer opens: the decode's registered
request plus the winner register, with the lookahead not reaching the
rank-level and post-precharge timers. On open-page streams those hops are
one per row and the cost is under the model's error bar, which is why the
SKU's 30 cells never saw it. On close-page streams every beat is such a hop.

ISSUE-003 asked for this exact measurement and named the model term: a
`hop_lag` (a command's fire no earlier than N slots after its timer opens,
for the hops the hint does not cover; N = 2 from both runs), plus the RTL
question of whether the lookahead can reach those timers. Filed as MC-021;
ISSUE-002 and ISSUE-003 close into it.

## Method

- Score every knob combination on every preset against the board before
  choosing; a setting that wins one cell and loses the neighbouring cell on
  the same knob axis is a cliff, not a fit.
- A knob that must flip per preset to approach the board is not a model of
  the RTL (the RTL has one decode): it is a stand-in for a term that is
  missing. Go and measure the term.
- A preset is what the host programs, not what its name says. The board
  CSV's `config` column names a `ControllerConfig`; read the fields
  (`scheme`, `page_policy`) before encoding it in the model, and guard the
  encoding with a test that imports the host's table.
- The proxy reproduces the board on all three presets to within a percent
  (section 2 table). When the model and the board disagree, run the proxy at
  the board's exact preset with the DRAM trace and the pick probe before
  touching the model.
- The test's perf dump lands in `dv/tests/logs/perf_dump_test_granite_char_perf.json`
  and every run overwrites it; set `PERF_DUMP=<own path>` per run, or the
  second run's numbers wear the first run's name (it happened here, caught by
  the `page_policy` field in the dump).

## Recipe

```bash
# the grid: a 60-line driver around char_model.run_scenario -- configs = dataclasses.replace(cm.SKU, ...) over
#   presets {SKU; addr_map=bank_interleave + page_close; addr_map=bank_interleave open (reference); page_close}
#   x knobs cap_per_beat {0,1} x admit_lag 0..6 x req_bank_timing {0,1}, scenarios cm.SUITES['all'],
#   multiprocessing.Pool(40) with one tempdir per cell; 1680 cells in 169 s. Scored per preset against
#   cm._load_measured(<CR>, 'granite', 'sku100def_2026-11-16') with board-compare's tolerances.
# the corrected preset through the CLI + the board compare
python3 bin/char_model.py run --config granite_sku100_bi --suite all --out <CR>/model_ramulator2_ddr2_granite_sku100_bi_grid_2026-11-17.csv
python3 bin/char_model.py board-compare --model <sku100 issue004 csv> <bi grid csv> <close issue004 csv> --measured <CR> --granite sku100def_2026-11-16 --out <CR>/compare_model_sku_vs_board_sku100def_grid_2026-11-17.md
# the proxy at the board's presets (ddr2_char_framework/dv/tests, env_python sourced)
TEST_FPGA_CLK_HZ=100000000 TEST_T_PHY_WRLAT=1 TEST_TREFI=772 TEST_TXN=2048 TEST_LEVEL=FUNC TEST_DUAL=1 TEST_NUM_ENTRIES=16 \
TEST_ADDR_SCHEME=2 TEST_PAGE_POLICY=2 TEST_FAMILIES=incremental,col_major TEST_NUM_GEN=1 \
PERF_DUMP=<own path>.json PERF_DRAM_TRACE=<path>.json PERF_PICK_PROBE=<path>.json PERF_PICK_PROBE_FROM=60000 PERF_PICK_PROBE_CYCLES=64 \
python3 -m pytest test_granite_char_perf.py::test_granite_char_perf -q
# scheme 1 + policy 2 = close_page; scheme 2 + policy 1 = the open interleave the board did not run
```
