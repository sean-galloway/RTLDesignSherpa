# RTL measured, not landed: the row lane carrying ACT only (memory-controllers MC-019), 2026-11-20

MC-019 proposed dropping the PRE class from the pick core's row lane
(`mc_bank_pick.sv`, the DUAL_ISSUE lane of MC-014) on the SKU model's word: a
lane carrying ACT or PRE and one carrying ACT only gave the same MB/s on all 29
MC-018 patterns, so a demand PRE never needed to ride. The change was made,
linted, proved, built and A/B-run on the proxy. **It is not landed**: the lane
carries 414-424 demand PREs per `col_ilv` run at the SKU, the model issues
none, and removing them costs the read side of that cell 1.3 percent. The RTL
is back at HEAD; the patched file is kept beside this record's session
scratch (`mc_bank_pick_mc019.sv`) for the owner's decision (section 6).

## 1. The change

The lane's candidate set becomes the ACT requests whose bank has no column
pending (a PRE request is never rideable and takes the main slot, as a row
command always did); the ACT-before-PRE class order, the PRE class / timer /
lookahead checks, the lane's PRE -> ACT hint and the `row2_pre_o` payload go
(the port stays, constant 0, for the plane's word format); `r2_cls` goes with
them. 46 lines in for 62 out. `formal_bank_pick_dual.sv`: `a_pre_gate` becomes
`a_no_lane_pre` (the lane never fires a PRE), the PRE-beside-column cover is
removed. The model's SKU point moves to `lane` 2 with `sku_laneboth` as the
form before. Verilator lint clean at DUAL_ISSUE 1.

## 2. Formal (on the flat of the changed RTL, `make clean` first)

| task | result |
|---|---|
| dual | PASS, k-induction, 3 s |
| dual_cover | PASS, the three remaining covers reached (ACT beside a column, beside a read, beside a write) |
| cover | PASS |
| equiv | PASS (8 min; the lane is compiled out of the equivalence against the gold copy, so this checks the rest did not move) |
| equiv_n4 | PASS (2 min) |

## 3. The no-knob sys100 build

`GRANITE_SYS_100=1 make bitstream`, `reports_sys100_mc019_2026-11-20/`
(the bitstream `ddr2_char_granite_sku100_mc019_2026-11-20.bit`, not board-run).

| build | LUT | FF | WNS | failing endpoints | worst path |
|---|---|---|---|---|---|
| SKU 2026-11-16 (the task's baseline) | 37,357 | - | +0.012 | 0 | inside the pick: `r_is_col` -> `r_win_cls` |
| MC-021 step 5, 2026-11-19 (HEAD) | 37,389 | 32,926 | +0.080 | 0 | - |
| MC-019 lane ACT only | 37,112 | 32,923 | +0.014 | 0 | store `wr_full` -> pick `r_win_pair` |

-277 LUT against HEAD (-245 against the 11-16 build), 3 FF. WNS +0.014 is
inside the placement band the 0.2 ns clock-uncertainty budget absorbs (the
three SKU builds sit at +0.012 / +0.080 / +0.014); the pick core still holds
the worst path. The lane's PRE path was not the binding cone: the task's own
"if not, it closes on the area number alone" case.

## 4. The proxy A/B, and why the first one was wrong

The proxy (granite char harness, SKU: 100 MHz, lane on, pool 16, 4 generators,
512 transactions, AxLEN 8; `incremental`, `row_major`, `col_ilv`, `col_major`,
`mixed`) was first run on a `git archive` of HEAD against the working tree.
The TEST_DUAL=0 pair, where the lane is built out and the RTL change cannot
reach, differed on four of five cells -- so the two directories, not the RTL,
were being compared. A second run in ONE directory with the two RTL files
swapped is the A/B below; a repeat of one base run in its own directory gives
the run-to-run band (section 5).

Before = the lane carrying ACT or PRE (HEAD), after = ACT only. Write / read
MB/s; cycles of the two passes.

| run | family | before | after | wr cycles | rd cycles | read |
|---|---|---|---|---|---|---|
| SKU defaults, lane on | incremental | 755.2 / 757.2 | 755.2 / 757.2 | 17355 / 17355 | 17311 / 17311 | identical |
| | row_major | 755.9 / 759.0 | 755.8 / 757.6 | 17339 / 17342 | 17269 / 17302 | within the band |
| | col_ilv | 756.5 / 741.1 | 755.8 / **731.8** | 17326 / 17342 | 17687 / **17912** | **-1.3 % read** |
| | col_major | 758.8 / 758.9 | 752.4 / 759.1 | 17273 / 17420 | 17272 / 17266 | within the band (the same RTL gave 752.4 and 758.8) |
| | mixed | 269.5 / 271.3 | 268.8 / 270.0 | 48631 / 48769 | 48317 / 48538 | within the band |
| open_page, lane on | incremental | 755.2 / 757.4 | 755.2 / 757.4 | - | - | identical |
| | row_major | 757.1 / 758.8 | 757.1 / 757.6 | 17313 / 17313 | 17273 / 17300 | within the band |
| | col_ilv | 755.9 / 742.2 | 755.0 / **733.2** | 17339 / 17360 | 17661 / **17877** | **-1.2 % read** |
| | col_major | 757.6 / 759.8 | 753.9 / 758.0 | 17302 / 17387 | 17250 / 17291 | within the band |
| | mixed | 296.6 / 445.3 | 269.3 / 270.9 | 44191 / 48676 | 29435 / 48392 | the bimodal cell (ISSUE-005): a mode, not a delta |
| SKU defaults, lane off (TEST_DUAL=0) | all five | - | - | identical | identical | identical, as it must be |

The `col_ilv` read side is the one real move: four runs of each form (two
directories, two policies) give 741.1-742.2 before and 731.8-733.2 after, with
a band of 0.2 percent on that cell. Every other delta is inside the band or
the mixed cell's mode. `mismatched` 0 in every run.

**The mechanism**, from the command-kind log (`PERF_CMD_TRACE`, `col_ilv`
alone, both passes):

| policy | form | main ACT | lane ACT | main PRE | lane PRE | read pass cycles |
|---|---|---|---|---|---|---|
| defaults | before | 498 | 1063 | 259 | **424** | 17665 |
| defaults | after | 134 | 1514 | 774 | 0 | 17924 (+259) |
| open_page | before | 505 | 1061 | 272 | **414** | 17678 |
| open_page | after | 133 | 1516 | 782 | 0 | 17881 (+203) |

Under the shipped `defaults` (the hybrid page predictor) and under static open
page the RTL issues ~700 demand PREs on this cell: rows left open by the
policy are closed when the next row of that bank arrives. Before, 424 of them
rode the lane beside a column; after, every one takes a main slot, and the
read pass pays about one slot per PRE that used to ride. (The after form also
cycles rows more -- 1,648 ACTs against 1,561 -- because the PRE now lands
later and the predictor's view of the bank changes with it.)

**Correction (later the same day, ISSUE-006):** the proxy's `TEST_PAGE_POLICY=1`
wrote only the flat policy field and left `policy_mode` at its RDL reset, the
hybrid (4), so the "open_page" rows above measured the hybrid too; the board's
open_page preset writes policy_mode 0 (the flat close-on-drain, no history gate,
no timeout), under which the model -- and, by the board's open_page numbers,
the RTL -- issue almost no demand PRE. The 1.3 percent is the `defaults`
preset's. The knob writes mode 0 and tr_init 0 with the policy now.

**Why the model said 0.0.** `lane_pre` is 0 on all fifteen SKU cells of the
step-8 model CSV: the model never issues a demand PRE on these presets. Its
SKU auto-precharges on drain (the exact close-on-drain term) and has no term
for the hybrid predictor or for static open page -- the same stand-in that
ISSUE-006 names for the mixed cell. Where the model's `laneact` variant
measured nothing, it was measuring a command it never issues. A 0.0 the model
gives a path it does not exercise is not a price; the proxy's command-kind
log is where such a claim is checked before the RTL is touched.

## 5. The proxy's run-to-run band (granite ISSUE-003)

The same build directory, seed and environment, run twice (TEST_DUAL=0, the
first under three other sims and a Vivado run, the second under less):

| family | run 1 wr / rd cycles | run 2 | delta |
|---|---|---|---|
| incremental | 17412 / 17416 | 17412 / 17416 | 0 |
| row_major | 17322 / 17331 | 17347 / 17328 | 0.14 % |
| col_ilv | 17918 / 18353 | 17992 / 18386 | 0.4 % / 0.18 % |
| col_major | 19530 / 19507 | 19524 / 19507 | 0.03 % |
| mixed | 49872 / 49519 | 49740 / 49387 | 0.26 % |

and the same RTL in two directories gave `col_major` 752.4 and 758.8 on the
write side (0.85 percent). MC-021's "reruns identical" was observed on a
single-family run; a five-family run is not deterministic. Filed as granite
ISSUE-003 (the host-over-UART harness is the suspect: anything paced on the
wall clock moves GO against the refresh counter). Until it is settled a proxy
delta under about half a percent needs repeats to read, and the compare of
one run against one run reads only the moves above it -- as the `col_ilv`
read side here is.

## 6. What this leaves

The task's done-when is not met: the cells are not unchanged, by 1.3 percent
on one family's read side at the SKU. The gain is 277 LUT (0.7 percent of the
design) and nothing on timing. The decision is the owner's:

- take it: 277 LUT for -1.3 percent on `col_ilv` reads (about 10 MB/s on the
  board's 767 / 770 for that cell on `defaults` / `open_page`), with the
  regressions, the board run and the model's `lane` 2 to follow; or
- drop MC-019 with this measurement, the RTL stays as it is.

Either way ISSUE-006 widens: the model's open-page stand-in has no demand
PREs where the RTL's `defaults` and `open_page` presets have ~700 per
`col_ilv` run, and every lane / PRE question the model prices is wrong by
that much until the page policy is a term.

## 7. Record

- `reports_sys100_mc019_2026-11-20/` (the build), the bitstream kept beside
  the others, not board-run.
- Scratch (session `mc019/`): `mc_bank_pick_mc019.sv` and
  `formal_bank_pick_dual_mc019.sv` (the change), `perf_*.json` (the proxy
  dumps: `base` / `new` the first, cross-directory pair; `ntbase` / `newtree`
  the same-directory A/B; `base2` the repeat), `pre_*.json.gaps.json` (the
  command-kind counts), `formal_*.log`, `build_sys100.log`.
- The model is unchanged (`lane` 3, `sku_laneact` still the ACT-only
  variant).
