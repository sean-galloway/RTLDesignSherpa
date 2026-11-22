# The phase-exact JEDEC derivation is the host default (memory-controllers MC-020, decision 1), 2026-11-22

The owner adopted the phase-exact derivation
(`board_mc020_phase_exact_sku100_2026-11-21.md`) as the host's default, on
the condition of one endurance soak at the new counters. This record is the
soak, the default flip, and the board re-baselined at the default. No RTL
change; the bitstream is the step-5 build
(`fpga/bitstream/ddr2_char_granite_sku100_mc021s4_2026-11-19.bit`, HEAD's RTL).

## 1. What the soak had to run, and the tidy that came first

The bring-up soak (`pumice_master.long_soak` under `SimpleTest`) soft-resets
the controller every round, and the reset state is not the SKU: row lane
off, `DFI_PHASE.row_phase` 0 (its RDL reset), the paging resets. The char
measures the SKU through `pumice_char.ControllerConfig.apply` -- lane on,
`row_phase` 1, the JEDEC set derived for those phases. A soak through the
reset state would have run tWR 4 on phase-0 row commands and said nothing
about the tWR 3 the SKU runs. So:

- `bin/seq_soak.py`, a `soak` sequence: `init`, then `long_soak` for
  `--soak-minutes` with a named `ControllerConfig` (`--soak-config`, default
  `defaults`) re-applied after every per-round reset (`long_soak(reapply=...)`,
  three call sites: the device init, every round, the eye re-verify).
- The derivation-order tidy from the 11-21 record: `SimpleTest` and
  `A7Leveling` derived their JEDEC set in `__init__`, reading the DFI phases
  back from a register that then held whatever the previous session left.
  Under the margin that moved nothing but tRTP; under the phase-exact
  derivation a tWR of 3 derived for `row_phase` 1 and run at `row_phase` 0
  is one CK short. Both now derive in the reset path, after
  `program_geometry` (`_derive_jedec`), so the set describes the device as
  programmed. The smoke's own set at the reset state is tRC 6, tWR 4, tWTR 3,
  tRRD 1, tRFC 13 (row commands on phase 0), the set the 11-21 smoke ran.

## 2. The soak

`JEDEC_PHASE_EXACT=1` (the flag; the code default was flipped after),
`make run SEQUENCES="init soak" RUN_ARGS="--controller granite --soak-minutes 60
--soak-config defaults"`. Every round's apply logged the SKU's set:
`tRC=6 tRCD=2 tRP=2 tRAS=5 tRFC=13 tREFI=780 tRRD=1 tFAW=5 tWTR=3 tCCD=1 tWR=3
tRTP=1 tRTW=21`, paging at the RDL resets (policy_mode 4, tr_init 2), the lane on.

| | |
|---|---|
| wall clock | 60 min (init 324 s before it) |
| rounds | 2,493 rotating 4 MB write-then-read windows across 128 MB |
| concurrent rounds | 249 (every tenth: write region A while reading region B, then verify A) |
| eye re-verifies | 11 (every 5 min at the cached bitslip / tap) |
| data moved | 21,944 MB |
| dirty rounds | **0**; 0 mismatched beats, 0 rd_error, 0 hangs, 0 eye fails |

Heartbeat: `soak_granite_sku100px_defaults_2026-11-22.csv` (2,754 rows).
With the 81-cell run and the memtest of 11-21, that is the data the default
stands on.

## 3. The default

- `ddr2_char.py` `jedec_timings_for`: `phase_exact` is on whenever the three
  DFI phases read back (`JEDEC_PHASE_EXACT=0` restores the margin; a phase the
  device cannot report still keeps the margin inside
  `ddr2_timings_mc_cycles`, whose own kwarg default stays False -- it is the
  pure derivation).
- The proxy (`test_granite_char_perf.py`): `TEST_PHASE_EXACT` default 1.
- The model (`char_model.py`): `granite_sku100` and its `_open` / `_bi` /
  `_close` presets on `DDR2_GRANITE_SKU100_PX`; the margin set stays as the
  `sku_margin` variant (`DDR2_GRANITE_SKU100`). The model at its default
  reproduces the 11-21 `px` CSVs cell for cell (60 cells, 0 differing). Three
  tests that reproduce board or proxy numbers recorded under the margin
  (`hit_lag`, the admission gates, the close-lag modes) pin that preset by
  name (`MARGIN`); 43 / 43 pass.
- Every board record before this date was made under the margin. The 11-21
  flagged run is the first at the new counters; today's run below is the
  baseline at the default.

## 4. The board at the default

No env (`JEDEC_PHASE_EXACT` and `TEST_PHASE_EXACT` unset), the same bitstream,
`--profile windows` three times (the modes) and `--profile every` once, each
behind its own `init`: 81 cells, 99 runs, **0 mismatched beats, every cell
ok**. The init derived the reset-state set (tWR 4, row commands on phase 0,
as on 11-21); every config applied the SKU's (`tWR=3`, the lane on, row
commands on phase 1); no flag line in the logs, the default path.

Against the 11-21 flagged run on the same bitstream
(`board_delta` over the 77 cells both have): 66 cells within one percent, 11
moved, and the 11 are one thing. The `bank_interleave` row-hit cells sit at
the 583 MB/s ceiling at the new counters (387 under the margin, the tRRD-bound
ACT rate), and on any one run a handful of them land a step below it: 566
(-3 percent) on five to seven of the eighteen, and ONE cell at ~520 (-11)
-- `row_major_bl16` writes on 11-21, `row_major_bl4` writes today. Which cells
fall is a per-pass draw (the two runs disagree on every one of the 11), no
cell shows a mismatch, and the model has no such level (585 on every one).
Under the margin the stream was 30 percent below the ceiling and the draw had
nothing to take; it is visible only now. Filed as memory-controllers
ISSUE-007. The eleventh moved cell is `close_page row_thrash_bl8` reads,
351 -> 344 (-2).

The mixed cells across the three `windows` runs: `defaults` 277 / 276 three
of three (the hybrid's one mode, as on every board run since ISSUE-006),
`open_page` 280 / 280 twice and 303 / 594 once (the two modes of ISSUE-005,
both faster than the margin's 272 / 272 and 311 / 522), `close_page` 60 / 66
three of three (the margin's 56 / 59).

## 5. The model against the baseline

`compare_model_sku_vs_board_sku100pxd_2026-11-22.md`, the model at its
default (four presets, two GO phases on the mixed cells) against the three
`windows` runs read by mode and the `every` run: **51 in / 6 out of 57**, the
same tally and the same six as the flagged run of 11-21:

- `bank_interleave col_major_bl4` reads 442 against the model's 520,
  `col_major_interleaved_bl4` 356 against 402: the auto-precharge path's
  tRP (decision 2, `t_rp_ap`) -- the RTL sequences tRAS then the shared tRP
  for 7 MC where the CK-exact distance is 6 and the model takes 6. On the
  single-bank `close_page` read sides the same gap sits inside the 15
  percent tolerance (model +12 .. +14).
- `bank_interleave row_major_bl4` writes 519 against 585: the ISSUE-007 draw
  (section 4); on 11-21 the same cell was 583 and in.
- The three mixed cells. At the exact counters the model's preference
  INVERTED against the board's: `defaults` -- the model is in the fast mode at
  BOTH GO phases (310 / 571, union 619; 309 / 560 at GO 480) where the board
  is slow three of three (277 / 276, union 553; +11.8 against a 10 tolerance),
  and under the margin it was the model that never left the slow mode.
  `open_page` -- the model fast at both phases (union 617), the board slow
  two of three (union 559; the fast run's union 606 groups with it at the 10
  percent tolerance), +10.2. `close_page` -- board 60 / 66 (union 120) three
  of three, model 73 / 121 (146), +21.5 against 15; under the margin 56 / 59
  against 58 / 75 (117), in. All three are the direction-register attractors
  of ISSUE-005, which now carries today's data; the shipped `defaults` cell is
  the one of the three where the model is in the wrong mode on every phase.

The sanity compare of the model against the 11-21 flagged board run, with the
same model CSVs: the same verdicts cell for cell (the model at its default IS
the 11-21 `px` model, 60 of 60 cells equal).

## 6. Record

- `char_granite_sku100pxd_{windows,every}_2026-11-22.csv`,
  `char_granite_sku100pxdw{2,3}_windows_2026-11-22.csv` (the board at the
  default; the two extra `windows` runs are the modes),
  `soak_granite_sku100px_defaults_2026-11-22.csv` (the soak heartbeat),
  `model_ramulator2_ddr2_granite_sku100{,_open,_bi,_close}_pxd_2026-11-22.csv`
  and the two `go480` files (the model at its default),
  `compare_model_sku_vs_board_sku100pxd_2026-11-22.md`.
- Host: `pumice_master.py` (`_derive_jedec`, `long_soak(reapply)`),
  `bin/seq_soak.py`, `bin/run_smoke.py` (`--soak-minutes`, `--soak-config`,
  `--soak-csv`), `ddr2_char.py`, `pumice_device.py` (docstring),
  `test_granite_char_perf.py`; model: `char_model.py`, `tests/test_char_model.py`.
- Left in MC-020: decision 2, the `t_rp_ap` CSR field (the auto-precharge
  path's own tRP per direction; +12 .. +14 on every close-page read side,
  +13 .. +17 on the bank_interleave bl4 cells in the model). It pays only at
  the phase-exact counters -- under the margin the self-close's 5 + 2 was
  already the margin tRC 7 -- so it was sequenced after this decision.
- Regressions at the new default (clean-all first): the ddr2_char_framework
  suite `run-all-func-parallel` 226 passed, 2 xfailed, 0 errors in 32:46
  (`TEST_PHASE_EXACT` unset, so the proxy ran phase-exact; the pumice char sim
  test included); the host unit tests (`test_pumice_master.py`,
  `test_pumice_device.py`, `test_harness_regmap_consistency.py`,
  `test_pumice_page_stats.py`) 32 passed; `tests/test_char_model.py` 43 passed.
  The vendor Ramulator C++ and the Python preset file are untouched by this
  step and were not re-run.
- Not re-run: the pumice controller's board numbers. `ddr2_char.py` serves
  both controllers, so a pumice board flow now derives phase-exact too; the
  pumice sim suite ran at the new default (section 6), the
  pumice board was not.
