# ISSUE-023: perf-proxy DRAM checker anchors tWR on an uncalibrated CWL + BL, so every write-row close counts a phantom violation

> Source: pumice TASK-044 (2026-10-23), reading `model_violations` beside
> the command-gap traces instead of past it.
> Related: `test_ddr2_char_perf.py::_calibrated_checker` (keeps CL / CWL / BL
> at the DFI slave's original values on purpose: the slave's read return and
> write capture are timed off them), RDS-DV `dram_state.py`
> (`on_precharge`, `on_auto_precharge`), the "a passing sim must prove its
> config" rule.

**Priority:** P2
**Status:** closed 2026-10-29 (anchor fixed in the proxy, zero asserted, mutation-checked; see the closing entry)
**Owner:** TBD

## Finding

`_calibrated_checker` rescales the JEDEC intervals to MC cycles but leaves
CL / CWL / BL at the slave's values (documented reason: the DFISlavePHY
times its data off `dram.timings.CL / CWL`). The model's tWR check does
not use tWR alone: `on_write` sets
`last_wr_data_cycle = cycle + CWL + BL - 1` and `on_precharge` requires
`PRE >= last_wr_data_cycle + tWR`. With the slave's CWL and BL (DFI-beat
units, not CK) that anchor is ~7 MC cycles after the WR command, so the
model demands PRE at WR + 9 while the controller's `t_wr` CSR (4 MC cycles
= WL + BL/2 + tWR at 150 MHz CK, JEDEC-correct) closes at WR + 6.

Measured on col_major, one generator, txn 256 (256 write rows):

| core | close | `tWR` count | `tRP` count |
|---|---|---|---|
| FR-FCFS, explicit PRE | before and after TASK-044 | 256 / 258 | 0 |
| BANK_PICK, explicit PRE (2026-10-22 run) | - | 256 | 0 |
| FR-FCFS, WRA (close-on-drain) | TASK-044 | 4 | 251 |

The read side is clean in every run (RDA: no tRTP, no tRP), so the anchor
is the only cause. The WRA row moved the phantom from tWR to tRP because
`on_auto_precharge` now records the device's internal close at
`last_wr_data_cycle + tWR` and times the next ACT against it: same wrong
anchor, next check down the chain.

## Why it matters

The counter is the proxy's only JEDEC verdict. 256 phantom tWR (or tRP)
per run hides a real one, and the earlier passes (BUG-030, the three-way
table) were read without this number.

## Fix shape

Give the checker a WR-to-PRE anchor in the controller's units: either
calibrate CWL / BL for the TIMING checks separately from the data-path
values the slave uses (two fields, or a `tWR_anchor_cycles` override), or
express the DDR2 write recovery as a single `WR command -> PRE` interval
the way the controller does. Then assert the count is zero in the proxy.

## Not this issue

The explicit-PRE `tRTP` and the RDA paths are correctly modeled (zero
counts at the floor).

## Fix (2026-10-29)

Taken the second way: the checker keeps the slave's CL / CWL / BL for the
data path and gets the write-recovery anchor in the controller's unit.
`test_ddr2_char_perf.py` installs `_McAnchoredDram`, a `DramStateModel`
whose `on_write` sets `last_wr_data_cycle = WR + wr_to_pre_cycles -
tWR_cycles`; the proxy sets `wr_to_pre_cycles` to the `tWR` field it has
just programmed (`set_jedec_timings`, 4 MC cycles at 75 MHz = WL + BL/2 +
tWR in CK), so the model's own `+ tWR_cycles` lands PRE exactly where the
controller's bank timer does, and tWTR reads off the same last-beat point.
Nothing in the RDS-DV model changed. The proxy now asserts the whole
soft-violation dict is empty: the counter is its one JEDEC verdict and a
nonzero entry is a real violation.

Measured, clean build, pumice proxy at 75 MHz, four families:
`model_violations = {}`, 1 passed in 382 s; the granite proxy (which
shares `_bringup`) 1 passed in 242 s. Mutation: the anchor line replaced
by `pass` reproduces the item exactly ("PRE bank=N only -3 cycles after
last WR data beat (needs tWR=2)" on every write-row close) and the new
assert fails the test (1 failed in 384 s). The counts before the fix were
read without this assert; the three-way table and BUG-030 stand on their
bandwidth columns, which never depended on it.
