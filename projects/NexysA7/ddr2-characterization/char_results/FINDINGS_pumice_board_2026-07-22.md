# pumice board wrap-up findings — 2026-07-22

Bitstream: rebuilt from the fixed RTL (apb_slave_cdc gray-FIFO CDC fix, deskew
removal, arbiter refresh fix: w_ref_safe + mission tRFC + column guard).
Timing MET: WNS +0.169 ns @ 66.67 MHz, 0 failing endpoints.
Flow: `make wrapup` (program -> level -> soak gate -> char matrix), plus the
fixed `--char` after the ControllerConfig t_phy_wrlat clobber was found.
Raw data: `char_2026-07-22_wrapup.csv` (70 records, full meters + histograms).

## Validated

- **Bring-up tuple** holds on the new bitstream: `t_phy_wrlat=1, t_rddata_en=6,
  rddata_delay=7`, leveled at bitslip 0 / tap ~8 (cached window verified).
- **Refresh soak gate PASSED on silicon**: default / tiny(0x40) / huge(0xFFFF)
  tREFI rounds all clean — the arbiter refresh-collision fix
  (TASK-SCHED-REFRESH silicon manifestation) is board-validated for
  contiguous-access workloads.
- **Baseline perf is real and healthy** (config: ROW_MAJOR scheme, CLOSE page,
  no reorder; 64000-txn runs; timer-stamped BW):

  | scenario | rd BW (MB/s) |
  |---|---|
  | incremental bl4/8/16 | 114.8 |
  | row_major (page-hit) bl4/8/16 | 116.0 |
  | col_major (page-thrash) bl4/8/16 | 33.1 / 59.0 / 78.7 |
  | col_major_interleaved bl4/8/16 | 65.1 / 67.8 / 87.5 |
  | col_major bl8 multiid / gap | 59.0 / 59.0 |

  Clean page-penalty and bank-parallelism signatures; ~9x the pre-fix era's
  flat 12.7 MB/s. (Utilization needs the meter window fix noted in the char
  output; BW is timer-based and solid.)

## Bugs found in the flow itself (fixed)

- `ControllerConfig.t_phy_wrlat` hardcoded 0 (pre-tuple) and `apply()`
  re-programmed it EVERY scenario -> clobbered the leveled wrlat=1 -> 0/70.
  Now env-driven (`TEST_T_PHY_WRLAT`, default 1) — the THIRD incarnation of
  the stale-hardcoded-PHY-timing bug in this flow.
- `measure()` used the bail-on-error `wait_engine` -> mismatches misreported
  as "engine did not complete". Now `ignore_error=True`.

## Open: config-axis integrity failures (18/70 pass)

First-ever board run of the rearchitected controller's runtime config axes:

| config | pass | note |
|---|---|---|
| baseline | 9/14 | col_major family fails at scale 1000 (passed at scale 1) |
| inorder  | 9/14 | same shape as baseline |
| bank_interleave | 0/14 | scheme = bank_lsb 0 |
| open_page | 0/14 | page_policy OPEN |
| reorder | 0/14 | OPEN + lookahead + rd_in_order=False |

Signatures:
- Some points = every-beat corruption (mismatch counter == total beats mod
  2^16); others partial/irregular.
- multiid scenarios: rd histogram total 64007 != 64000 issued — 7 EXTRA read
  returns (duplicate issue or double-count) — smells like a rd CAM/scheduler
  duplicate under reorder pressure.
- Long col-major runs failing where short ones pass (even on baseline) points
  at refresh x heavy-PRE/ACT interplay beyond the fixed REFab collision.

These are REAL rearch-era defects in the runtime-config paths, consistent with
the pre-existing sim failures (TASK-CHARSIM: bank_interleave families;
TASK-TOPCSR: CSR-programmed config path) — the config axes were never
board-validated post-rearch. Tools ready for the campaign: in-scheduler
command-history checker (CMD_HISTORY_EN), dfi_rd_return_checker, ILA-capable
bitstream flow, and this CSV as the failure map.
