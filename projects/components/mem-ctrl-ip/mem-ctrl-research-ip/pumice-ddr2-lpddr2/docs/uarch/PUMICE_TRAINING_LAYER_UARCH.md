# PUMICE training layer — LPDDR2 ZQ calibration and DQ read training

This document describes the macro-level training layer added to pumice for
LPDDR2: periodic ZQ calibration (`pumice_zq_ctrl`) and one-shot DQ calibration
via mode-register reads (`pumice_lp_cal`). Both are maintenance-class traffic
that share a single command channel into the scheduler's arbiter.

## 1. Scope and run gating

The training layer only operates for LPDDR2 (`memtype_i == MEMTYPE_LPDDR2`) and
after initialization completes (`init_done_i`). DDR2 has no ZQ pin and no MRR
mechanism, so both FUBs are inert for DDR2 builds.

## 2. Sub-blocks

### 2.1 `pumice_zq_ctrl` — periodic ZQ calibration

LPDDR2 has no dedicated ZQCS/ZQCL command; both are MRW writes to MR10
(OP = `0x56` for ZQCS, `0xAB` for ZQCL). The FUB:

- Counts down `t_zqcs_interval_i` MC cycles between calibrations.
- Requests the scheduler arbiter when the interval expires.
- Holds a post-grant quiet window (`t_zqcs_i` or `t_zqcl_i` cycles) during which
  `cal_busy_o` is asserted and demand-class traffic is blocked.
- Supports deferral under sustained demand when `zq_defer_en_i` is set; an
  overdue deferral escalates to ZQCL.
- Outputs the MRW row as `{MA[5:0]=10, OP[7:0]}` on its 18-bit `zq_row_o`.

### 2.2 `pumice_lp_cal` — one-shot MRR DQ calibration

Issues MRR reads to MR32 (pattern A) and MR40 (pattern B), captures the first
return beat of each, and exposes the captured data to firmware:

- Started by a pulse on `cal_start_i`; cancelled by `cal_abort_i`.
- Waits for arbiter grant, then pulses `cal_expect_o` for one cycle to arm the
  DFI-layer read aligner.
- Captures the first `dfi_rddata_valid_i` beat after the arm and stores it.
- Waits `t_mrr_i` cycles between MR32 and MR40.
- Sets sticky `cal_done_o` after MR40 capture; sets sticky `cal_err_o` if either
  read times out (`t_readout_i`).
- Outputs MRR row as `{MA[5:0], OP[7:0]=0}` on its 18-bit `cmd_row_o`.

### 2.3 `pumice_training_layer` — arbitration and CDC

- One-active arbitration between ZQ and lp_cal: ZQ has priority because it is
  periodic maintenance; lp_cal is a firmware-initiated one-shot.
- Selects MRW (ZQ) vs MRR (lp_cal) via `trn_cmd_mrr_o`.
- Crosses `cal_expect_o` from `mc_clk` to `dfi_clk` with `sync_pulse`.
- Crosses the captured calibration data from `dfi_clk` back to `mc_clk` with a
  multi-flop synchronizer (`cdc_synchronizer`) plus `sync_pulse` for the valid
  strobe.

## 3. Scheduler interface

The training layer connects to `pumice_scheduler_layer` / `pumice_cmd_arbiter`
on a dedicated maintenance-class channel:

| Signal | Direction | Description |
|--------|-----------|-------------|
| `trn_cmd_req_o`   | out | Training requests arbitration |
| `trn_cmd_grant_i` | in  | Arbiter grant |
| `trn_cmd_op_o`    | out | Always `OP_MRS` |
| `trn_cmd_bank_o`  | out | `0` (MR index lives in row) |
| `trn_cmd_row_o`   | out | `{MA[5:0], OP[7:0]}` |
| `trn_cmd_mrr_o`   | out | `1` for MRR, `0` for MRW |
| `cal_busy_i`      | in  | From ZQ/lp_cal post-grant hold |

Arbiter priority (highest to lowest):
1. Refresh / init
2. Training (this channel)
3. Demand read/write

`cal_busy_i` is folded into the arbiter's `w_out_safe` so that demand-class
commands and ACT cannot fire while calibration holds the bus quiet.

## 4. DFI-layer calibration sideband

`pumice_dfi_rd_aligner` exposes:

| Signal | Direction | Description |
|--------|-----------|-------------|
| `cal_expect_i` | in  | Single-cycle arm from training layer (dfi_clk domain) |
| `cal_data_o`   | out | Captured first beat, held until next arm |
| `cal_valid_o`  | out | Single-cycle pulse when data is captured |

The sideband is mutually exclusive with normal read traffic: the arbiter
guarantees no read is outstanding when calibration is active, so the capture
FSM cannot collide with the read FIFO path.

## 5. CSR exposure

The training layer is controlled and observed through the `CAL_CTRL`,
`CAL_ZQ_INTERVAL`, `CAL_ZQ_TIMING`, and `CAL_TRAIN_TIMING` register blocks, plus
status registers `CAL_STATUS`, `CAL_MRR32_DATA`, and `CAL_MRR40_DATA`. See
`rtl/macro/pumice_csr.rdl` for field definitions and reset values.

## 6. Verification

- FUB: `dv/tests/fub/test_pumice_zq_ctrl.py`, `dv/tests/fub/test_pumice_lp_cal.py`
- Formatter: `dv/tests/fub/test_dfi_cmd_formatter.py::lpddr2_mrr`
- Read aligner: `dv/tests/fub/test_pumice_dfi_rd_aligner.py::test_pumice_dfi_rd_aligner_cal_capture`
- Scheduler: `dv/tests/macro/test_pumice_scheduler_layer.py::test_pumice_scheduler_layer_training`
