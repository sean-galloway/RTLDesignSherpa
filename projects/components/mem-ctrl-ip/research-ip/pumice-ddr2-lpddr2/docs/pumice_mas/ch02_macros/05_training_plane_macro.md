<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Training plane macro — `mc_training_plane` instantiation

**Module:** `mc_training_plane` (common IP)  
**Location:** `projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_training_plane.sv`  
**Category:** Plane-4 macro in `pumice_core` (maintenance traffic for LPDDR2)  
**Instance:** `u_train_plane` (`rtl/top/pumice_core.sv:756-798`)  
**Child FUBs (pumice build):** `mc_lpddr2_zq_ctrl` (`u_zq`, slot 0) + `mc_lpddr2_dq_cal` (`u_lp_cal`, slot 1), around `mc_training_shell` (`u_shell`: one-active `trn_cmd` mux and the mc_clk/dfi_clk CDC)  
**Status:** implemented and FUB-tested (ZQ control, DQ calibration)

> The plane is documented in [common_mas chapter 5: `mc_training_plane`](../../../../../common-ip/docs/common_mas/ch05_training_plane/01_mc_training_plane.md). Until 2026-10-11 pumice reached the shell through its own `pumice_training_plane` wrapper around pumice-local `pumice_zq_ctrl` / `pumice_lp_cal`; those FUBs moved into common-ip as `mc_lpddr2_zq_ctrl` / `mc_lpddr2_dq_cal`, the plane now composes them itself, and the wrapper was removed. `pumice_core` builds the plane with `NUM_SLOTS = 2`, `EXTRA_WIDTH = 1`, `CAL_DATA_WIDTH = DFI_DATA_WIDTH`, `HAS_LP_ZQ = 1`, `HAS_LP_DQ_CAL = 1`.

## Purpose

LPDDR2 needs two kinds of calibration traffic that DDR2 simply doesn't have:
periodic ZQ calibration (ZQCS/ZQCL — LPDDR2 has no dedicated command, so both
are MRW writes to MR10) and DQ calibration (MRR reads of MR32/MR40 against
which firmware sweeps the PHY read-delay taps). Both are maintenance-class:
they need the bus to themselves, they can wait, and they must never invent
their own command encodings. This plane is where they live.

`mc_training_plane` holds the two FUBs, muxes both onto the single
`trn_cmd` maintenance channel into the scheduler plane's arbiter, and (in
`mc_training_shell`) owns all of the mc_clk/dfi_clk clock crossing for the
read-aligner calibration sideband. Run gating (`init_done && memtype ==
MEMTYPE_LPDDR2`) lives inside the two FUBs, not in the plane — the plane is
wiring and arbitration.
For DDR2 builds both FUBs are inert: no ZQ pin, no MRR.

The DQ-vs-tap sweep itself deliberately stays outside the core (the scoria/
andesite doctrine: cores are DFI-clean, no FPGA-primitive logic). The plane
exposes `cal_start`/`cal_abort` CSRs and the MRR engine; board firmware walks
the taps and compares each lane against patterns A/B.

## FUBs

| FUB             | Role |
|-----------------|------|
| `mc_lpddr2_zq_ctrl` | Periodic ZQ calibration. Counts down `zq_interval`, requests the arbiter on expiry, holds the post-grant bus-quiet window (`t_zqcs`/`t_zqcl`) that comes back as `cal_busy`. Mode-C deferral holds the request under sustained demand and escalates an overdue deferral to ZQCL. |
| `mc_lpddr2_dq_cal`  | One-shot DQ-calibration sequencer. On `cal_start`: MRR to MR32, capture the first return beat, wait `t_mrr`, MRR to MR40, capture, done. Sticky `cal_done`/`cal_err`; abort via `cal_abort`. |

## The One-Active Mux

Both FUBs want the same `trn_cmd` channel, so the plane arbitrates: ZQ wins,
because it is periodic maintenance with a real expiry behind it, while DQ
calibration is a firmware-initiated one-shot that can wait a few hundred cycles
without anything drifting. ZQ sits on shell slot 0 and DQ calibration on slot
1, and `mc_training_shell` selects the lowest-numbered requesting slot; the
channel payload is just the selected FUB's payload, with one wrinkle — the
command kind, carried as the slot's extra bit:

| `trn_cmd_*` output | ZQ selected (slot 0)  | DQ cal selected (slot 1) |
|--------------------|-----------------------|------------------------|
| `trn_cmd_op_o`     | `w_zq_op` (always `OP_MRS`) | `OP_MRS`         |
| `trn_cmd_row_o`    | `{4'd0, MR10, OP}` (`0x56` ZQCS / `0xAB` ZQCL) | `{4'd0, MA, 8'd0}` (MR32=32 / MR40=40, OP=0) |
| `trn_cmd_mrr_o`    | `0` (MRW)             | `1` (MRR)              |
| `trn_cmd_bank_o`   | `0`                   | `0`                    |

Grant is returned to the selected slot only: `slot_grant_o[g] =
slot_req_i[g] && trn_cmd_grant_i && (w_sel == g)`. The arbiter passes the granted op verbatim onto the command
output — neither the mux nor the arbiter re-encodes maintenance commands.

## External Boundaries

- **Maintenance channel out (to `mc_scheduler_plane`'s `maint_*` slot):** `trn_cmd_req_o`,
  `trn_cmd_op_o`, `trn_cmd_bank_o[2:0]`, `trn_cmd_row_o[17:0]`,
  `trn_cmd_mrr_o`; `trn_cmd_grant_i` back. Wired in `pumice_core.sv`
  (`maint_col_i` tied `'0`, `cal_busy_o` onto `maint_busy_i`). The arbiter grants only when
  all banks are idle, nothing row-affecting is in flight or inside its guard
  window, and no REF recovery is running — see
  [ch02/07](../ch02_blocks/07_scheduler.md) and
  [ch04/05](../ch04_apb_config/05_training_interface_contracts.md).
- **CSR controls in (from `pumice_top` hwif):** `zq_en_i`, `zq_defer_en_i`,
  `zq_interval_i[31:0]`, `t_zqcs_i[15:0]`, `t_zqcl_i[15:0]`,
  `zq_overdue_max_i[12:0]`, `cal_start_i`, `cal_abort_i`,
  `t_mrr_i[15:0]`, `t_readout_i[15:0]` — the `CAL_*` register block
  (§4.2). Config-drive, like every other CSR field: no staging, no
  quiet point.
- **DFI-plane calibration sideband (dfi_clk domain):** `cal_expect_o` down
  to the read aligner, `cal_data_i`/`cal_valid_i` back with the captured
  beat. See [ch02/18](../ch02_blocks/18_rd_data_path.md).
- **Telemetry out (CAL_STATUS and MRR data registers):** `cal_busy_o` (ZQ hold or DQ cal
  running), `cal_done_o`/`cal_err_o` (sticky), `mrr32_data_o`/
  `mrr40_data_o` (full DFI read width each), `zq_busy_o`, `zq_overdue_o`,
  `zqcs_total_o[15:0]`.

## CDC Discipline

All mc_clk/dfi_clk crossing for the calibration sideband lives in
`mc_training_shell`, using the repo's standard cells:

- `cal_expect_o` crosses down through `sync_pulse` (3 stages) — a single
  mc_clk assertion from `mc_lpddr2_dq_cal` becomes exactly one dfi_clk pulse,
  which arms the aligner sideband.
- Captured data crosses up through `cdc_synchronizer` (`WIDTH =
  DFI_DATA_WIDTH`, 3 flops). This is safe because the aligner holds the
  captured beat stable until the next arm — a multi-flop synchronizer is
  sufficient, no handshake required.
- `cal_valid_i` crosses up through `sync_pulse` so the mc_clk-side FSM sees
  a single-cycle "data landed" strobe.

## Parameters

| Parameter        | Pumice value | Meaning                              |
|------------------|--------------|--------------------------------------|
| `NUM_SLOTS`      | 2            | Shell slots: ZQ (0) and DQ cal (1). |
| `BKW` / `ROW_WIDTH` | core `BKW` / `ROW_WIDTH` | Maintenance bank/row field widths. |
| `EXTRA_WIDTH`    | 1            | Per-slot extra bit = MRR flag. |
| `CAL_DATA_WIDTH` | `DFI_DATA_WIDTH` (128 default) | Full DFI read-data width; sizes `cal_data_i`, `mrr32_data_o`, `mrr40_data_o`, and the up-synchronizer. |
| `HAS_LP_ZQ` / `HAS_LP_DQ_CAL` | 1 / 1 | Build both LPDDR2 clients. |

## Tests

The training plane and both clients are common-ip (`mc_training_shell`,
`mc_lpddr2_zq_ctrl`, `mc_lpddr2_dq_cal`). No pumice test drives calibration
today: nothing under `dv/tests/top/` writes `CAL_CTRL.cal_start` or enables
ZQ, and `pumice_core_tb_top.sv` ties every training input to 0. The directed tests
that used to sit in this area -- `test_pumice_scheduler_plane.py`
(training priority vs refresh/demand, the hold window, fire==valid),
`test_pumice_zq_ctrl.py` and `test_pumice_lp_cal.py` -- were removed from the pumice area 2026-10-13 (pumice tests target only pumice DUTs); no common-ip replacement exists yet.

## Open Questions / Future Work

- **Multi-rank ZQ overlap.** Pumice board targets are single-rank, so a
  shared-ZQ-resistor overlap policy is untested; `mc_lpddr2_zq_ctrl` has no
  per-rank loop yet.
- **Temperature-driven refresh.** The MRR engine makes MR4 reads possible,
  but tREFI derating on temperature class is not built.
- **Self-refresh-exit ZQCL.** Pumice has no power-down path (`powerdown_ctrl` was removed), so
  no ZQCL-on-self-refresh-exit trigger exists.
