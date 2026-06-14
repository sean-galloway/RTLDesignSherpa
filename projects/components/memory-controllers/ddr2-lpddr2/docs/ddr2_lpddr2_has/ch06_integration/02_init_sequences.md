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

# Init Sequences

The full cold-boot init sequences for DDR2 and LPDDR2. These are the step lists embedded in `ddr2_init_steps_pkg.sv` and `lpddr2_init_steps_pkg.sv`.

## DDR2 Cold Init

Per JESD79-2F §4.1 and Micron TN-47-09.

| Step | Type             | Description                                                     |
|------|------------------|-----------------------------------------------------------------|
| 1    | `SET_CTRL_BITS`  | Power stable; CKE = 0 for ≥ 200 µs                              |
| 2    | `DELAY`          | NOP for ≥ 400 ns                                                |
| 3    | `SET_CTRL_BITS`  | CKE → 1, ODT = 0, RESET_N = 1                                   |
| 4    | `ISSUE_CMD`      | PRECHARGE all banks (PREA with addr[10] = 1)                    |
| 5    | `MRS_LOAD`       | EMRS(2) = 0 (extended mode register 2 defaults)                 |
| 6    | `MRS_LOAD`       | EMRS(3) = 0                                                     |
| 7    | `MRS_LOAD`       | EMRS(1) = enable DLL                                            |
| 8    | `MRS_LOAD`       | MRS = reset DLL + initial CL / BL                               |
| 9    | `ISSUE_CMD`      | PRECHARGE all                                                   |
| 10   | `ISSUE_CMD`      | AUTO REFRESH (REF)                                              |
| 11   | `ISSUE_CMD`      | AUTO REFRESH (REF)                                              |
| 12   | `MRS_LOAD`       | MRS = final CL / BL / WR config (no DLL reset)                  |
| 13   | `MRS_LOAD`       | EMRS(1) = OCD default                                           |
| 14   | `MRS_LOAD`       | EMRS(1) = OCD exit                                              |
| 15   | `END`            | Assert `init_done`                                              |

Real-time delays embedded in `post_delay`: step 1 = 200 µs; step 2 = 400 ns; step 3 = 200 ns NOPs; intermediate MRS steps = tMRD (≥ 2 clocks).

## LPDDR2 Cold Init

Per JESD209-2F §6.1 and Micron TN-46-22.

| Step | Type             | Description                                                     |
|------|------------------|-----------------------------------------------------------------|
| 1    | `SET_CTRL_BITS`  | tINIT1: CKE low ≥ 100 ns                                        |
| 2    | `SET_CTRL_BITS`  | tINIT2: CKE high ≥ 200 µs                                       |
| 3    | `DELAY`          | tINIT3: NOP ≥ 11 µs                                             |
| 4    | `MRS_LOAD`       | MR63 reset                                                      |
| 5    | `DELAY`          | tINIT5: ≥ 10 µs                                                 |
| 6    | `MRS_LOAD`       | MR10 ZQ calibration                                             |
| 7    | `WAIT_FOR_BIT`   | Wait `dfi_init_complete` (ZQ done)                              |
| 8    | `MRS_LOAD`       | MR1: BL, WRAP, BT                                               |
| 9    | `MRS_LOAD`       | MR2: RL, WL                                                     |
| 10   | `MRS_LOAD`       | MR3: drive strength                                             |
| 11   | `MRS_LOAD`       | MR4 read for temperature class (programs internal tREFI scale)  |
| 12   | `MRS_LOAD`       | MR16: PASR bank mask (default 0 = all banks refresh)            |
| 13   | `MRS_LOAD`       | MR17: PASR segment mask (default 0)                             |
| 14   | `END`            | Assert `init_done`                                              |

Real-time delays embedded in `post_delay`: step 1 = 100 ns; step 2 = 200 µs; step 3 = 11 µs; step 5 = 10 µs; step 7 timeout = 1 ms; subsequent MRS = tMRD.

## Self-Refresh Entry (Both Memtypes)

Used during power-state FSM transitions:

| Step | Type             | Description                                            |
|------|------------------|--------------------------------------------------------|
| 1    | `WAIT_FOR_BIT`   | Wait for all banks idle and refresh complete           |
| 2    | `ISSUE_CMD`      | PRECHARGE all                                          |
| 3    | `SET_CTRL_BITS`  | CKE low + ODT off (initiates self-refresh)             |
| 4    | `END`            | FSM transitions to SELF_REFRESH state                  |

## Self-Refresh Exit (Both Memtypes)

| Step | Type             | Description                                            |
|------|------------------|--------------------------------------------------------|
| 1    | `SET_CTRL_BITS`  | CKE high (initiates self-refresh exit)                 |
| 2    | `DELAY`          | tXSNR (~200 ns)                                        |
| 3    | `END`            | FSM transitions to ACTIVE                              |

## LPDDR2 Deep Power Down Entry

| Step | Type             | Description                                            |
|------|------------------|--------------------------------------------------------|
| 1    | `WAIT_FOR_BIT`   | Wait for all banks idle and refresh complete           |
| 2    | `ISSUE_CMD`      | PRECHARGE all                                          |
| 3    | `ISSUE_CMD`      | DPD command (special LPDDR2 encoding)                  |
| 4    | `SET_CTRL_BITS`  | CKE low                                                |
| 5    | `END`            | FSM transitions to DPD state                           |

## LPDDR2 Deep Power Down Exit

DPD exit loses DRAM content; the full cold-init sequence (LPDDR2 init above) must run again. The DPD exit step table is effectively just:

| Step | Type             | Description                                            |
|------|------------------|--------------------------------------------------------|
| 1    | `JUMP_TO_TABLE`  | Restart the LPDDR2 cold init step table from step 1    |

This is implemented by having the power-state FSM signal `init_engine` to restart, rather than a separate step table.

## Sim Scaling

All `post_delay` fields are scaled by `SIM_INIT_SCALE` during simulation. For example, a 200 µs delay (about 20,000 cycles at 100 MHz) becomes 20 cycles at `SIM_INIT_SCALE = 1000`. This keeps test runtimes practical without changing the step table logic. Silicon builds always use `SIM_INIT_SCALE = 1`.
