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

The cold-boot init sequences for DDR2 and LPDDR2 are implemented as a single
FSM in `rtl/fub/init_sequencer.sv` (not separate step-package files). The FSM
issues real MRS / precharge / refresh commands to the DRAM through the command
scheduler while `init_busy_o` is high, and updates the mode-register shadow in
lockstep so the live CL / CWL / BL decode tracks what was programmed. The
`memtype_i` input selects the DDR2 or the LPDDR2 branch.

The DDR2 branch mirrors LiteDRAM's `get_ddr2_phy_init_sequence` and is proven on
the Nexys A7 board.

## DDR2 Cold Init

Per JESD79-2F. FSM states from `init_sequencer.sv`; MR data rides the ROW
request field (`init_cmd_row_o`), and the MR / EMR number is carried in the bank
index (`init_cmd_bank_o`).

| Step | State        | Command                | MR data  | Post-wait |
|------|--------------|------------------------|----------|-----------|
| 1    | `S_DFI_INIT` | assert `dfi_init_start`, wait `dfi_init_complete`, then tINIT | —        | `t_init_wait` |
| 2    | `S_PREA1`    | PRECHARGE all          | —        | `t_rp_wait` (tRP)  |
| 3    | `S_EMR2`     | MRS EMR(2)             | `0x0000` | `t_mrd_wait` (tMRD) |
| 4    | `S_EMR3`     | MRS EMR(3)             | `0x0000` | `t_mrd_wait` |
| 5    | `S_EMR1`     | MRS EMR(1)             | `0x0000` | `t_mrd_wait` |
| 6    | `S_MR0_DLL`  | MRS MR0 + DLL reset    | `0x0532` (BL4 / CL3 / tWR3 / DLL_RESET) | `t_dll_wait` (tDLLK) |
| 7    | `S_PREA2`    | PRECHARGE all          | —        | `t_rp_wait` |
| 8    | `S_REF1`     | AUTO REFRESH           | —        | `t_rfc_wait` (tRFC) |
| 9    | `S_REF2`     | AUTO REFRESH           | —        | `t_rfc_wait` |
| 10   | `S_MR0`      | MRS MR0 (DLL reset cleared) | `0x0432` | `t_mrd_wait` |
| 11   | `S_OCD_DEF`  | MRS EMR(1) + OCD default | `0x0380` | `t_mrd_wait` |
| 12   | `S_OCD_EXIT` | MRS EMR(1) + OCD exit  | `0x0000` | `t_mrd_wait` |
| 13   | `S_DONE`     | assert `init_done`     | —        | —          |

Note the JEDEC extended-mode-register order: EMR(2), then EMR(3), then EMR(1),
before MR0. The OCD-default state (`S_OCD_DEF`) leaves the MR1 shadow unchanged;
`S_OCD_EXIT` restores it to the final `0x0000` value so the live decode is
stable.

## LPDDR2 Cold Init

Per JESD209-2F. LPDDR2 uses the Mode Register Write (MRW) chain. Because the MR
address (MA) can reach MR63 / MR10 — beyond a 3-bit bank port — the sequencer
packs `{MA[5:0], OP[7:0]}` into the ROW request field, and `dfi_cmd_formatter.sv`
unpacks it (row[13:8] = MA, row[7:0] = OP) to build the bit-exact LPDDR2 CA-bus
MRW word. Only MR1 / MR2 / MR3 update the CL / CWL / BL decode shadow; MR63 and
MR10 are issued to the DRAM but not shadowed.

| Step | State       | Command                    | OP data | Post-wait               |
|------|-------------|----------------------------|---------|-------------------------|
| 1    | `S_DFI_INIT`| assert `dfi_init_start`, wait `dfi_init_complete`, then tINIT | —       | `t_init_wait`           |
| 2    | `S_L_RESET` | MRW(MR63) Reset            | `0x00`  | `t_init_wait` (tINIT4)  |
| 3    | `S_L_ZQ`    | MRW(MR10) ZQ Init Calibration | `0xFF`  | `t_dll_wait` (tZQINIT)  |
| 4    | `S_L_MR1`   | MRW(MR1) BL8 / nWR3        | `0x23`  | `t_mrd_wait` (tMRW)     |
| 5    | `S_L_MR2`   | MRW(MR2) RL3 / WL1         | `0x01`  | `t_mrd_wait`            |
| 6    | `S_L_MR3`   | MRW(MR3) DS 40 ohm         | `0x02`  | `t_mrd_wait`            |
| 7    | `S_DONE`    | assert `init_done`         | —       | —                       |

The LPDDR2 branch reuses the same CSR waits as DDR2: `t_init_wait` covers both
tINIT and tINIT4, `t_dll_wait` covers tZQINIT, and `t_mrd_wait` covers the
post-MRW tMRW delay.

LPDDR2 is now fully functional in sim: reads and writes, bit-exact JESD209-2F CA
encoding, and the full MR init chain above.

## Inter-Command Waits (CSR-Backed)

The JEDEC inter-command delays were previously hardcoded; they are now driven by
CSR fields (zero-extended to the 16-bit internal countdown). All counts are in
MC (`aclk`) cycles.

| CSR field                  | Purpose                | Reset value |
|----------------------------|------------------------|-------------|
| `INIT_TIMING0.t_init_wait` | CKE / tINIT settle     | 512         |
| `INIT_TIMING0.t_dll_wait`  | DLL lock (tDLLK)       | 256         |
| `INIT_TIMING1.t_mrd_wait`  | post mode-register (tMRD) | 8        |
| `INIT_TIMING1.t_rp_wait`   | post precharge (tRP)   | 8           |
| `INIT_TIMING1.t_rfc_wait`  | post auto-refresh (tRFC) | 16        |

Init is a one-time event, so generous margins are fine — the reset defaults
comfortably cover the JEDEC minimums at the on-board clock rate. Simulation
programs shorter `INIT_TIMING*` values to keep test runtimes practical; there is
no separate scaling parameter — the shorter waits are just smaller CSR values.

## Power-State Transitions

Self-refresh and deep-power-down transitions are handled by the optional
`powerdown_ctrl.sv` power-state FSM, not by the init sequencer. On an idle
threshold it requests a low-power state and drops CKE (`dfi_cke_o`); it wakes on
any new controller activity. The two supported entry modes are:

- Precharge Power Down (PDE) — CKE low, banks may stay active.
- Self Refresh (SR) — CKE low plus the SRE command; the DRAM self-refreshes
  internally and the controller stops issuing REFs.

Self-refresh entry requires all banks precharged first (the scheduler enforces
this precondition before granting). Self-refresh exit timing (tXSDLL for DDR2 /
tXSR for LPDDR2) is enforced by the scheduler; the power-state FSM itself only
drops and restores CKE.

LPDDR2 Deep Power Down (DPD) is supported as a planned power-state entry (CKE
low after precharge-all). DPD exit loses DRAM content, so the full LPDDR2 cold
init sequence above must run again.
