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

# Init Sequencer and Power-Down

Cold-boot bring-up is handled by `init_sequencer`; low-power entry/exit by `powerdown_ctrl`.

## `init_sequencer`

### Purpose

Sequence post-reset DRAM bring-up: the DFI init handshake, JEDEC mode-register loads, precharge, and refresh. RTL: `rtl/fub/init_sequencer.sv`. It is a compact hard-coded FSM (not a microprogram ROM). Its commands are **issued to the DRAM**, not merely shadowed — this was the fix for the on-board bring-up failure where an earlier shadow-only walk left the read DLL unlocked.

### Command Path

While `init_busy_o` is high, the scheduler stays idle and forwards the sequencer's single-cycle command pulses (`init_cmd_valid_o` / `init_cmd_op_o` / `init_cmd_bank_o` / `init_cmd_row_o`) straight to `dfi_cmd_formatter`. Each command state is occupied for exactly one cycle, then the FSM parks in `S_WAIT` for the JEDEC inter-command delay before advancing. Because `dfi_cmd_formatter` is always `cmd_ready`, a single-cycle pulse issues exactly one command with no grant handshake.

The `mode_register` shadow is updated in lockstep (`mr_seq_we_o` / `mr_seq_index_o` / `mr_seq_data_o`) so the live CL/CWL/BL decode tracks what was programmed.

### CSR-Backed Waits

The inter-command delays are CSR-backed (INIT_TIMING registers), zero-extended into a 16-bit countdown, rather than hardcoded:

| Input            | JEDEC          | Default |
|------------------|----------------|---------|
| `t_init_wait_i`  | CKE / tINIT    | 512     |
| `t_dll_wait_i`   | DLL lock tDLLK | 256     |
| `t_mrd_wait_i`   | tMRD           | 8       |
| `t_rp_wait_i`    | tRP            | 8       |
| `t_rfc_wait_i`   | tRFC           | 8       |

### DDR2 Sequence

Mirrors LiteDRAM's DDR2 PHY init (the reference proven on the Nexys A7 board):

1. Assert `dfi_init_start_o`; wait `dfi_init_complete_i` (the PHY runs its own DLL-lock / IO training), then wait tINIT.
2. Precharge All.
3. EMRS in JEDEC order EMRS(2) then EMRS(3) then EMRS(1) — all defaults 0.
4. MRS(0) + DLL reset (`0x532` = BL4/CL3/tWR3/DLL_RESET); wait tDLLK.
5. Precharge All.
6. Auto Refresh x2 (each followed by tRFC).
7. MRS(0) without DLL reset (`0x432`) — clears the reset bit.
8. EMRS(1) + OCD default (`0x380`) then EMRS(1) + OCD exit (`0x000`).
9. `init_done_o = 1`.

The DDR2 MR values are `localparam` constants (MR0 `0x432`/`0x532`, MR1 `0x0000`, OCD default `0x380`, MR2/MR3 `0x0000`).

### LPDDR2 Sequence (fully functional)

Per JESD209-2F power-up and mode-register configuration:

1. Assert `dfi_init_start_o`; wait `dfi_init_complete_i`; tINIT settle.
2. MRW(MR63) = Reset (OP don't-care).
3. MRW(MR10) = `0xFF` ZQ Init Calibration.
4. MRW(MR1) = `0x23` (BL8 / nWR3), MRW(MR2) = `0x01` (RL3 / WL1), MRW(MR3) = `0x02` (DS 40 ohm).
5. `init_done_o = 1`.

Only MR1/MR2/MR3 update the CL/CWL/BL decode shadow; MR63/MR10 are issued to the DRAM but not shadowed (they exceed the 5-bit shadow index). The MR index (MA, up to MR63) and data (OP) are carried packed as `{MA[5:0], OP[7:0]}` in the ROW request field, so `dfi_cmd_formatter` can build the full LPDDR2 CA MRW word — a 3-bit bank port alone could not reach MR10/MR63.

### Memtype Selection

`memtype_i` (from the PHY_TIMING CSR: 0 = DDR2, 1 = LPDDR2) chooses the sequence at runtime. After the shared DFI-init step, DDR2 branches to `S_PREA1` and LPDDR2 to `S_L_RESET`.

### Status Outputs

| Signal             | Purpose                                        |
|--------------------|------------------------------------------------|
| `dfi_init_start_o` | High after leaving reset                        |
| `init_busy_o`      | High until the FSM reaches `S_DONE`             |
| `init_done_o`      | Asserted at `S_DONE`                            |
| `zqcl_req_o`       | Tied off — DDR2 has no ZQCL                      |

---

## `powerdown_ctrl`

### Purpose

Idle-detect into a low-power state. RTL: `rtl/fub/powerdown_ctrl.sv`. It is available but not in the default top build; it is documented here for completeness.

### Modes

- **PDE (Precharge Power Down)** — CKE low, banks may stay active. Wakes on new activity within ~tXPDLL cycles.
- **SR (Self Refresh)** — CKE low plus an SRE command issued by the scheduler; the DRAM self-refreshes internally and the controller stops issuing REFs. Exit requires SRX plus tXSDLL (DDR2) / tXSR (LPDDR2) before new commands. SR entry requires all banks precharged first (the scheduler enforces the precondition).

### Selection

- `enable_sref_i` high: on the idle threshold, request SR (`pdn_kind_o = 1`).
- `enable_sref_i` low, `enable_pde_i` high: request PDE (`pdn_kind_o = 0`).
- neither: never request.

### Scope / TODO

Deep Power Down (LPDDR2), per-rank power-down, and the `dfi_dram_clk_disable` cooperation with `dfi_signal_pack` are documented TODOs. The block currently powers down all ranks together and trusts the scheduler not to grant before init completes.
