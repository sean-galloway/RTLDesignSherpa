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

# Init Sequencer (`init_sequencer`)

**Module:** `init_sequencer.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `pumice_mem_cmd_scheduler`
**Status:** Implemented — DDR2 and LPDDR2 sequences both complete (DDR2 validated on the Nexys A7 board; LPDDR2 passes the full sim suite for family reuse)

> **Renamed / re-scoped:** an early sketch called this an `init_engine_fub`
> built on a microprogram step-record ROM (opcodes, a step interpreter FSM,
> `SIM_INIT_SCALE`, `WAIT_FOR_BIT` polling, ZQ retry loops, an `init_error`
> path, IRQ outputs, and a CSR MR-override path). **None of that ROM
> machinery was built.** The implemented module is a small hard-coded FSM
> that issues a fixed JEDEC bring-up sequence. It drives MR-write strobes into
> [`mode_register`](20_mode_register.md) (which owns the MR shadow + live
> CL/CWL/BL decode), and it issues the real DRAM commands (PRECHARGE, REFRESH,
> MRS/MRW) through the command path while `init_busy_o` is high.

---

## Purpose

`init_sequencer` walks the JEDEC cold-boot DRAM initialization sequence — the
deterministic recipe of DFI init handshake, PRECHARGE-ALL, mode-register
loads, and REFRESH settling that must complete before any normal traffic can
issue. It is memtype-specific: `memtype_i` selects between the DDR2 sequence
(mirrors LiteDRAM's proven Nexys A7 recipe) and the LPDDR2 MRW sequence
(JEDEC JESD209-2F).

Two things happen for each mode-register step:

1. A real DRAM command is issued. The sequencer drives a single-cycle command
   request (`init_cmd_valid_o` / `init_cmd_op_o` / `init_cmd_bank_o` /
   `init_cmd_row_o`) that the parent scheduler forwards to
   [`dfi_cmd_formatter`](14_cmd_encoder.md). Because the scheduler stays
   idle during init (it owns nothing else while `init_busy_o` is high) and the
   formatter is always `cmd_ready`, a single-cycle pulse issues exactly one
   command — no grant handshake is needed.
2. The `mode_register` shadow is updated in lockstep (`mr_seq_we_o`) so the
   controller's live CL/CWL/BL decode tracks what was actually programmed.

The init sequencer sits above the scheduler in the command-priority hierarchy.
`init_done_o` also drives [`refresh_ctrl`](11_refresh_mgr.md)`.enable_i` —
periodic refresh does not start until init reports done.

> **History (why the sequence is "full").** An earlier version was a
> "simplified" 4-MR shadow-only walk that never issued MRS/PRECHARGE/REFRESH to
> the DRAM. On the DFI-loopback sim the memory model stores/returns data
> regardless of init state, so it passed. On real DDR2 the read DLL never
> locked (no proper reset + refresh sequence) and no IDELAY tap found a read
> eye. The full sequence documented here fixed on-board bring-up.

---

## Synthesis Parameters

| Parameter    | Default | Effect                                                             |
|--------------|---------|--------------------------------------------------------------------|
| `ROW_WIDTH`  | 14      | Width of the `init_cmd_row_o` request field (carries MR data; must hold DDR2 MR0=0x533 which needs bit 10, so a narrower COL-based path would truncate). |
| `NUM_BANKS`  | 8       | Number of DRAM banks.                                              |
| `BKW`        | derived | `$clog2(NUM_BANKS)` — width of `init_cmd_bank_o` (bank / MR index). |

There is no `MEMTYPE` synthesis parameter — the sequence is selected at
run-time by the `memtype_i` input, so one elaboration supports both families.

---

## Interface

### Clock / reset

| Signal     | Direction | Description                              |
|------------|-----------|------------------------------------------|
| `mc_clk`   | input     | Memory-controller clock.                 |
| `mc_rst_n` | input     | Active-low async reset (house macros).   |

### Configuration

| Signal        | Direction | Width | Description                              |
|---------------|-----------|-------|------------------------------------------|
| `memtype_i`   | input     | enum  | `MEMTYPE_DDR2` selects the DDR2 sequence; anything else selects the LPDDR2 MRW chain. |

### JEDEC init-sequence waits (CSR-backed, MC cycles)

All countdowns run internally as 16-bit values; the 8-bit inputs are
zero-extended. Defaults live in the CSR (mentioned as 512 / 256 / 8 / 8 / 16),
so these were promoted from hardcoded constants to `INIT_TIMING`-programmable.

| Signal          | Width | Internal name | JEDEC parameter                         |
|-----------------|-------|---------------|-----------------------------------------|
| `t_init_wait_i` | 16    | `W_INIT`      | CKE / tINIT settle (also LPDDR2 tINIT4). |
| `t_dll_wait_i`  | 16    | `W_DLL`       | DLL lock tDLLK (also LPDDR2 tZQINIT).    |
| `t_mrd_wait_i`  | 8     | `W_MRD`       | tMRD, post mode-register-set.            |
| `t_rp_wait_i`   | 8     | `W_RP`        | tRP, post precharge.                     |
| `t_rfc_wait_i`  | 8     | `W_RFC`       | tRFC, post auto-refresh.                 |

### DFI status

| Signal                | Direction | Description                                                       |
|-----------------------|-----------|-------------------------------------------------------------------|
| `dfi_init_start_o`    | output    | Asserted (registered) once `r_state != S_RESET`. Tells the PHY to begin its own init. |
| `dfi_init_complete_i` | input     | PHY reports its DLL-lock / IO training complete. Gates the exit from `S_DFI_INIT`. |

### MR-shadow write port (muxed with CSR by `pumice_mem_cmd_scheduler`)

| Signal           | Direction | Width | Description                          |
|------------------|-----------|-------|--------------------------------------|
| `mr_seq_we_o`    | output    | 1     | Write-enable strobe into `mode_register`. |
| `mr_seq_index_o` | output    | 5     | MR index (0..3) being shadowed.      |
| `mr_seq_data_o`  | output    | 16    | MR data being shadowed.              |

### DRAM command request into the scheduler (issued while init_busy)

| Signal             | Direction | Width       | Description                                         |
|--------------------|-----------|-------------|-----------------------------------------------------|
| `init_cmd_valid_o` | output    | 1           | Single-cycle command pulse.                         |
| `init_cmd_op_o`    | output    | `dram_op_e` | `OP_PREA`, `OP_REF`, or `OP_MRS`.                   |
| `init_cmd_bank_o`  | output    | `BKW`       | MR index for MRS (DDR2) / bank field.               |
| `init_cmd_row_o`   | output    | `ROW_WIDTH` | MR data for MRS on the wide row path (see MR tables). |

### Legacy ZQCL handshake (DDR3+; unused for DDR2/LPDDR2)

| Signal          | Direction | Description                                          |
|-----------------|-----------|------------------------------------------------------|
| `zqcl_req_o`    | output    | Tied to 0 — DDR2 has no ZQCL command.                |
| `zqcl_grant_i`  | input     | Unused (tied off via a `_unused` sink).              |

### Status

| Signal        | Direction | Description                                                        |
|---------------|-----------|--------------------------------------------------------------------|
| `init_busy_o` | output    | Registered; high whenever `r_state != S_DONE`. Reset value is 1.   |
| `init_done_o` | output    | Registered; high when `r_state == S_DONE`. Drives `refresh_ctrl.enable_i`. |

---

## FSM

A single 5-bit `state_e` enum drives everything. Each command state is occupied
for exactly one cycle (an unconditional transition to `S_WAIT`), so the
combinational command decode produces a single-cycle pulse per command. `S_WAIT`
holds for the programmed inter-command delay: it counts `r_wait` down and, when
it reaches zero, jumps to `r_next` (the resume state latched by the command
state).

| State        | Value | Role                                                        | Wait after (into S_WAIT) |
|--------------|-------|-------------------------------------------------------------|--------------------------|
| `S_RESET`    | 0     | Reset entry; unconditionally advances.                      | — (→ `S_DFI_INIT`)       |
| `S_DFI_INIT` | 1     | Wait for `dfi_init_complete_i`, then arm `W_INIT`.          | `W_INIT`                 |
| `S_PREA1`    | 2     | DDR2: Precharge All (pre-EMR).                              | `W_RP` → `S_EMR2`        |
| `S_EMR3`     | 3     | DDR2: MRS EMR(3).                                           | `W_MRD` → `S_EMR1`       |
| `S_EMR2`     | 4     | DDR2: MRS EMR(2).                                           | `W_MRD` → `S_EMR3`       |
| `S_EMR1`     | 5     | DDR2: MRS EMR(1).                                           | `W_MRD` → `S_MR0_DLL`    |
| `S_MR0_DLL`  | 6     | DDR2: MRS MR0 + DLL reset (MR0.VAL | 0x100; reset 0x533).                          | `W_DLL` → `S_PREA2`      |
| `S_PREA2`    | 7     | DDR2: Precharge All (pre-refresh).                          | `W_RP` → `S_REF1`        |
| `S_REF1`     | 8     | DDR2: Auto Refresh #1.                                      | `W_RFC` → `S_REF2`       |
| `S_REF2`     | 9     | DDR2: Auto Refresh #2.                                      | `W_RFC` → `S_MR0`        |
| `S_MR0`      | 10    | DDR2: MRS MR0, DLL-reset bit cleared (MR0.VAL; reset 0x433).              | `W_MRD` → `S_OCD_DEF`    |
| `S_OCD_DEF`  | 11    | DDR2: MRS EMR(1) + OCD default (0x380).                    | `W_MRD` → `S_OCD_EXIT`   |
| `S_OCD_EXIT` | 12    | DDR2: MRS EMR(1) + OCD exit (0x000).                       | `W_MRD` → `S_DONE`       |
| `S_WAIT`     | 13    | Inter-command countdown; `r_wait==0` → `r_next`.           | —                        |
| `S_DONE`     | 14    | Terminal; `init_done_o` high, self-loop.                   | —                        |
| `S_L_RESET`  | 15    | LPDDR2: MRW(MR63) Reset.                                    | `W_INIT` → `S_L_ZQ`      |
| `S_L_ZQ`     | 16    | LPDDR2: MRW(MR10) ZQ Init Calibration.                     | `W_DLL` → `S_L_MR1`      |
| `S_L_MR1`    | 17    | LPDDR2: MRW(MR1) BL8 / nWR3.                                | `W_MRD` → `S_L_MR2`      |
| `S_L_MR2`    | 18    | LPDDR2: MRW(MR2) RL3 / WL1.                                 | `W_MRD` → `S_L_MR3`      |
| `S_L_MR3`    | 19    | LPDDR2: MRW(MR3) drive strength 40ohm.                     | `W_MRD` → `S_DONE`       |

`memtype_i` only branches once: on exit from `S_DFI_INIT`, `r_next` is set to
`S_PREA1` for DDR2 or `S_L_RESET` otherwise. From there each path is a fixed
chain of command states separated by `S_WAIT`.

`S_DONE` is a hard self-loop — there is no restart, no `init_error`, and no
software-triggered re-run in the RTL. A fresh init requires `mc_rst_n`.

---

## DDR2 Sequence

Mirrors LiteDRAM's `get_ddr2_phy_init_sequence` (upstream `litedram/init.py`), the
reference proven on the Nexys A7:

1. Assert `dfi_init_start_o`; wait `dfi_init_complete_i` (PHY runs its own
   DLL-lock / IO training). Then wait `W_INIT` (tINIT / CKE settle).
2. Precharge All (`S_PREA1`), wait `W_RP`.
3. Load the extended mode registers in JEDEC JESD79-2 order **EMR(2), EMR(3),
   EMR(1)** — the state chain is `S_EMR2 → S_EMR3 → S_EMR1` — each followed by
   `W_MRD`. (Note the enum numbering: `S_EMR2` = 4, `S_EMR3` = 3, so the values
   are out of numeric order but the executed order is 2 → 3 → 1.)
4. Load MR0 + DLL reset (`S_MR0_DLL`, MR0.VAL | 0x100; reset 0x533: BL8 / CL3 / tWR3, DLL_RESET);
   wait `W_DLL` for the DLL to lock (~200 DRAM clocks).
5. Precharge All (`S_PREA2`), wait `W_RP`.
6. Auto Refresh x2 (`S_REF1`, `S_REF2`), each followed by `W_RFC`.
7. Load MR0 with the DLL-reset bit cleared (`S_MR0`, MR0.VAL; reset 0x433); wait `W_MRD`.
8. EMR(1) + OCD Default (`S_OCD_DEF`, 0x380) → EMR(1) + OCD Exit
   (`S_OCD_EXIT`, 0x000).
9. `S_DONE`: `init_done_o = 1`.

MR data is carried on `init_cmd_row_o` (ROW_WIDTH wide, MR index on
`init_cmd_bank_o`), because MR0 = 0x533 sets bit 10 and a 10-bit column-based
path would truncate it.

### DDR2 MR values

Localparams, transcribed exactly:

| Symbol          | Value    | State        | Meaning                                   | Shadowed? |
|-----------------|----------|--------------|-------------------------------------------|-----------|
| `DDR2_MR0_DLL`  | `MR0.VAL \| 0x100` (reset `0x0533`) | `S_MR0_DLL`  | MR0: BL8 / CL3 / tWR3, DLL_RESET ORed in. | Yes (MR0) |
| `DDR2_MR0`      | `MR0.VAL` (reset `0x0433`) | `S_MR0`      | MR0 with DLL_RESET cleared.               | Yes (MR0) |
| `DDR2_MR1`      | `0x0000` | `S_EMR1`, `S_OCD_EXIT` | EMR(1): Rtt disabled, ODS full. | Yes (MR1) |
| `DDR2_MR1_OCD`  | `0x0380` | `S_OCD_DEF`  | EMR(1) + OCD calibration default.         | No — transient calibration; shadow left at final EMR value. |
| `DDR2_MR2`      | `0x0000` | `S_EMR2`     | EMR(2).                                   | Yes (MR2) |
| `DDR2_MR3`      | `0x0000` | `S_EMR3`     | EMR(3).                                   | Yes (MR3) |

`DDR2_MR0_DLL` decomposes as `log2(BL=4)=2 | (CL=3<<4)=0x30 | (tWR=3<<9)=0x400 =
0x433`, plus `reset_dll = 1<<8 = 0x100`, giving 0x533. OCD default = `EMR |
(7<<7) = 0x380`; OCD exit = `EMR = 0`.

---

## LPDDR2 Sequence

JEDEC JESD209-2F §3.4.1 power-up + §3.5 mode registers:

1. Assert `dfi_init_start_o`; wait `dfi_init_complete_i`; wait `W_INIT` (tINIT
   settle).
2. MRW(MR63) = Reset (`S_L_RESET`, OP don't-care); wait `W_INIT` (tINIT4).
3. MRW(MR10) = 0xFF ZQ Init Calibration (`S_L_ZQ`); wait `W_DLL` (tZQINIT).
4. Configure the device: MRW(MR1) = BL8 / nWR3 (`S_L_MR1`, 0x23),
   MRW(MR2) = RL3 / WL1 (`S_L_MR2`, 0x01), MRW(MR3) = DS 40ohm
   (`S_L_MR3`, 0x02) — each followed by `W_MRD` (tMRW).
5. `S_DONE`.

The CSR waits are reused: `W_INIT` covers tINIT4, `W_DLL` covers tZQINIT,
`W_MRD` covers post-MRW settling.

LPDDR2 mode-register writes must reach indices up to MR63, which a 3-bit bank
port cannot express. So the index (MA) and data (OP) are packed together into
the wide row request by the `mrw_row()` function as `{MA[5:0], OP[7:0]}`
(`init_cmd_row_o[13:8]` = MA index, `init_cmd_row_o[7:0]` = OP data);
`dfi_cmd_formatter` unpacks this for the LPDDR2 CA MRW word.

### LPDDR2 MR values

| Symbol           | OP value | State        | Meaning                       | Shadowed?               |
|------------------|----------|--------------|-------------------------------|-------------------------|
| `LPDDR2_MR63_OP` | `0x00`   | `S_L_RESET`  | MRW(63) Reset (OP don't-care). | No — issued, not shadowed (MR63 exceeds the 5-bit index). |
| `LPDDR2_MR10_OP` | `0xFF`   | `S_L_ZQ`     | MR10 ZQ Init Calibration.     | No — issued, not shadowed. |
| `LPDDR2_MR1_OP`  | `0x23`   | `S_L_MR1`    | MR1: nWR3 \| BL8.             | Yes (MR1).              |
| `LPDDR2_MR2_OP`  | `0x01`   | `S_L_MR2`    | MR2: RL3 / WL1.               | Yes (MR2).              |
| `LPDDR2_MR3_OP`  | `0x02`   | `S_L_MR3`    | MR3: DS 40ohm.                | Yes (MR3).              |

Only MR1 / MR2 / MR3 update the `mode_register` shadow (`mr_seq_we_o`), because
those are the registers that feed the CL/CWL/BL decode. MR63 and MR10 are
issued to the DRAM but not shadowed.

---

## Init-Busy Gating

`init_busy_o` is high from reset (its reset value is 1) through every state
except `S_DONE`. While busy:

- The parent `pumice_mem_cmd_scheduler` forwards the sequencer's command
  request to `dfi_cmd_formatter` and issues nothing of its own — the scheduler
  parks so exactly one command reaches DFI per `init_cmd_valid_o` pulse.
- `refresh_ctrl.enable_i` is low (driven by `init_done_o`), so periodic refresh
  does not start until init completes.

When the FSM reaches `S_DONE`, `init_busy_o` drops and `init_done_o` rises;
the scheduler and refresh controller take over normal operation.

---

## Verification Notes (cocotb test plan)

| Scenario                                                                           | What it proves                                              |
|------------------------------------------------------------------------------------|-------------------------------------------------------------|
| DDR2 init from cold reset to `init_done_o`                                         | Full DDR2 state chain executes in order.                    |
| Observe the DDR2 command stream: PREA, MRS×3 (EMR2/EMR3/EMR1), MRS MR0_DLL, PREA, REF×2, MRS MR0, MRS OCD_DEF, MRS OCD_EXIT | Exact JEDEC order + op/index/data on each `init_cmd_*` pulse. |
| DDR2 MR values on `init_cmd_row_o` match 0x533 / 0x433 / 0x380 / 0x000 (MR0.VAL resets) | Wide row path carries bit 10 without truncation.            |
| LPDDR2 init from cold reset to `init_done_o`                                       | Full LPDDR2 MRW chain executes.                             |
| LPDDR2 `mrw_row()` packing: MR63/MR10 reach the DRAM; only MR1/MR2/MR3 set `mr_seq_we_o` | Index/data packing + selective shadowing.             |
| `dfi_init_complete_i` held low → FSM stalls in `S_DFI_INIT`, `init_busy_o` stays high | DFI handshake gating.                                   |
| Each command state produces exactly one `init_cmd_valid_o` cycle, then `S_WAIT`   | Single-cycle pulse behavior.                                |
| Program short `t_*_wait_i` values → inter-command `S_WAIT` countdown matches       | CSR-backed wait timing.                                     |
| `mr_seq_*` shadow tracks the MRS writes (MR0/MR1/MR2/MR3 for DDR2)                 | Shadow lockstep with issued commands; OCD_DEF not shadowed. |
| After `init_done_o`, `refresh_ctrl.enable_i` asserts and refresh begins            | Init → refresh handoff.                                     |

---

## Open Questions / Future Work

- **No restart / error path.** `S_DONE` is terminal and there is no
  `init_error`, timeout, or software-triggered re-run — a fresh init requires
  `mc_rst_n`. If a DFI handshake never completes, the FSM simply parks in
  `S_DFI_INIT` forever. A future variant could add a timeout on
  `dfi_init_complete_i` and a status/restart CSR, but that machinery is not in
  the current RTL.
- **MR4 readback (LPDDR2).** LPDDR2 supports reading MR4 for device temperature
  class. The current sequencer only writes mode registers; it does no MRR
  readback. Folding a temperature read into or after init is possible future
  work but is not implemented.
- **ZQCL / ZQCS.** The `zqcl_req_o` / `zqcl_grant_i` ports exist only as a
  legacy DDR3+ handshake and are tied off; DDR2 has no ZQCL and LPDDR2 does its
  ZQ init via the MR10 MRW. If the family is extended to DDR3/DDR4, this port
  becomes a real ZQ-calibration handshake and the FSM would gain a ZQ state.
- **Per-rank MRS.** The sequencer issues a single stream of commands with no
  rank iteration; multi-rank support would require a rank field and a per-rank
  MRS loop. Out of scope for the current single-rank Nexys A7 target.
