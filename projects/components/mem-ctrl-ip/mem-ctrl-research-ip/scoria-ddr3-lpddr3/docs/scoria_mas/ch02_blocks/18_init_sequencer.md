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

# Init Sequencer (`scoria_init_sequencer`)

**Module:** `scoria_init_sequencer.sv`
**Location:** `rtl/fub/`
**Category:** control / initialization
**Parent:** `scoria_scheduler_layer`
**Status:** landed and sim-verified

## Purpose

`scoria_init_sequencer` owns the DRAM power-up handshake. It drives `RESET#`, raises `CKE`, programs the mode-register set in JEDEC order, issues `ZQCL`, waits out `tDLLK` and `tZQinit`, and then releases the scheduler to normal traffic. The block is NEW relative to pumice because DDR3 adds the `RESET#` pin and a shorter init sequence than DDR2; the LPDDR3 chain is inherited from pumice's LPDDR2 path, reusing the same `{MA[5:0], OP[7:0]}` MRW packing.

The sequencer issues real commands through the scheduler's init passthrough while `init_busy_o` is high. Each command state occupies one cycle, then the FSM parks in `S_WAIT` for the JEDEC inter-command delay. The mode-register shadow is updated in lockstep via `mr_seq_we_o` so live CL/CWL/BL decode tracks what was programmed.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `ROW_WIDTH` | int | — | 14 | width of `init_cmd_row_o`; carries MR data for MRS and `{MA, OP}` for LPDDR3 MRW |
| `NUM_BANKS` | int | — | 8 | number of DRAM banks; determines `BKW` |
| `BKW` | int | — | `$clog2(NUM_BANKS)` | bank/MR-index width on `init_cmd_bank_o` |

: Table 2.18.1: Init sequencer build parameters

All timing values are runtime CSRs, not parameters. That is the family rule: a timing compiled in cannot be swept, and a controller that cannot be swept cannot be characterized.

## Interface

### Clocks, reset, configuration, and DFI status

| Signal | Direction | Width | Description |
|---|---|---|---|
| `mc_clk` | in | 1 | controller clock |
| `mc_rst_n` | in | 1 | active-low reset |
| `memtype_i` | in | `memtype_e` | `MEMTYPE_DDR3` or `MEMTYPE_LPDDR3` |
| `dram_reset_n_o` | out | 1 | `RESET#` to top/PHY; latched released at `S_D3_CKE` |
| `dfi_init_start_o` | out | 1 | asserted from `S_RESET` until `S_DONE` |
| `dfi_init_complete_i` | in | 1 | PHY reports init complete; gates exit from `S_DFI_INIT` |

: Table 2.18.2: Clocks, reset, configuration, and DFI status

### JEDEC init-sequence waits (CSR-backed)

| Signal | Direction | Width | Description |
|---|---|---|---|
| `t_init_wait_i` | in | 16 | CKE / `tINIT` settle wait |
| `t_dll_wait_i` | in | 16 | `tDLLK` DLL lock wait |
| `t_xpr_wait_i` | in | 16 | `tXPR` = max(`tXS`, 5 tCK) after CKE high |
| `t_zqinit_wait_i` | in | 16 | `tZQinit` after `ZQCL` |
| `t_mrd_wait_i` | in | 8 | `tMRD` between MRS commands |
| `t_rp_wait_i` | in | 8 | `tRP` after precharge (unused on DDR3 init) |
| `t_rfc_wait_i` | in | 8 | `tRFC` after refresh (unused on DDR3 init) |

: Table 2.18.3: JEDEC timing CSR inputs

### Mode-register values, restart, and shadow port

| Signal | Direction | Width | Description |
|---|---|---|---|
| `mr0_i` | in | 16 | MR0 base value (BL/CL/tWR) |
| `mr1_i` | in | 16 | MR1 value (ODT, ODS, DLL enable) |
| `mr2_i` | in | 16 | MR2 value |
| `mr3_i` | in | 16 | MR3 value |
| `init_restart_i` | in | 1 | rising edge re-runs the JEDEC chain from `S_RESET` |
| `mr_seq_we_o` | out | 1 | pulse: capture `mr_seq_data_o` into shadow MR[`mr_seq_index_o`] |
| `mr_seq_index_o` | out | 5 | MR index (0..3) |
| `mr_seq_data_o` | out | 16 | MR value to shadow |

: Table 2.18.4: Mode-register inputs, restart, and shadow write port

### Command request and status

| Signal | Direction | Width | Description |
|---|---|---|---|
| `init_cmd_valid_o` | out | 1 | single-cycle pulse: issue this init command |
| `init_cmd_op_o` | out | `dram_op_e` | command opcode (`OP_MRS`, `OP_ZQCL`, etc.) |
| `init_cmd_bank_o` | out | `BKW` | bank address; for MRS this is the MR index |
| `init_cmd_row_o` | out | `ROW_WIDTH` | MR data for MRS; `{MA[5:0], OP[7:0]}` for LPDDR3 MRW |
| `zqcl_req_o` | out | 1 | tied low; `ZQCL` is issued through the command stream |
| `zqcl_grant_i` | in | 1 | unused; tied off at source |
| `init_busy_o` | out | 1 | high while init is in progress (tied off in scheduler layer) |
| `init_done_o` | out | 1 | high when FSM reaches `S_DONE` |

: Table 2.18.5: Command request, legacy handshake, and status outputs

The `init_cmd_valid_o` pulse is accepted by the scheduler's init passthrough without a grant handshake. During init the scheduler stays in `S_IDLE` and `dfi_cmd_formatter` is always `cmd_ready`, so a single-cycle pulse issues exactly one command.

## Microarchitecture internals

### FSM state list

```text
S_RESET
S_DFI_INIT
    DDR3 branch:
        S_D3_RSTN, S_D3_CKE, S_D3_XPR
        S_D3_MR2, S_D3_MR3, S_D3_MR1, S_D3_MR0
        S_D3_ZQCL, S_D3_LOCK
    LPDDR3 branch:
        S_L_RESET, S_L_ZQ, S_L_MR1, S_L_MR2, S_L_MR3
S_WAIT
S_DONE
```

### DDR3 initialization sequence

```text
S_RESET -> S_DFI_INIT -> S_D3_RSTN -> S_D3_CKE -> S_D3_XPR
S_D3_XPR -> S_D3_MR2 -> S_D3_MR3 -> S_D3_MR1 -> S_D3_MR0
S_D3_MR0 -> S_D3_ZQCL -> S_D3_LOCK -> S_DONE
```

The MR order is JESD79-3F's, not sorted. MR1 carries DLL enable and MR0 carries DLL reset, so the order encodes a dependency.

### LPDDR3 initialization sequence

```text
S_RESET -> S_DFI_INIT -> S_L_RESET -> S_L_ZQ
S_L_ZQ -> S_L_MR1 -> S_L_MR2 -> S_L_MR3 -> S_DONE
```

LPDDR3 MRW uses `init_cmd_row_o` packed as `{MA[5:0], OP[7:0]}` because the 3-bit bank path cannot reach MR10 or MR63. MR63 and MR10 are issued to the DRAM but not shadowed; only MR1, MR2, and MR3 update the shadow.

### MR0 DLL reset handling

The MR0 command issued to the DRAM ORs in `DDR3_DLL_RESET = 16'h0100` (MR0 A8). The bit is self-clearing per JESD79-3F 3.4.2.4, so no second MR0 load is needed. The shadow is written with the unmodified `mr0_i` so the live CL/CWL/BL decode tracks the steady-state value rather than the reset pulse.

### `dram_reset_n_o` latch

`dram_reset_n_o` is asserted from reset until the FSM reaches `S_D3_CKE`, then released and never re-asserted without a controller reset or an `init_restart_i` pulse. The latch avoids the one-cycle/low-window hazards that come from decoding the pin directly off the FSM state set. For LPDDR3, which has no `RESET#` pin, the output reads high throughout.

## FSM policy

The block has **one FSM** and it is the init FSM. There are no nested state machines. Command states occupy exactly one cycle each; the inter-command waits live in `S_WAIT`, which decrements a CSR-loaded counter until zero and then resumes `r_next`. The `r_next` register captures the state to resume before entering `S_WAIT`.

## Timing

Every wait state counts from a CSR-loaded value captured on entry, so a CSR written mid-wait does not affect the running count. Values are runtime CSRs initialized from the JESD79-3F or JESD209-2F speed bin at CSR-derivation time.

| Wait | Symbol | Loaded from | Counted in |
|---|---|---|---|
| RESET# low to CKE high | `tINIT` | `t_init_wait_i` | MC clocks |
| CKE high to first MRS | `tXPR` | `t_xpr_wait_i` | MC clocks |
| Between MRS commands | `tMRD` | `t_mrd_wait_i` | MC clocks |
| `ZQCL` to ready | `tDLLK`, `tZQinit` | `t_dll_wait_i`, `t_zqinit_wait_i` | MC clocks, the larger of the two |
| LPDDR3 reset settle | `tINIT` | `t_init_wait_i` | MC clocks |
| LPDDR3 ZQ init | `tZQinit` | `t_dll_wait_i` | MC clocks |

: Table 2.18.6: Init-sequence timing windows

## Notes

- **`zqcl_req_o` and `init_busy_o` are intentionally tied off** in the scheduler layer. `ZQCL` is issued through the ordinary command stream, and the scheduler derives init occupancy from the command stream rather than from `init_busy_o`.
- **Re-initialization:** A rising edge on `init_restart_i` forces the FSM back to `S_RESET` and replays the MRS chain with the current CSR MR values. `init_done_o` falls immediately so the scheduler stops admitting host commands.
- **Ordering checks** — for example, that MR2 precedes MR0 — are assertions in DV, not in RTL. The FSM encodes the order, and DV proves the FSM never strays.
- **`t_rp_wait_i` and `t_rfc_wait_i`** are accepted for compatibility with the broader timing CSR set but are unused during DDR3 or LPDDR3 initialization.
