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

# Training-Layer Interface Contracts

> Wire-level contracts for the interfaces the LPDDR2 calibration/training
> layer added at rev 0.8. Block behavior lives in
> [ch02/23](../ch02_blocks/23_zq_ctrl.md),
> [ch02/24](../ch02_blocks/24_lp_cal.md), and
> [ch02/25](../ch02_macros/05_training_layer_macro.md); the registers are in
> [§4.2](02_csr_map.md). Every row below is transcribed from committed RTL —
> the file:line citations are the contract.

---

## Contract: scheduler command FIFO word (MRR flag)

**Source.** `rtl/macro/pumice_scheduler_layer.sv` — pack at the `w_cmd_wr_data`
assign, unpack at `w_cmd_rd_data`.

The arbiter-to-DFI command FIFO word grew one bit for training: the MRR
flag rides on top of the demand-path fields. MSB first:

| Field  | Width         | Meaning                                            |
|--------|---------------|----------------------------------------------------|
| `mrr`  | 1             | 1 = MRR (mode-register read); 0 = normal / MRW     |
| `ap`   | 1             | auto-precharge verdict carried with the pick       |
| `col`  | `COL_WIDTH`   | column address                                     |
| `row`  | `ROW_WIDTH`   | row address (MR index + OP packing for MRS/MRR)    |
| `bank` | `BKW`         | bank address                                       |
| `rank` | `RKW`         | rank (single-rank today)                           |
| `op`   | 4             | `dram_op_e`; MRR rides as `OP_MRS` + `mrr = 1`     |

`CMD_W = 4 + RKW + BKW + ROW_WIDTH + COL_WIDTH + 1 + 1`. `dram_op_e` is not
widened — all 16 opcodes were consumed, and MRR never enters the demand
path. The word is a `gaxi_fifo_sync` data width; the only pack/unpack sites
are the scheduler layer and `pumice_dfi_cmd_path`, so no external consumer
sees the packing.

The arbiter registers the flag with the decision:
`r_cmd_mrr <= w_do_trn ? trn_cmd_mrr_i : 1'b0` — demand-class commands
always carry `mrr = 0`, so a set flag by construction means a maintenance
MRR got through.

## Contract: formatter MRR CA word

**Source.** `rtl/fub/dfi_cmd_formatter.sv` — `OP_MRS` branch; JESD209-2F §5.12.

For `OP_MRS`, the formatter already builds the MRW CA word; MRR is the same
word with one bit inverted:

| CA bit  | MRR value | Meaning                                        |
|---------|-----------|------------------------------------------------|
| `CA3r`  | H (`cmd_mrr_i`) | 0 = MRW, 1 = MRR — the only difference   |
| `CA4r..CA9r` | `MA[5:0]` | mode-register address, low half           |
| `CA0f`  | `MA[6]`   | mode-register address, high half                 |
| `CA1f`  | `MA[7]`   | mode-register address, high half                 |
| `CA2f..CA9f` | `OP[7:0]` | operation field; 0 for MRR (`mrr_row()`), `0x56`/`0xAB` for ZQCS/ZQCL |
| `CA0r..CA2r` | L      | fixed low for MRS-class                         |

So the MRR command word is `CA0r=L, CA1r=L, CA2r=L, CA3r=H` with the MR
select `{CA1f, CA0f, CA9r..CA4r}` = `MA[7:0]` — identical field packing to
MRW, `CA3r` inverted. The ZQCS/ZQCL opcodes themselves remain NOP at the
formatter (`default` branch): LPDDR2 ZQ is pure MRW, so no formatter change
was needed for ZQ.

## Contract: read-aligner calibration sideband

**Source.** `rtl/fub/pumice_dfi_rd_aligner.sv` — calibration capture block;
CDC owned by `pumice_training_layer`.

| Signal          | Domain   | Direction (aligner) | Contract                                       |
|-----------------|----------|---------------------|------------------------------------------------|
| `cal_expect_i`  | dfi_clk  | in                  | single-cycle arm; set the capture flag         |
| `cal_data_o`    | dfi_clk  | out               | first `dfi_rddata_valid` beat after the arm, held until the next arm |
| `cal_valid_o`   | dfi_clk  | out               | single-cycle pulse when the beat is captured   |

Behavior: `cal_expect_i` sets `r_cal_armed`; the next cycle with any
`dfi_rddata_valid_i` beat latches `dfi_rddata_i` into `r_cal_data`, raises
`cal_valid_o` for one cycle, and clears the flag. The normal read FIFO push
path is untouched — the arbiter grant contract guarantees no read is
outstanding when calibration is active, so the sideband cannot collide with
a returning demand read. Crossing into mc_clk for `pumice_lp_cal` is a
`cdc_synchronizer` on data (held stable by this register) plus a
`sync_pulse` on valid.

## Contract: `trn_cmd` maintenance arbitration

**Source.** `rtl/fub/pumice_cmd_arbiter.sv` — priority pick, `w_trn_safe`,
grant output; channel driven by `pumice_training_layer`.

The training layer is one more maintenance client on the arbiter, in
priority order:

```text
init > refresh > trn (training) > demand
```

Same shape scoria uses (ZQ below refresh there, same here). The contract
rows:

| # | Term | Contract |
|---|------|----------|
| 1 | Request payload | `trn_cmd_req_i/op_i/bank_i/row_i/mrr_i` from the training-layer mux; the granted op passes **verbatim** onto the command output — the arbiter never re-encodes maintenance commands |
| 2 | Grant safety (`w_trn_safe`) | all banks idle (`!w_any_active`), no ACT/PRE in flight (`!w_inflight_preact`), both guard windows clear (`r_guard0/1 == 0`), no REF recovery (`!w_rfc_busy`), no in-flight write data (satisfied by the scheduler draining the write path before `trn_cmd_req_i` asserts) |
| 3 | Priority | training picks only when init is done and no refresh request/drain is pending; it never preempts either, and demand never preempts it |
| 4 | Grant return | `trn_cmd_grant_o = w_fire_out && r_do_trn` — the grant is the fired command, so grant and issue cannot diverge |
| 5 | Post-grant hold | `cal_busy` from the training layer folds into `w_out_safe`; all demand-class fires are blocked during the ZQ/lp_cal bus-quiet window |

Row 5 is the BUG-003 discipline applied again: the new gate lives in
`w_out_safe`, never in the pick cone, so `w_fire_out == cmd_valid_o &&
cmd_ready_i` holds by construction.

## Contract: CSR map additions

**Source.** `rtl/macro/pumice_csr.rdl` — full field-level detail in
[§4.2](02_csr_map.md).

Seven registers added at 0x0A0–0x0F0 (free range between `OBS_ROW_HIT`
0x080–0x09F and the retired 0x0C0 hole; retired holes are never reused):

| Offset | Register | Acc | Reset | Contents |
|--------|----------|-----|-------|----------|
| 0x0A0 | `CAL_CTRL` | rw | `0x00000000` | `zq_en[0]`, `zq_defer_en[1]` (Mode C), `cal_start[4]` (self-clearing strobe), `cal_abort[5]` (strobe), `zq_overdue_max[28:16]` (0 = no cap) |
| 0x0A4 | `CAL_ZQ_INTERVAL` | rw | `0x00000000` | 32-bit ZQCS interval in MC cycles, 0 = off |
| 0x0A8 | `CAL_ZQ_TIMING` | rw | `0x00000000` | `t_zqcs[15:0]`, `t_zqcl[31:16]` post-grant hold windows |
| 0x0AC | `CAL_TRAIN_TIMING` | rw | `0x00020000` | `t_mrr[15:0]` = 2 (JEDEC tMRR), `t_readout[31:16]` MRR issue→data timeout |
| 0x0B0–0x0BC | `CAL_MRR32_DATA[4]` | ro | `0` (hw-written) | first captured DFI read-data beat for MRR MR32 (pattern A), four 32-bit slices |
| 0x0E0–0x0EC | `CAL_MRR40_DATA[4]` | ro | `0` (hw-written) | first captured DFI read-data beat for MRR MR40 (pattern B), four 32-bit slices |
| 0x0F0 | `CAL_STATUS` | ro | `0x00000000` | `zq_busy[0]`, `cal_busy[1]`, `cal_done[2]` (sticky), `cal_err[3]` (sticky), `zq_overdue[4]`, `zqcs_total[31:16]` |

The sticky done/err bits survive `cal_abort` and clear on soft reset (a
fresh `cal_start` re-arms them). Config-drive applies like everywhere else
in this map: a written field tracks straight into the datapath, no staging
or quiet point (see [§4.1](01_apb_interface_spec.md)).
