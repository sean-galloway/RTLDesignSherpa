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

# Top-Level Integration (`ddr2_lpddr2_ctrl`)

**Module:** `ddr2_lpddr2_ctrl.sv`
**Location:** `rtl/top/`
**Category:** TOP (Structural only — no behavioral logic)
**Status:** Skeleton

---

## Purpose

`ddr2_lpddr2_ctrl` is the controller's top-level integration. It is **pure structural wiring** — every behavioral statement belongs in a FUB. The role of the top is:

1. Declare the external port list (see §1.2)
2. Instantiate every FUB
3. Wire FUB↔FUB interfaces
4. Fan-out per-rank / per-bank / per-phase signals where the FUB count is parametric

## Instantiation Inventory

| Instance Name        | FUB                     | Count                  | Notes                                       |
|----------------------|-------------------------|------------------------|---------------------------------------------|
| `u_axi4_slave`       | `axi4_slave_fub`        | 1                      | Single AXI4 slave port                      |
| `u_addr_mapper`      | `addr_mapper`       | 1                      | Combinational; no clock                     |
| `u_rd_cmd_cam`       | `rd_cmd_cam`        | 1                      | Read-side CAM                               |
| `u_wr_cmd_cam`       | `wr_cmd_cam`        | 1                      | Write-side CAM                              |
| `u_txn_queue`        | `txn_queue_fub`         | 1                      | Unified pending queue                       |
| `u_scheduler`        | `scheduler`         | 1                      |                                             |
| `u_page_predictor`   | `page_predictor_fub`    | 0 or 1                 | Conditional on `PAGE_POLICY == HAPPY_HYBRID`|
| `u_bank_machine[r][b]` | `bank_machine_fub`    | `NUM_RANKS × NUM_BANKS`| `generate` block, two-dimensional           |
| `u_xbank_timers`     | `xbank_timers`      | 1                      | Internally per-rank tRRD/tFAW + global tCCD |
| `u_refresh_mgr`      | `refresh_mgr_fub`       | 1                      |                                             |
| `u_init_engine`      | `init_engine_fub`       | 1                      |                                             |
| `u_power_state`      | `power_state_fub`       | 1                      |                                             |
| `u_cmd_encoder`      | `cmd_encoder_fub`       | 1                      | Parameterized by `MEMTYPE`                  |
| `u_gear_dfi`         | `gear_dfi_fub`          | 1                      |                                             |
| `u_odt_ctrl`         | `odt_ctrl_fub`          | 1                      |                                             |
| `u_wr_data_path`     | `wr_data_path_fub`      | 1                      |                                             |
| `u_rd_data_path`     | `rd_data_path_fub`      | 1                      |                                             |
| `u_csr_apb`          | `csr_apb_fub`           | 1                      | Only FUB in `apb_pclk` domain               |

## Generate Blocks

The only parametric-fanout instances are the bank machines, fan-out arrays of per-rank CSRs, and per-rank ODT/CKE outputs:

```systemverilog
generate
    for (genvar r = 0; r < NUM_RANKS; r++) begin : g_rank
        for (genvar b = 0; b < NUM_BANKS; b++) begin : g_bank
            bank_machine_fub #(.ROW_WIDTH(ROW_WIDTH)) u_bank_machine (
                .mc_clk         (mc_clk),
                .mc_rst_n       (mc_rst_n),
                .scheduler_if   (sched_to_bank[r][b]),
                .refresh_if     (refresh_to_bank[r][b]),
                .xbank_if       (xbank_to_bank[r][b]),
                .state_o        (bank_state[r][b]),
                .open_row_o     (bank_open_row[r][b]),
                .last_ref_age_o (bank_last_ref_age[r][b])
            );
        end
    end
endgenerate
```

The `for (genvar r)` outer loop is the per-rank dimension; the inner is the per-bank dimension. The aggregation of `bank_state[r][b]` into the scheduler input is a structural concatenation only — no behavioral aggregation in the top.

## What the Top Does Not Do

- No combinational logic beyond signal renaming or pure concatenation
- No CSR field expansion (the CSR slave handles its own field encoding)
- No clock gating (clock-gate insertion is a synthesis-script concern, not RTL)
- No reset synchronization (handled per-domain in `power_state_fub` and `csr_apb_fub`)
- No `assign` statements except for tying-off optional DFI signals (DDR2 vs LPDDR2 strobe ties)

This intentional poverty of the top file makes it the obvious place for the structural-only synthesis sanity check: "every line in this file is either an instantiation or a port-mapping; if a line is anything else, it is a bug."
