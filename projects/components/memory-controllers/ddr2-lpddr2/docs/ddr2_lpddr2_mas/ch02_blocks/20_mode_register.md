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

# Mode Register (`mode_register`)

**Module:** `mode_register.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `command_scheduler_macro`
**Status:** v1 implemented (DDR2 decode; LPDDR2 TODO)

## Purpose

Per-rank Mode Register shadow + live decode of MR-derived timing values
for use by the rest of the controller.

On `mr_we_i`, write `mr_data_i` into shadow MR[`mr_index_i`] for
`mr_rank_i`. `init_sequencer` drives this during DRAM bring-up; a
CSR/APB hot-update path will drive it later.

## Live Decoded Outputs

| Output     | Source (DDR2)    | Source (LPDDR2 — planned) |
|------------|------------------|--------------------------|
| `cl_o`     | MR0[6:4]         | MR2[3:0]                 |
| `cwl_o`    | CL − 1           | MR2[7:4]                 |
| `bl_o`     | MR0[2:0]         | MR1 (4/8/16)             |
| `al_o`     | MR1[5:3]         | (0; not used)            |
| `drv_o`    | MR1 drive bits   | (informational)          |
| `odt_o`    | MR1[6,2]         | (0)                      |

All outputs are strict-flop registered. Consumed by:

- `scheduler` — uses `cl_o`, `cwl_o`, `al_o` to time RD/WR latencies.
- `wr_beat_sequencer` — uses `cwl_o` for the WR-to-wrdata window.
- `rd_cl_aligner` — uses `cl_o` + PHY `t_rddata_en` for RD-to-rddata.
- `dfi_cmd_formatter` — uses `bl_o` to size column commands.

## Scope (v1)

- `NUM_MRS=4` fits DDR2 (MR0/MR1/MR2/MR3). LPDDR2 needs up to MR17;
  bumping `MAX_MR_IDX` lands when LPDDR2 init is wired up.
- `mr_req_o` is tied 0 — no hot MR updates issued via the scheduler in
  v1. Init does the MR loads directly through this FUB's CSR write port.

## Tests

Verified by `dv/tests/fub/test_mode_register.py` (6 scenarios):
`smoke_ddr2`, `ddr2_cl_sweep`, `reset_values`, `ddr2_bl_sweep`,
`ddr2_al_sweep`, `multi_rank`.
