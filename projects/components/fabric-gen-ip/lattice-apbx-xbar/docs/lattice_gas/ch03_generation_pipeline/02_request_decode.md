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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Request Decode

Each master presents a cmd/rsp command after the master-side `apb4_slave`/`apb5_slave` has accepted the APB transaction. The generator decodes the command's `cmd_paddr` to determine which slave (if any) should service it.

## Offset-based slave selection

The slave index is computed from the offset (`PADDR - BASE_ADDR`), not from raw `PADDR` bits:

```systemverilog
m0_cmd_offset    = m0_cmd_paddr - BASE_ADDR;
m0_addr_in_range = (m0_cmd_paddr >= BASE_ADDR) &&
                   (m0_cmd_paddr < (BASE_ADDR + 32'h00040000));
m0_slave_sel     = m0_cmd_offset[17:16];
```

Using the offset prevents the address map from rotating when `BASE_ADDR` is not aligned to the total span. The subtraction folds to constants at elaboration because `BASE_ADDR` is a parameter, so it costs no logic.

## Decode-miss handling

If a command falls outside the mapped range, the crossbar must complete the transaction with `PSLVERR` rather than holding `PREADY` low forever. The generator emits a per-master `r_m<N>_decerr_pending` flop:

- When `cmd_valid && cmd_ready && !addr_in_range`, the pending flag is set.
- The master-side `cmd_ready` is asserted only while the pending flag is clear.
- A locally generated response (`rsp_valid = 1`, `rsp_pslverr = 1`) is returned on the next cycle and cleared when `rsp_ready` is asserted.

This guarantees that an unmapped access completes as a recoverable error instead of wedging the external master.

## Single-master simplification

When `num_masters == 1`, no arbitration is needed. The request decode still creates the per-slave `cmd_valid` signals directly from the slave-select result, and the decode-miss logic remains.
