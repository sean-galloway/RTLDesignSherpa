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

# RVFI Aggregation

## Retire Point

This chapter will describe how RVFI records are aggregated at the WB stage, one beat per retired instruction.

## Field Construction

This section will explain how `rvfi_valid`, `rvfi_pc_rdata`, `rvfi_pc_wdata`, register fields, and memory fields are derived from the `mem_wb_q` struct.

## Trap Beat

This section will explain that the halting instruction retires with `rvfi_trap=1` and that no further beats are emitted after halt.

---

**Last Updated:** 2026-11-01
