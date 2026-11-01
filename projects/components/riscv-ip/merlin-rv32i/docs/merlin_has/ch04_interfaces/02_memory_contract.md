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

# Memory Contract

## Registered-Read Instruction Memory

This section will explain that `imem_addr` is presented in cycle N and the instruction is captured one cycle later in IF/ID.

## Registered-Read Data Memory

This section will explain that `dmem_addr` is presented in the MEM stage and the load data is assembled in WB from the registered `dmem_rdata` port.

## `mem_wait` Global Hold

This section will describe the `mem_wait` input: all pipeline registers stall, `dmem_req` deasserts, and no instruction retires while memories are not ready.

## Byte-Wise Store Behavior

This section will document the rotated `dmem_wdata` and `dmem_wstrb` outputs and the expectation that the memory subsystem merges bytes.

---

**Last Updated:** 2026-11-01
