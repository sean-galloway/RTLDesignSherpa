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

# merlin_core Port Specification

## Port List

This section will present the `merlin_core` port list with direction, width, and functional description for each signal.

## Clock, Reset, and Power-Up

This section will describe the clock, active-low reset, and the `RESET_ADDR` parameter.

## Instruction Memory Port

This section will document `imem_addr`, `imem_addr_next`, and `imem_rdata`.

## Data Memory Port

This section will document `dmem_req`, `dmem_addr`, `dmem_wdata`, `dmem_wstrb`, and `dmem_rdata`.

## Halt and RVFI Ports

This section will document `halt`, `halt_cause`, and the RVFI retire-channel signals.

---

**Last Updated:** 2026-11-01
