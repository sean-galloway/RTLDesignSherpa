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

# Verification Hooks and Observability

## GTKW Save File

This section will document the `merlin_tb_top.gtkw` save file at `projects/components/riscv-ip/merlin-rv32i/dv/tests/GTKW/merlin_tb_top/merlin_tb_top.gtkw` and the signal groups it provides.

## Test Suites

This section will summarize the DV suites: focus tests, OP/OP-IMM sweep, load/store and mem_wait pulse tests, directed hazard suite (forwarding matrix, load-use matrix, branch-flush cases), rv32ui battery, spike lockstep, and fuzz tests.

## Formal Checks

This section will summarize the riscv-formal retire-interface checks adapted for the pipelined WB interface.

---

**Last Updated:** 2026-11-01
