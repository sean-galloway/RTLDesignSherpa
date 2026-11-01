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

# Hazard Detection and Operand Forwarding

## Forwarding Paths

This chapter will describe the EX/MEM-to-EX and MEM/WB-to-EX forwarding paths, the EX/MEM priority rule, and the WB-to-ID bypass for an instruction entering ID while its producer is in WB.

## Hazard Unit

This section will explain the inputs and outputs of `merlin_hazard`, including how it detects load-use stalls and drives the flush signals.

## Waveform 4.1: Back-to-Back Dependent ALU Operations

> **Placeholder:** A GTKWave screenshot or Wavedrom figure will be added in a follow-on task. The waveform will be captured from `projects/components/riscv-ip/merlin-rv32i/dv/tests/GTKW/merlin_tb_top/merlin_tb_top.gtkw` and will show `ex_fwd_a`/`ex_fwd_b` selecting `FWD_EXMEM` or `FWD_MEMWB` as dependent ALU instructions move through the pipeline.

---

**Last Updated:** 2026-11-01
