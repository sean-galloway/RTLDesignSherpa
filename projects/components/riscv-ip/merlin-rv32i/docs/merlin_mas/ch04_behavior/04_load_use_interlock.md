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

# Load-Use Interlock

## Detection

This chapter will explain how the hazard unit detects a load-use hazard: the producer is in EX/MEM as a load (`idex_is_load`) and its destination matches a source register in ID/EX.

## Stall and Bubble Injection

This section will describe how `stall_ifid` holds the PC and IF/ID, while `id_ex_flush_eff` injects a bubble into ID/EX so the consumer is retried after the load writes back.

## Waveform 4.3: Load-Use Bubble

> **Placeholder:** A GTKWave screenshot or Wavedrom figure will be added in a follow-on task. The waveform will be captured from `projects/components/riscv-ip/merlin-rv32i/dv/tests/GTKW/merlin_tb_top/merlin_tb_top.gtkw` and will show `stall_ifid`, the one-cycle bubble, and the consumer finally seeing the load data via forwarding from MEM/WB.

---

**Last Updated:** 2026-11-01
