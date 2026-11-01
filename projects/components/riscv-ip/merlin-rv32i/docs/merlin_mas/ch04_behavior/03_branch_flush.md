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

# Branch Resolution and Flush

## Branch Comparator

This chapter will describe the dedicated branch comparator on forwarded operands and how `funct3` selects the condition.

## Target Computation

This section will explain JAL, JALR, and branch target computation in EX and the `ex_target`/`ex_next_pc` signals.

## Flush Timing

This section will explain the two-cycle bubble after a taken branch or jump: the IF/ID and ID/EX instructions younger than the resolved branch are flushed.

## Waveform 4.2: Taken Branch Flush

> **Placeholder:** A GTKWave screenshot or Wavedrom figure will be added in a follow-on task. The waveform will be captured from `projects/components/riscv-ip/merlin-rv32i/dv/tests/GTKW/merlin_tb_top/merlin_tb_top.gtkw` and will show `ex_flush`, `if_id_flush_eff`, `id_ex_flush_eff`, and the PC redirect to `ex_target`.

---

**Last Updated:** 2026-11-01
