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

# The Pipelined Cycle, Step by Step

## The Five Stages

This chapter will walk through one clock cycle of the pipeline: IF (PC + fetch), ID (decode + register read), EX (ALU + branch), MEM (data memory request), WB (writeback + RVFI retire).

## Pipeline Register Update

This section will explain the stall/flush semantics shared by the four stage registers and how `valid` bubbles propagate.

## Waveform Reference

This section will reference the `merlin_tb_top.gtkw` save file for observing the pipeline stages.

---

**Last Updated:** 2026-11-01
