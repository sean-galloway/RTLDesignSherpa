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

# Design Philosophy and Machine Organization

## From kestrel to merlin

This chapter will explain the design migration from the single-cycle kestrel core to the 5-stage pipelined merlin core, preserving the ISA package and functional blocks while adding pipeline registers, forwarding, and hazard logic.

## Pipeline Organization

> **Placeholder:** A house-style graphviz pipeline diagram will be added in a follow-on task. It will show the IF/ID/EX/MEM/WB stages, the register file, the hazard unit, and the forwarding paths.

## Design Decisions

This section will summarize the key decisions: EX/MEM-priority forwarding, load-use interlock in ID, branch resolved in EX with a two-cycle flush, CSR stub forcing zero writeback, and halt latched in WB.

---

**Last Updated:** 2026-11-01
