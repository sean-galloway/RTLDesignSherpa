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

# System Overview and Context

## Place in the Falcon Suite

This chapter will describe merlin as the rung-2 pipelined core in the RISC-V Falcon suite, positioned between the single-cycle kestrel and future superscalar or out-of-order designs.

## High-Level Block Diagram

> **Placeholder:** A house-style graphviz block diagram will be added in a follow-on task. It will show the IF/ID/EX/MEM/WB stages, the memory ports, and the RVFI retire channel.

## Pipeline at a Glance

This section will summarize the five stages, the registered-read memory contract, and the key micro-architectural features (forwarding, load-use interlock, branch flush).

---

**Last Updated:** 2026-11-01
