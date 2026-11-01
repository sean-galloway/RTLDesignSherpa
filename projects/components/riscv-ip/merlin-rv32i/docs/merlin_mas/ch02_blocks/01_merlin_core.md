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

# merlin_core (top)

## Top-Level Responsibility

This chapter will describe the `merlin_core` top module: it instantiates the five pipeline stages, the shared functional blocks, the hazard/forwarding unit, and the RVFI aggregation logic.

## Hierarchy

> **Placeholder:** A house-style graphviz hierarchy diagram will be added in a follow-on task.

## Stage Boundaries

This section will introduce the `if_id_t`, `id_ex_t`, `ex_mem_t`, and `mem_wb_t` structs carried across the stage registers.

---

**Last Updated:** 2026-11-01
