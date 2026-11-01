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

# Purpose and Scope

## What This Document Is

This chapter will introduce the merlin-rv32i core, state the design intent (a 5-stage pipelined RV32I implementation sharing the common-rv32i functional blocks with kestrel), and define the scope of the HAS: external behavior, port contracts, memory timing, halt semantics, and integration guidance.

## What This Document Is Not

The HAS will not describe internal pipeline timing, forwarding muxes, or the hazard unit; those live in the companion MAS.

## Scope Boundaries

This section will enumerate what is in scope (RV32I base integer ISA, registered-read memory contract, halt/trap reporting via RVFI) and what is deliberately out of scope (prediction, CSRs beyond the stub, M/A/F/D extensions, caches, MonBus).

---

**Last Updated:** 2026-11-01
