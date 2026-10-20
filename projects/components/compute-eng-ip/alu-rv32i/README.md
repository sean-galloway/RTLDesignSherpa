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

# alu-rv32i — Falcon-Suite Integer ALU (definition)

The RV32I integer ALU product definition for the falcon ladder: ten
operations, eq/lt/ltu flags, and the flags ruling, pinned once so every rung
teaches the same contract while its microarchitecture diverges.

This directory holds the **definition only** — no RTL here. Each rung
realizes the contract in its own RTL (kestrel_alu is the v1 reference).

- **PRD:** [PRD.md](PRD.md)
- **Realization home:** [`riscv-ip/kestrel-rv32i/`](../../riscv-ip/kestrel-rv32i/)
  (v1 reference; later rungs re-implement per the ladder)
- **Back to family:** [compute-eng-ip README](../README.md)
