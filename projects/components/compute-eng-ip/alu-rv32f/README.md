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

# alu-rv32f — Falcon-Suite FP32 Execution Unit (definition)

The RV32F single-precision execution-unit product definition for the falcon
ladder: the full F-extension set on the repo's `math_ieee754_2008_fp32_*`
library, with the fcsr flag contract and the long-latency divide/square-root
lesson pinned for the garuda rung to realize.

This directory holds the **definition only** — no RTL here. The realization
is the garuda rung's FPU in `riscv-ip/garuda-rv32imaf/`.

- **PRD:** [PRD.md](PRD.md)
- **Realization home:** [`riscv-ip/garuda-rv32imaf/`](../../riscv-ip/garuda-rv32imaf/)
  (planned; see the garuda row of the [riscv-ip README](../../riscv-ip/README.md))
- **Arithmetic library:** [`rtl/math/`](../../../../rtl/math/) fp32 blocks
- **Back to family:** [compute-eng-ip README](../README.md)
