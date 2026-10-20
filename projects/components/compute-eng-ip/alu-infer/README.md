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

# alu-infer — Cell Inference ALU (definition)

The cell's compute ALU: a bf16 inference datapath — two bf16 lanes per
32-bit line — built mostly on the repo's `math_bf16_*` library (adder,
multiplier, fused FMA-mac, comparator, min/max, ReLU, and the activation
growth set), driven by the cell's execution FSM.

This directory holds the **product definition only**; the RTL implementation
is built and verified inside the cell component (owner decision 2026-10-17).

- **PRD:** [PRD.md](PRD.md)
- **MAS:** [Micro-Architecture Specification](docs/alu_infer_mas/alu_infer_mas_index.md)
  ([PDF](docs/ALUINFER_MAS_v0.50.pdf)) — module tree, function rows, fp32
  MAC accumulator, ALU↔FSM interface, cycle behavior, verification hooks
- **Implementation home:** [`cell/`](../cell/README.md) — the "ALU + execution
  FSM" block; the normative datapath context is [cell PRD §4](../cell/docs/PRD.md).
  The v1 RTL landed in `cell/rtl/` on 2026-10-17/18 (func+gate green):
  `alu_infer_top.sv`, `alu_infer_rows.sv`, `alu_infer_pipe.sv`,
  `alu_infer_acc.sv`.
- **Arithmetic library:** [`rtl/math/`](../../../../rtl/math/) `math_bf16_*`
  family
- **Back to family:** [compute-eng-ip README](../README.md)
