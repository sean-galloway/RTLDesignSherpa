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
growth set), issued by the tetrad's gatling core. bf16, int8, fp32 and fp8
e4m3 element formats; reduce, PWL LUT activation, const, library
activations and conversions alongside the v1 rows.

This directory holds the **product definition and the RTL**; the ALU is
integrated and verified at system level inside the cell component (owner
decision 2026-10-17; RTL moved here from `cell/rtl/` on 2026-10-20).

- **PRD:** [PRD.md](PRD.md)
- **MAS:** [Micro-Architecture Specification](docs/alu_infer_mas/alu_infer_mas_index.md)
  ([PDF](docs/ALUINFER_MAS_v0.50.pdf)) — module tree, function rows, fp32
  accumulator rows, PWL LUT, conversions, the issue seam, cycle behavior,
  verification hooks
- **RTL:** [`rtl/`](rtl/) — `alu_infer_top.sv` and its module tree (decode,
  per-format row families, activations, PWL LUT, conversions, accumulator,
  tag FIFO; package in `rtl/includes/`), with per-block filelists under
  `rtl/filelists/`, an `alu-infer_all.f` lint master and a four-line area
  Makefile
- **PWL table builder:** [`bin/alu_infer_pwl.py`](bin/alu_infer_pwl.py) —
  fits the 256-entry LUT for sigmoid/tanh/gelu/silu/exp and models the row
- **Unit tests:** [`dv/tests/`](dv/tests/) — `test_alu_infer.py`, run via
  `make -C dv/tests run-all-<gate|func|full>` after `make clean-all`
- **Issuer:** [`gatling-rv32i`](../../riscv-ip/gatling-rv32i/PRD.md)
  — the tetrad barrel core whose programs issue the ALU
- **Integration home:** [`cell/`](../cell/README.md); the cell filelists
  include this block's filelist.
- **Arithmetic library:** [`rtl/math/`](../../../../rtl/math/) — the
  `math_bf16_*`, IEEE fp32, `math_fp8_e4m3_*` and converter blocks
- **Back to family:** [compute-eng-ip README](../README.md)
