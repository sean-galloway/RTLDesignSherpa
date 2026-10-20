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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# References

## Normative Specifications

- **cell PRD** —
  [`projects/components/compute-eng-ip/cell/docs/PRD.md`](../../PRD.md).\
  The governing product definition. The MAS implements PRD §12 open
  questions and cites §§3, 6, 7 throughout.

- **TILE_SPEC §11** —
  [`projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md`](../../../../tile/docs/TILE_SPEC.md).\
  Defines the packet header (§11.5), transport binding (§11.6), payload
  types (§11.2), destination coordinate (§11.3), end-to-end credits and
  straps (§§11.9–11.10), and result flush (§11.14).

- **alu-infer PRD §3** —
  [`projects/components/compute-eng-ip/alu-infer/PRD.md`](../../../../alu-infer/PRD.md).\
  Normative ALU function set, element model (bf16), and MAC
  accumulation semantics.

- **alu-infer MAS** —
  [`projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas/alu_infer_mas_index.md`](../../../../alu-infer/docs/alu_infer_mas/alu_infer_mas_index.md).\
  Implementation-intent book for the ALU block: module tree, function
  rows, accumulator, ALU↔FSM interface, and cycle behavior.

## RTL Sources

- **cell_top.sv** —
  [`projects/components/compute-eng-ip/cell/rtl/cell_top.sv`](../../../rtl/cell_top.sv).\
  Slice-1 top-level: delta node, rx demux, registers, memories.

- **cell_rx.sv** —
  [`projects/components/compute-eng-ip/cell/rtl/cell_rx.sv`](../../../rtl/cell_rx.sv).\
  Slice-1 header parse/demux with provisional 64-bit TUSER packing.

- **cell_cfg_regs.sv** —
  [`projects/components/compute-eng-ip/cell/rtl/cell_cfg_regs.sv`](../../../rtl/cell_cfg_regs.sv).\
  Slice-1 AXIL + cfg-stream register file.

- **cell_mem_in.sv** —
  [`projects/components/compute-eng-ip/cell/rtl/cell_mem_in.sv`](../../../rtl/cell_mem_in.sv).\
  Slice-1 input memory with per-line source tag.

- **cell_mem_out.sv** —
  [`projects/components/compute-eng-ip/cell/rtl/cell_mem_out.sv`](../../../rtl/cell_mem_out.sv).\
  Slice-1 result memory.

- **cell_pkg.sv** —
  [`projects/components/compute-eng-ip/cell/rtl/cell_pkg.sv`](../../../rtl/cell_pkg.sv).\
  Shared types, coordinate layout, register offsets, and slice-1
  compact header offsets.

- **delta_mesh_cell.sv** —
  [`projects/components/fabric-gen-ip/delta/rtl/delta_mesh_cell.sv`](../../../../../fabric-gen-ip/delta/rtl/delta_mesh_cell.sv).\
  The node the cell instantiates; defines the 9-port unpacked-array
  interface and `P_LOCAL = 8`.

## Verification

- **test_cell.py** —
  [`projects/components/compute-eng-ip/cell/dv/tests/test_cell.py`](../../../dv/tests/test_cell.py).\
  Existing slice-1 cocotb test suite; the base for the slice-2/3
  credit-loop and ALU-run tests.

## House Style and Build

- **Block diagrams handbook** —
  [`vault/handbook/authoring/block-diagrams.md`](../../../../../../../vault/handbook/authoring/block-diagrams.md).\
  Binding house style for the whole-cell and credit-loop figures.

- **alu-infer MAS PDF generator** —
  [`projects/components/compute-eng-ip/alu-infer/docs/generate_mas_pdf.sh`](../../../../alu-infer/docs/generate_mas_pdf.sh).\
  The build script this MAS generator is modeled on.

---

**Last Updated:** 2026-10-18
