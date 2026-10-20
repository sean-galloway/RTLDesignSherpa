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

# Compute Engine IP

Compute systems: the engines that compute and the control planes that
orchestrate them. Family revived 2026-10-13 (created 2026-09-29 in the
component-tree regrouping) when **cell** joined and **hive-serv** returned
from its 2026-10-10..2026-10-13 stay in riscv-ip — HIVE uses RISC-V cores but
is a *system*, not a core, and it is the control half of this family.

| Directory | What | Status |
|---|---|---|
| [`hive-serv/`](hive-serv/) | Hierarchical control/monitoring system: 1 VexRiscv master (HIVE-C) + 16 SERV per-tile monitors; inband descriptor injection into delta; coordinates RAPIDS and cell | HAS/MAS v0.2; Phase 1 RTL in progress (vault hive-serv TASK-000) |
| [`cell/`](cell/) | The tile's compute unit — the lowest module (owner direction 2026-10-18): alu-infer bf16 ALU (elastic valid/ready pipeline) + one `delta_mesh_cell` node + config registers + ALU registers (A·B·C·D persistent operands + T, `OP_SRC` mux, `IP`/`OP` pointers) + data-in / data-out memories; sender-generic credit returns, `DEST` result routing (default: recorded source). ALU RTL landed in [`alu-infer/rtl/`](alu-infer/rtl/) (func + gate green); balance planned | [PRD](cell/docs/PRD.md) 0.3 (2026-10-18) |
| [`tile/`](tile/) | Compute-engine tile: 16 cells as 2×2×1 tetrads (K4 at both scales) + per-level MonBus aggregation + rapids attach; **delta is the node**, instantiated 16×; tetrad control core deferred pending the cell (gatling-rv32itetrad leading) | [Tile Spec](tile/docs/TILE_SPEC.md) v1.5 (2026-10-18) |
| [`alu-infer/`](alu-infer/) | Cell compute ALU: bf16 inference datapath (2×bf16 lanes per line) built mostly on the [rtl/math](../../../rtl/math/) `math_bf16_*` library — fp32 MAC accumulate; valid/ready elastic pipeline (II=1 while draining; **tag-based alignment** ruled 2026-10-18, as-built since 2026-10-19 — 8-bit tag per loaded invocation, FIFO-tracked, an op's valid gated on its whole tag group); per-tetrad RV32I control core (**deferred 2026-10-18** — gatling-rv32itetrad leading candidate, kestrel-class a `CORE_FLAVOR` option; in-band config/programming; not SERV — Ocelus agent). RTL + unit tests live here (`alu-infer/rtl/`, `alu-infer/dv/tests/`, moved from `cell/` 2026-10-20); the cell integrates the block | [PRD](alu-infer/PRD.md) 0.50 · [MAS](alu-infer/docs/alu_infer_mas/alu_infer_mas_index.md) 0.50 (2026-10-18; revs pinned at 0.50 per owner, "for now," while the ALU heads to the board) |
| [`alu-rv32i/`](alu-rv32i/) | Falcon-suite RV32I integer ALU definition — ten operations, eq/lt/ltu flags, the flags ruling; realized per-rung in [riscv-ip](../riscv-ip/) (kestrel_alu is the v1 reference); no RTL here | [PRD](alu-rv32i/PRD.md) 0.1 (2026-10-17) |
| [`alu-rv32f/`](alu-rv32f/) | Falcon-suite RV32F FP32 execution-unit definition — full F-extension set on the [rtl/math](../../../rtl/math/) fp32 library, fcsr flag contract, long-latency divide/sqrt lesson; realized by the garuda rung; no RTL here | [PRD](alu-rv32f/PRD.md) 0.1 (2026-10-17) |

The trio forms the compute system: **cell** is the data plane (the CGRA),
**hive-serv** is the control plane, **tile** is the subsystem that assembles
cells onto delta nodes at scale, and **delta** is the fabric between them —
nodes collectively form the network, tile is the IP that instantiates one
network segment. **RAPIDS** moves bulk data. See the [hive-serv HAS](hive-serv/docs/hive_has/hive_has_index.md),
the [cell README](cell/README.md), and the [tile spec](tile/docs/TILE_SPEC.md).

The three `alu-*` directories are the family's ALU building-block
**definitions**: the contracts the engines (and the falcon ladder) realize —
alu-infer inside cell, alu-rv32i/alu-rv32f per-rung in
[riscv-ip](../riscv-ip/). Each holds a PRD and a pointer README, not RTL.
**Queue (owner 2026-10-18):** cell first, then gatling; the alu-rv32i /
alu-rv32f realizations (drop-in for the RV cores' ALU slots) wait behind
both.
