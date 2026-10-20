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

# Cell — Compute Engine IP

**Codename:** cell · **Directory:** `cell/` — the compute-eng-ip family
alongside [`hive-serv`](../hive-serv/).

Cell is the repo's compute engine and the **lowest module** of the
compute tile (owner direction 2026-10-18): the part that actually
computes. Where [hive-serv](../hive-serv/) is the control plane (one
VexRiscv master + sixteen SERV monitors), cell is the data plane — fed,
programmed, and paced entirely in-band on delta.

## Blocks

| Block | Name | What | Status |
|---|---|---|---|
| Compute cell | [`cell`](docs/PRD.md) | One `delta_mesh_cell` node (black box; containment is the whole cell↔delta relationship, owner clarification 2026-10-16) + input memory + ALU/execution FSM + result memory + packetizer + credit logic + config registers + ALU registers (A·B·C·D persistent operands + T, `OP_SRC` operand-source mux, `IP`/`OP` pointers). Delta traffic fills the input memory through the node; the FSM issues invocations to the ALU's elastic valid/ready pipeline; results leave as packets batched X flits toward `FLUSH_DEST`/`FLUSH_TAG` (gatling-programmed; `DEST` reserved for the deferred cell→cell path); each consumed input line returns a credit to its recorded sender. The ALU block is defined by the [alu-infer PRD](../alu-infer/PRD.md) (bf16 on the rtl/math `math_bf16_*` library, fp32 MAC accumulate) — RTL landed in [`rtl/`](rtl/) (func + gate green) | **PRD 0.5 (2026-10-19)** |
| Compute array | `cgra` | Reconfigurable array of richer PEs — the 2026-10-13 ambition, deferred 2026-10-16. The cell's block boundaries are chosen so an array replaces ALU+FSM without disturbing the network, credit, or observation contracts | Deferred |
| Result routing | [`axon`](docs/axon_spec.md) | **Superseded 2026-10-16** by the cell PRD's output path (the result memory + packetizer do the collect/packetize/stream role axon sketched, against the adopted §11 header/credit protocols) | Superseded |

## Architecture

The top-level block plan is **Figure 1** of the
**[cell PRD](docs/PRD.md)** — a house-style graphviz diagram: programming
flows down the center (cfg packets → demux → registers → FSM), operand
fill drops on the left (demux → input memory → FSM → ALU), and results +
credits climb back up the right to the node's local port. The delta node
is the boundary bar; its eight mesh ports pass through to the cell
boundary.

Sixteen cells per tile per the adopted hierarchy
([tile](../tile) TILE_SPEC §11); the tile connects to rapids through
the root nodes and mux. Full dataflow, credit/grant behavior, config
registers, and open questions: **[cell PRD](docs/PRD.md)**.

**Fabric configuration (owner decisions 2026-10-13):** in-band only — delta
routers are programmed through routing tables carried by PKT_CONFIG; no
dedicated configuration wires. Routing is QoS-aware (the HIVE HAS router
register map already provisions `ROUTE_TABLE_n`, `FLOW_CTRL_CFG`, and
`PRIORITY_MASK`; descriptor priority levels cover the traffic side).

**Conventions (standing owner decisions — apply to cell as they do to HIVE):**
delta is the fabric; everything crossing a block boundary is AXI4-Stream;
AXI4-Lite is for registers only; SERV is the repo's tiny agent core; the
verification stack is cocotb + the rds-dv BFMs.

## History

- compute-eng-ip created 2026-09-29 in the component-tree regrouping;
  `hive` retired here 2026-09-27 (unstarted), re-homed to riscv-ip
  2026-10-10, returned 2026-10-13 when cell revived the family.
- 2026-10-16: cell redefined to the ALU cell ([PRD](docs/PRD.md)) on
  owner datapath decisions (node fills input memory; ALU+FSM computes;
  consumed-line credits; X-flit batching; grants on the result path;
  credit batching config N default 1; B4/8/16/32 element widths). CGRA
  deferred; axon superseded; TILE_SPEC §11 adopted the same day.
- 2026-10-17: the ALU's element model corrected to bf16 (2 lanes per
  32-bit line) on the rtl/math `math_bf16_*` library, with fp32 MAC
  accumulation — the B4–B32 integer note is superseded. The ALU block,
  its control interface (one RV32I core per tetrad, in-band
  config/programming, no config origination from the core), and its
  verification doctrine are now governed by the
  [alu-infer PRD](../alu-infer/PRD.md); the cell PRD links to it.
- 2026-10-18: cell PRD 0.3/0.4 — owner direction defines the cell as the
  lowest module: ALU + delta node + config registers + ALU registers
  (A·B·C·D + T as persistent operands, `OP_SRC`, `IP`/`OP`) + data-in /
  data-out memories. Credit returns become sender-generic (per-source
  batching to the recorded source); result-path grants renamed to straps
  (`TILE_LAND_FLITS`). Tetrad engine deferred — gatling the leading
  candidate. House-style Figure 1 replaces the ASCII sketch.
- 2026-10-19: cell PRD 0.5 + MAS 0.12 — gatling sequences the cell ALU
  (`POP`/`PUSH`/`FLUSH` Xcell encodings); `FLUSH_DEST`/`FLUSH_TAG` become
  the operational drain destination and `DEST` is reserved for the
  deferred cell→cell path; local-port width stays at delta `DATA_WIDTH`
  (64b) with beat-chained header; credit-class encoding (sink space = 0)
  added.
