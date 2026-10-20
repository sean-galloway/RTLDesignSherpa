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

# Module Tree

## Purpose

`cell_top` is the compute cell top-level. It instantiates one
`delta_mesh_cell` node and the cell's own datapath blocks. The module
tree below shows the slice-1 blocks that are built and the slice-2/3
blocks that this MAS specifies.

## Module Tree

```text
cell_top (built, slice 1)
├── delta_mesh_cell (black box — fabric-gen-ip/delta)
├── cell_rx (built, slice 1) — header parse / demux from the node's local port
├── cell_cfg_regs (built, slice 1) — AXIL slave + in-band cfg-stream register file
├── cell_mem_in (built, slice 1) — input operand memory with per-line source tag
├── cell_mem_out (built, slice 1) — result memory
├── cell_credit (specified, slice 2) — per-source owed counters + credit packet builder
├── cell_packetizer (specified, slice 2) — result-flit batching + §11.5 header builder
└── cell_exec_fsm (specified, slice 3) — pop → issue → push loop + ALU hookup
```

The ALU block itself (`alu-infer`) is instantiated inside
`cell_exec_fsm` (or as a sibling driven by it); its specification is
owned by the alu-infer PRD and MAS.

## Block Intent (one paragraph each)

### `delta_mesh_cell`

The network attachment. The cell instantiates one node; its local port
(`P_LOCAL = 8`) delivers traffic to `cell_rx`, and its eight mesh ports
pass through to the cell boundary. The node is a black box owned by
`fabric-gen-ip/delta`; its HAS/MAS govern it. The cell depends only on
the node's local-port AXI4-Stream contract and on the node's ability to
route packets by destination coordinate.

### `cell_rx`

Header parse and demux for the node's local port. Slice 1 already
parses a provisional 64-bit TUSER packing (because the instantiated
delta node exposes a 64-bit TUSER) and routes `mem` payloads to the
input memory, `cfg` writes to the register file, and `credit` packets to
a counted TODO drop. Slice 2/3 reworks `cell_rx` to the §11.6 transport:
delta's route header rides `TUSER`, and the 128-bit tile header is the
first data beat. Every input-memory line is tagged with the packet's
source coordinate so credit returns can be addressed correctly.

### `cell_cfg_regs`

AXI4-Lite slave plus in-band `cfg`-stream register file per PRD §7. The
register map is defined in Chapter 6. The block exposes register values
to the execution FSM and packetizer, generates the one-cycle
`soft_rst` pulse, and assembles `STATUS` and `IRQ_STATUS`.

### `cell_mem_in`

Input operand memory. Sized to `IN_DEPTH` lines; each line carries a
source-coordinate tag. It has one write port (from `cell_rx`) and one
read port (from `cell_exec_fsm`). The read pointer `IP` is owned by the
FSM; occupancy is exposed for `STATUS`.

### `cell_mem_out`

Result memory. Sized to `OUT_DEPTH` lines; one write port (from
`cell_exec_fsm`) and one read port (from `cell_packetizer`). The write
pointer `OP` is owned by the FSM; occupancy is exposed for `STATUS`.

### `cell_credit`

Credit-return logic. Maintains per-source owed counters keyed by the
source coordinate recorded on each consumed input line. Batches returns
to `N = CREDIT_BATCH_N` consumed lines per source; drains a partial
batch after a 64-cycle timeout. Builds header-only `credit`/`add`
packets addressed to the recorded source and sends them back through the
node on the credit VC. Sends the boot `credit`/`set` advertisement to
`level` 3 carrying the input memory's size in flits.

### `cell_packetizer`

Result drain and packetizer. Batches result flits up to
`EMIT_BATCH_X`; flushes on batch-full or on `CTRL.flush-and-send`.
Builds the §11.5 tile header with destination and tag supplied by the
gatling-programmed drain command, and sends the packet through the node
only while the `TILE_LAND_FLITS` strap counter covers the whole packet.
Spends the strap counter per flit sent (header included) and restores it
as RAPIDS returns `credit`/`add` packets.

### `cell_exec_fsm`

Execution FSM and ALU hookup. Runs the pop→issue→push loop: pops
`OP_LINES` input lines per invocation (advancing `IP`), presents them to
the ALU's valid/ready elastic pipeline, and pushes each retired result
line into the result memory (advancing `OP`). Selects operand sources
per `OP_SRC` (input-memory pop or one of `A`/`B`/`C`/`D`; `T` backs the
threshold immediate). Clears `IP`/`OP` on `CTRL.soft_reset`.

## Parameters

| Parameter | Default | Meaning |
|---|---|---|
| `LINE_W` | 32 | Line width in bits; one line is two bf16 lanes |
| `COORD_W` | 4 | Coordinate sub-field width; coordinate is `{ext, level, X, Y, Z}` |
| `POS_X/Y/Z` | 0 | This cell's position in the tile grid |
| `IN_DEPTH` | 32 | Input memory depth in lines |
| `OUT_DEPTH` | 32 | Result memory depth in lines |
| `AXIL_ADDR_WIDTH` | 32 | AXIL address width |
| `AXIL_DATA_WIDTH` | 32 | AXIL data width |
| `DATA_WIDTH` | 64 | Cell↔delta local-port data width. Stays at the delta node's `DATA_WIDTH` (64 today); the 128-bit §11.6 tile header is beat-chained LSB-first across `ceil(128/DATA_WIDTH)` beats. No local-port widening. |
| `USER_WIDTH` | 64 | Delta route header width; unchanged until delta widens it |
| `NUM_VC` | 2 | Number of delta virtual channels |

: Table 2.1: `cell_top` parameters

## Clock and Reset

Single clock domain, active-low async `aresetn` (house
`ALWAYS_FF_RST`), matching the tile's single-clock-domain decision
(TILE_SPEC §9). Reset clears the memories, registers, pointers, and
credit/strap state; `CTRL.soft_reset` clears only `IP`, `OP`,
`IRQ_STATUS`, and selected datapath state.

---

**Last Updated:** 2026-10-19
