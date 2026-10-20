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

# External and Internal Interfaces

## Cell Boundary

### Mesh-Facing Ports

`cell_top` exposes the eight mesh-facing ports of the instantiated
`delta_mesh_cell` node:

| Port | Direction | Width | Purpose |
|---|---|---|---|
| `s_axis_tdata[8]` | in | `DATA_WIDTH` | Data from mesh neighbors |
| `s_axis_tvalid[8]` | in | 1 | Valid from mesh neighbors |
| `s_axis_tready[8]` | out | 1 | Ready to mesh neighbors |
| `s_axis_tlast[8]` | in | 1 | Packet last from mesh neighbors |
| `s_axis_tuser[8]` | in | `USER_WIDTH` | Delta route header from mesh neighbors |
| `m_axis_tdata[8]` | out | `DATA_WIDTH` | Data to mesh neighbors |
| `m_axis_tvalid[8]` | out | 1 | Valid to mesh neighbors |
| `m_axis_tready[8]` | in | 1 | Ready from mesh neighbors |
| `m_axis_tlast[8]` | out | 1 | Packet last to mesh neighbors |
| `m_axis_tuser[8]` | out | `USER_WIDTH` | Delta route header to mesh neighbors |
| `s_credit[8]` | in | `NUM_VC` | Per-VC credit levels from neighbors |
| `m_credit[8]` | out | `NUM_VC` | Per-VC credit levels to neighbors |

: Table 3.1: Mesh-facing AXI4-Stream ports

These ports are pass-through wiring in `cell_top`; the node performs all
routing. Cell-bound traffic must be addressed to the cell's external ID
`{ext=1, level=0, X, Y, Z}` and ride delta QoS ≠ 0 so the node does not
consume it as its own config traffic (TILE_SPEC §11.2).

### Local Port Contract

The cell's internal datapath sees only the node's local port
(`P_LOCAL = 8`). Slice 1 used a provisional 64-bit TUSER packing for the
tile header because the instantiated delta node exposes 64-bit `TUSER`.

**MAS decision:** Slice 2/3 moves to the `TILE_SPEC` §11.6 transport
binding, with the beat-chained header rule (owner ruling 2026-10-18):
every link keeps its own data width, and the 128-bit tile header occupies
the first `ceil(128/DW)` payload beats, LSB-first.

- The **delta route header** rides `TUSER` of the head beat, as delta
  owns it.
- The **128-bit tile header** is payload: on the 64-bit local port it
  spans beats 0–1 (`tdata[63:0]` = header `[63:0]`, next beat's
  `tdata[63:0]` = header `[127:64]`), then payload beats follow. On a
  128-bit-or-wider link it is beat 0 alone.
- The cell's local-port data width **stays at the delta node's
  `DATA_WIDTH` (64 bits today)** — no widening, no width conversion
  anywhere. The demux reassembles the two header beats; the packetizer
  emits the header across two beats.

This supersedes slice-1's provisional 64-bit TUSER packing and the
earlier MAS 0.10 draft's 128-bit local-port widening.

### AXI4-Lite Register Interface

The cell exposes a house-standard AXI4-Lite slave for debug and local
control. All registers are also writable from the in-band `cfg` stream.
The register map is in Chapter 6.

### Observability

| Signal | Width | Purpose |
|---|---|---|
| `o_err_drop_cnt` | 32 | Dropped-head count from the delta node |
| `o_todo_credit_drop_cnt` | 32 | Slice-1 TODO counter for unhandled credit packets |
| `o_todo_cfg_read_drop_cnt` | 32 | Slice-1 TODO counter for unhandled cfg read replies |
| `o_irq` | 1 | Interrupt output (level) |
| MonBus (AXI4-Lite) | - | The cell's one MonBus stream, merged at the tetrad with the other three cells and the tetrad node (tile spec §5). Not yet in the RTL |

: Table 3.2: Observability outputs

## Internal Interfaces

### `cell_rx` → `cell_mem_in`

| Signal | Width | Direction | Purpose |
|---|---|---|---|
| `mem_wr_valid` | 1 | rx → mem | Write valid |
| `mem_wr_ready` | 1 | mem → rx | Write ready |
| `mem_wr_addr` | `log2(IN_DEPTH)` | rx → mem | Line index |
| `mem_wr_data` | `LINE_W` | rx → mem | Line data |
| `mem_wr_src_coord` | `COORD_BITS` | rx → mem | Source coordinate tag |

: Table 3.3: Input-memory write port

### `cell_rx` → `cell_cfg_regs`

| Signal | Width | Direction | Purpose |
|---|---|---|---|
| `cfg_wr_valid` | 1 | rx → regs | In-band cfg write valid |
| `cfg_wr_ready` | 1 | regs → rx | In-band cfg write ready |
| `cfg_wr_addr` | 8 | rx → regs | Register offset |
| `cfg_wr_data` | 32 | rx → regs | Register value |
| `cfg_rd_valid` | 1 | rx → regs | In-band cfg read request valid (slice-2 completion) |
| `cfg_rd_addr` | 8 | rx → regs | Register offset |
| `cfg_rd_data` | 32 | regs → rx | Read data (slice-2 completion) |
| `cfg_rd_ready` | 1 | rx → regs | Read request accepted (slice-2 completion) |

: Table 3.4: Config-stream register interface

### `cell_cfg_regs` → datapath

The register block drives the following register values:

| Signal | Width | Purpose |
|---|---|---|
| `r_ctrl` | 32 | `CTRL` register |
| `r_func_sel` | 32 | `FUNC_SEL` register |
| `r_op_lines` | 32 | `OP_LINES` register |
| `r_emit_batch_x` | 32 | `EMIT_BATCH_X` register |
| `r_credit_batch_n` | 32 | `CREDIT_BATCH_N` register |
| `r_irq_en` / `r_irq_status` | 32 | IRQ enables and status |
| `r_a` / `r_b` / `r_c` / `r_d` / `r_t` | 32 | Persistent ALU operands and threshold |
| `r_op_src` | 32 | Operand-source mux selection |
| `r_dest` | 32 | Deferred cell-destined destination |
| `r_ip` / `r_op` | 32 | Input/result memory pointers |
| `o_soft_rst` | 1 | One-cycle soft-reset pulse |

: Table 3.5: Register outputs to datapath

### `cell_mem_in` → `cell_exec_fsm`

| Signal | Width | Direction | Purpose |
|---|---|---|---|
| `mem_in_rd_valid` | 1 | fsm → mem | Read request valid |
| `mem_in_rd_ready` | 1 | mem → fsm | Read request ready |
| `mem_in_rd_addr` | `log2(IN_DEPTH)` | fsm → mem | Read address |
| `mem_in_rd_data` | `LINE_W` | mem → fsm | Read data (registered) |
| `mem_in_rd_src_coord` | `COORD_BITS` | mem → fsm | Source tag of read line |
| `mem_in_empty` | 1 | mem → fsm/reg | Memory empty |
| `mem_in_full` | 1 | mem → fsm/reg | Memory full |
| `mem_in_occupancy` | `log2(IN_DEPTH+1)` | mem → fsm/reg | Line occupancy |

: Table 3.6: Input-memory read port

### `cell_exec_fsm` → `cell_mem_out`

| Signal | Width | Direction | Purpose |
|---|---|---|---|
| `mem_out_wr_valid` | 1 | fsm → mem | Write valid |
| `mem_out_wr_ready` | 1 | mem → fsm | Write ready |
| `mem_out_wr_addr` | `log2(OUT_DEPTH)` | fsm → mem | Write address |
| `mem_out_wr_data` | `LINE_W` | fsm → mem | Result line |

: Table 3.7: Result-memory write port

### `cell_exec_fsm` → `cell_credit`

| Signal | Width | Direction | Purpose |
|---|---|---|---|
| `credit_strobe` | 1 | fsm → credit | One input line consumed |
| `credit_src_coord` | `COORD_BITS` | fsm → credit | Source coordinate of consumed line |

: Table 3.8: Consumed-line credit strobe

### `cell_credit` → node (credit VC)

`cell_credit` builds header-only `credit`/`add` and `credit`/`set`
packets and injects them into the node's local-port credit sideband.
The packet format is defined in TILE_SPEC §11.5 and §11.9.

### `cell_mem_out` → `cell_packetizer`

| Signal | Width | Direction | Purpose |
|---|---|---|---|
| `pkt_rd_valid` | 1 | pkt → mem | Read request valid |
| `pkt_rd_ready` | 1 | mem → pkt | Read request ready |
| `pkt_rd_addr` | `log2(OUT_DEPTH)` | pkt → mem | Read address |
| `pkt_rd_data` | `LINE_W` | mem → pkt | Result line |
| `mem_out_empty` | 1 | mem → pkt | Memory empty |
| `mem_out_occupancy` | `log2(OUT_DEPTH+1)` | mem → pkt | Line occupancy |

: Table 3.9: Result-memory read port

### `cell_packetizer` → node (data network)

`cell_packetizer` builds write-format packets (`ptype=mem`, `op=0`) with
the §11.5 tile header and sends them through the node's local port. The
destination and tag are supplied by the gatling-programmed drain
command; the source coordinate is the cell's external ID.

### `cell_exec_fsm` ↔ ALU

The ALU interface is defined in the alu-infer MAS; the cell MAS cites
it in Chapter 4.3.

---

**Last Updated:** 2026-10-18
