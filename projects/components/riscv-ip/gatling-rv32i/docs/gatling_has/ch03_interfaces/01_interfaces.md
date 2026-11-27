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


# Interfaces

## Core memory ports

`gatling_core` has an instruction port and a data port, each carrying the requesting context. Both expect registered-read memory: the data is used exactly one cycle after the request, and nothing waits (there is no wait input).

| Port | Signals | Contract |
|---|---|---|
| Instruction | `imem_ctx`, `imem_addr` -> `imem_rdata` | The word at {ctx, addr} the next cycle |
| Data | `dmem_req`, `dmem_ctx`, `dmem_addr`, `dmem_wstrb`, `dmem_wdata` -> `dmem_rdata` | Word-aligned address, lane strobes; a load's word the next cycle |
| Run | `hart_run[NUM_HARTS-1:0]` (four by default) | Per context: 1 run, 0 hold at RESET_ADDR |
| Status | `halted[3:0]`, `halt_cause[3:0][3:0]`, `done[3:0]` | Per context; `done` is a halt by ECTX |
| Xcell | `xc_req`, `xc_ctx`, `xc_funct3`, `xc_reg0`, `xc_rs1`, `xc_imm` -> `xc_ok`, `xc_rdata` | With `XCELL_EN = 1`: the Xcell instruction in X, answered the same cycle; its value the next |
| Retire | `rvfi_*`, `rvfi_ctx` | riscv-formal RVFI, one beat per cycle at most, tagged with its context |

: Table 3.1: gatling_core interfaces

## The tetrad seams (gatling_tetrad)

`gatling_tetrad` is gatling with Xcell built (`XCELL_EN = 1`) and, per context, the three cell blocks the Xcell instructions reach: `cell_mem_in`, `alu_infer_top` and `cell_mem_out` (compute-eng-ip). The rest of the cell is not built yet (cell TASK-001/002), so its seams are `gatling_tetrad`'s ports, one per cell:

| Seam | Signals | Contract |
|---|---|---|
| Configuration | `cfg_func_sel`, `cfg_op_lines`, `cfg_threshold`, `cfg_credit_batch` | The cell's in-band cfg registers: the ALU function, its operand-line count (1 or 2), the compare threshold, the credit batch |
| Input fill | `min_wr_valid/ready/addr/data`, `min_occupancy` | The rx demux writes lines at its own tail; POP reads from the head |
| Consumed lines | `line_consumed` | One pulse per line popped, for the credit block |
| Result drain | `mout_rd_valid/addr/data`, `mout_occupancy` | The packetizer reads in order; registered read |
| Drain command | `flush_valid/ready`, `flush_dest`, `flush_tag` | One FLUSH, held until taken |
| Events and status | `kick_valid/value`, `event_flags`, `ctx_stalled`, `ctx_stall_op`, `done`, `alu_err_opcode` | For the tetrad MonBus: KICKs, raised events, which context is waiting on which Xcell instruction, which are done |

: Table 3.2: gatling_tetrad cell seams

## Board memory map (gatling_mem_bram, over UART -> AXI4-Lite)

| Address | Name | Access |
|---|---|---|
| 0x0_0000 + 0x4000*c | context c memory (16 KB; addr[16] aliases) | R any time; W only while context c is stopped (dropped otherwise) |
| 0x2_0000 | CTRL | W bits[3:0] run per context; R {halted[7:4], run[3:0]} |
| 0x2_0004 | BUILD_ID | R "GATL" (0x4741_544C) |
| 0x2_0100 + 0x10*c | STATUS, CYCLES, INSTRET, GP of context c | R; kept after a stop, cleared when the context is started |

: Table 3.3: Board memory map

### Figure 3.1: The board address map

![gatling_mem_bram address map over AXI4-Lite: four banks, the alias, CTRL, BUILD_ID and the per-context status block](../assets/graphviz/gatling_board_address_map.png)

A host loads a context by stopping it, writing its bank and setting its run bit; the other contexts can keep running throughout. The host driver is `projects/fpga-systems/NexysA7/riscv-ip/gatling/bin/gatling_board.py`.
