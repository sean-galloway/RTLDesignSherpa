# TASK-002: Cell slice 3 — cell_exec_fsm + ALU hookup + MonBus observer

**Priority:** P1
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

Slice 3 completes the standalone cell: the execution FSM that pops input
lines, issues invocations into the alu-infer elastic pipeline, and pushes
result lines. This is the bring-up driver; per the owner ruling 2026-10-19,
gatling later SEQUENCES the same ALU (POP -> issue, PUSH -> retire,
FLUSH -> drain) — the exec FSM stays as the standalone driver with the same
client contract, so nothing here is throwaway.

## What

Per cell MAS v0.12 ch04.3:

- `cell_exec_fsm`: Pop (OP_LINES input lines, advance IP) -> Issue (present
  operand lines + func_sel + acc_ctrl, hold while ready low) -> Push
  (result_valid && result_ready -> cell_mem_out, advance OP). Pipelined:
  issue every clock the ALU accepts.
- Instantiate `alu_infer_top` in cell_top (the slice-1 read-port tie-off at
  cell_top.sv:392 and the cell_mem_out write tie-off come out).
- OP_SRC mux: input-memory pop or persistent A/B/C/D registers; T immediate
  for opcode 6.
- MonBus observer leaf in cell RTL (MAS ch03 notes it is not yet in RTL).

## Done when

cell_exec_fsm RTL in `cell/rtl/`, alu_infer_top instantiated and wired,
func+gate green with an end-to-end cell program (fill -> compute -> drain)
in the cell DV suite, MonBus observer streaming, MAS status lines move to
built.

## Notes

Depends on TASK-001 (slice 2) for the drain path. This is the last cell
rung before tile milestone M1 (tetrad on the FPGA, TILE_SPEC 12).
