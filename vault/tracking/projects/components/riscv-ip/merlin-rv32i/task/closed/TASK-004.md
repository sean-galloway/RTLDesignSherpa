# TASK-004: FPGA rework -- the load-to-branch interlock

**Priority:** P2
**Status:** CLOSED (2026-11-21)
**Owner:** Claude (owner, 2026-11-21: "make it so number one.", accepting
the interlock over registering the redirect)
**From:** riscv-ip common-rv32i [ISSUE-001](../../../common-rv32i/issue/open/ISSUE-001.md) row 3

## Why

After TASK-003 the worst path was load data in WB -> the load align ->
the forward mux -> the branch compare -> the redirect, +0.065 ns under one
placer directive. Row 3(b), registering the redirect, would cost every
taken branch a third bubble and change PRD M2. The interlock costs only a
branch or JALR fed by a load.

## What landed

1. **The branch compare and the JALR target read their own operands**,
   `br_rs1` / `br_rs2`. They use the registered forwarding selects, but
   the MEM/WB arm is `mem_wb_q.alu_y`, never load data. `alu_y` equals the
   writeback value for every non-load producer (TASK-003 put the link and
   LUI there; the CSR stub forces it to zero).
2. **`stall_ldbr`**: a branch (rs1 or rs2) or JALR (rs1) in ID whose
   source would be forwarded from MEM/WB while the producer in EX/MEM is a
   load waits one cycle, then reads the value through the regfile's WB
   bypass. It ORs into `stall_ifid` with the hazard unit's load-use stall.
   - Distance 1 (`lw; beq`): the load-use bubble, then this one.
   - Distance 2 (`lw; x; beq`): one bubble.
3. **PRD** §4.2 and M4 record the interlock; M2 is unchanged. The MAS
   load-use and branch chapters and the HAS performance chapter (still
   skeletons, book rev unchanged) name it.
4. **Directed test** `cocotb_test_merlin_hazard_load_branch`
   (`programs/hazard_load_branch.hex`, hand-assembled like the other
   hazard programs): rs1 and rs2, distance 1 and 2,
   taken and not taken, and a JALR at distance 2. It checks the golden
   trace, that no wrong-path slot retires, and that each branch retires 3
   cycles after its load. With `stall_ldbr` removed (the operand muxes
   kept) it fails: the core takes the wrong path and halts at 0x64, not
   0x5c.

## Gates

- merlin suite: `make clean-all && make run-all-full-parallel`, 57/57
  (54 plus the new case at three levels), exit 0.
- riscv-formal merlin: 42/42.

## Result

Routed OOC, xc7a100t-1, 10 ns. One synthesis, three placer directives.
Base 8e14d4198 (merlin unchanged since).

| merlin_core | LUT | WNS Default / ExtraNetDelay_high / SpreadLogic_high |
|---|---|---|
| before | 1,262 / 1,275 / 1,263 | +0.131 / +0.241 / +0.065 |
| after | 1,334 / 1,320 / 1,333 | +0.356 / +0.231 / +0.284 |

- **Timing:** the worst case moves from +0.065 to +0.231 ns, inside the
  0.2 ns budget under all three directives.
- **Area:** about +70 LUT.
- **Worst path now:** MEM/WB `rd_addr` / `wb_sel` or EX/MEM `alu_y` -> the
  ALU operand -> `alu_y` -> the branch / JAL target -> the PC (9-11
  levels). The target is taken from `alu_y`; a dedicated pc + imm adder
  would take the ALU out of the redirect path. Not done: the budget is
  met.
- **Cycles:** on the rv32ui battery's spike streams, 255 interlock
  stalls in 225,324 instructions (0.11 percent; 90 at distance 1, 165 at
  distance 2), most in the load and store tests. The battery is not a
  workload; compiled C with `lw; beqz` will stall more often.
