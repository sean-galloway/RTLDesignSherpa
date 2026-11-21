# TASK-003: FPGA rework -- control-only pipeline-register reset, registered forwarding selects

**Priority:** P2
**Status:** CLOSED (2026-11-19)
**Owner:** Claude (owner, 2026-11-19: "push then start a.")
**From:** riscv-ip common-rv32i [ISSUE-001](../../../common-rv32i/issue/closed/ISSUE-001.md) rows 2 and 3a

## What landed

1. **Row 2: the pipeline registers reset and flush only their control
   fields.** These are valid, rd_wen, dmem_req, dmem_we, branch, jump, jalr,
   ls_misalign, halt_cause and csr_stub, each where the struct has it. The
   payload is a plain enable flop.
   - Two consumers had read payload unqualified. They are fixed:
     - The reset-time x0 write's zero-data select now reads the forced
       `wb_rd_addr`.
     - `idex_is_load` is now gated by `valid`.
   - `test_merlin_pipe_regs.py` now checks the new contract: the controls
     clear, and under stall + flush the payload holds.
2. **Row 3a: the forwarding selects are computed in ID, one cycle ahead,
   and registered beside ID/EX.** The hazard unit is unchanged. The core
   feeds it the ID sources (`id_ex_d`) against the producers that will be in
   EX/MEM and MEM/WB next cycle (`id_ex_q`, `ex_mem_q`). The select register
   takes ID/EX's stall and flush.
3. **The WB value is a two-way select.** A jump's link (pc + 4, the adder
   `ex_next_pc` already has) is written into `alu_y` in EX. LUI's ALU
   result is already its immediate. WB drops its pc + 4 adder and the LUI
   and link arms. This step came from the measurement: with rows 2 + 3a
   alone, the worst path started at the WB link adder (WNS -0.202).

## Gates

- merlin suite: `make clean-all && make run-all-full-parallel`, 54/54.
- riscv-formal merlin: 42/42. This is the run that matters for row 2. The
  unreset payload starts unconstrained in formal, and formal caught the x0
  bug (7/42) that the suite also failed on (45/54).

## Result

Routed OOC, xc7a100t-1, 10 ns. One synthesis, three placer directives.

| merlin | LUT | FDCE | WNS Default / ExtraNetDelay_high / SpreadLogic_high |
|---|---|---|---|
| before (row 1, 98eedce98) | 1,378 | 811 | +0.227 / -0.216 / -0.014 |
| after | 1,262 | 134 | +0.131 / +0.241 / +0.065 |

The worst case improves by 0.28 ns, and merlin meets 100 MHz under all
three directives. Before, it failed two of them. The margin is still under
0.25 ns. The worst path is now load data in WB (`alu_y[1:0]` -> load
align) -> the forward mux -> the branch compare -> the redirect. That is
row 3b's cone (register the redirect, one more branch-penalty cycle),
which stays an owner decision.

Intermediate builds (Default directive), each passing suite and formal:
- 3a alone: 1,350 LUT, -0.490.
- 3a + row 2: 1,115 LUT, -0.202.
- Link value selected in MEM instead of EX: 1,238 LUT, sweep
  +0.229 / +0.013 / +0.304. Equivalent to EX within the spread; EX was
  kept because it reuses an existing adder and has 35 fewer flops.
