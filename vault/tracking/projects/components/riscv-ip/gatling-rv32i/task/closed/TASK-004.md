# TASK-004: FPGA rework -- the per-context PC file in distributed RAM

**Priority:** P2
**Status:** CLOSED (2026-11-19)
**Owner:** Claude (owner, 2026-11-19: "do row 4")
**From:** riscv-ip common-rv32i [ISSUE-001](../../../common-rv32i/issue/open/ISSUE-001.md) row 4

## What landed

1. **`pc_q[NUM_HARTS]` (128 async-reset flops, loop write, mux read) is now
   `pc_mem[NUM_HARTS]`, a distributed RAM.** It has one write port (X, at
   `x_ctx`) and one asynchronous read port (F, at `sel_q`). The rotation
   keeps the two on different contexts.
2. **`pc_fresh[c]` stands in for the reset that a RAM cannot have.**
   - Reset sets it, and so does `hart_run[c]` low.
   - The context's first PC write clears it.
   - While it is set, F reads `RESET_ADDR`.
   - A halt writes no PC and leaves the flag alone, so a context that halts
     on its first instruction after release still reads that instruction's
     address. That matches the old flop array cycle for cycle.
3. **`halted_q` and `cause_q` stay flops.** The `halted` and `halt_cause`
   ports present every context at once, which would need NUM_HARTS read
   ports. The issue row's "cause / halt" part is closed on that reason:
   it is 20 flops.
4. **One test changed outside the area.**
   `dma-ip/rapids/dv/tests/top_g/test_rapids_g_restart.py` probed `pc_q`
   to compare the harts' timing after two restarts. It now rebuilds the
   per-hart PC vector from the fetch port (`sel_q`, `imem_addr`), which
   carries the same information one stage later.
5. **The gatling MAS** (ch02 core chapter, the datapath and rotation-grid
   diagrams, re-rendered) names the PC file and the flag.

## Gates

- gatling suite: `make clean-all && make run-all-full-parallel`, 42/42.
- riscv-formal gatling: 42/42. The RAM starts unconstrained in formal; `pc_fresh` masks it until the first write.
- rapids `fub_g macro_g top_g` (the gatling sequencer and the restart
  test), `make clean-all && make run-all-full-parallel AREAS="fub_g macro_g
  top_g"`: 192 + 270 + 183 passed, all three restart cells included.

## Result

Routed OOC, xc7a100t-1, 10 ns. One synthesis, three placer directives.
The base is HEAD 8e14d4198 (row 1 in).

| gatling_core | Slice LUT (of which LUTRAM) | FF (FDCE) | WNS Default / ExtraNetDelay_high / SpreadLogic_high |
|---|---|---|---|
| before | 1,308 (0) | 894 (409) | +0.190 / +0.470 / +0.196 |
| after | 1,200 (22) | 772 (281) | +0.424 / +0.506 / +0.660 |

- **Area:** 130 fewer logic LUTs, offset by 22 LUTRAM (34 RAMD32 + 10
  RAMS32), and 122 fewer flops. The issue estimated about 11 LUTRAM. Vivado
  builds the 4 x 32 RAM from RAM32M-class primitives, two bits per site
  pair, hence 22.
- **Timing:** the worst case moves from +0.190 to +0.424. The critical cone
  is the same before and after: register file read -> branch compare /
  misaligned target -> `halt_now` -> the context-state write enables. What
  changed is the end of the cone. Before, it was the per-context clock
  enables of 128 PC flops (`pc_q_reg[1][17]/CE`). Now it is the RAM's
  write enable (`pc_mem_reg_*/RAMA/WE`) or a `cause_q` enable.
