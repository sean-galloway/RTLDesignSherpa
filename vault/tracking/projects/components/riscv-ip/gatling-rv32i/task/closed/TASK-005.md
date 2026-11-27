# TASK-005: Interlock liveness proof and the tetrad on a board

**Priority:** P2
**Status:** CLOSED (2026-11-27)
**Owner:** Claude (owner, 2026-11-26: "file them then finish gatling")
**From:** [TASK-002](TASK-002.md), "Not done here"

## What landed

1. **Bounded liveness of the Xcell interlock** (`formal/gatling/xcell_live`).
   - The DUT is the real `gatling_core` (XCELL_EN = 1) and `gatling_xcell`.
     It runs against an abstract cell whose every wait is fair (K = 4).
   - The free instruction word is constrained to the program contract,
     now written in MAS 2, gatling_xcell, "The program contract".
   - prove_live: every context retires every 72 cycles. PASS, BMC depth 100.
   - prove_isolate: context 0 may starve, and contexts 1-3 still retire.
     PASS, BMC depth 100.
   - cover: all three reached, steps 12-18.
   - The first run failed because of the harness, not the RTL. The model ALU
     could drop `alu_result_valid` before it was taken. Fixed with a held
     valid, and recorded in the handbook (dv/formal.md).
   - Mutant: a FLUSH that never clears its pending bit fails at step 82.
   - Unbounded abc pdr reached frame 54 in 7 h without converging. It is
     not kept as a task.
2. **The tetrad on the Nexys A7.**
   - The build is `projects/fpga-systems/NexysA7/riscv-ip/gatling/build-tetrad`.
   - The rig: UART -> AXIL -> barrel BRAM program memory, plus a cell harness
     (config, fill, drain, FLUSH capture, KICK log).
   - It uses alu-infer's bf16 profile and runs at 4.6875 MHz.
     WNS +54.762 ns, with 0.2 ns uncertainty.
   - The tetrad program is authored once (`dv/tbclasses/gatling/tetrad_program.py`).
     It is shared by `test_gatling_tetrad` and the board host.
   - UART-equivalence sim: 2/2. Board runs: N = 96 seed 1 and N = 384 seed 7,
     both PASS and golden-identical.
   - A mutant that flips one drained bit fails seven checks.
   - The first board run answered one read with ERR, filed as
     [ISSUE-001](../../issue/open/ISSUE-001.md). `GatlingBoard.read` now
     raises on it.

## Gates

- gatling suite, `make clean-all && make run-all-full-parallel`: 69/69.
- Nexys A7 gatling build-bram sim 3/3; build-tetrad sim 2/2; board as above.
- MAS 5 (Tables 5.2, 5.3) and PRD 6 record the results.
