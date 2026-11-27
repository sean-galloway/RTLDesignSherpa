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


# Verification

## DV (dv/tests, make/tests.mk rails)

| Test | What it checks |
|---|---|
| `test_gatling_regfile` | Registered read on both ports, x0 zero in every context, contexts isolated, the barrel's read-D/write-W pattern; random traffic against a model at func/full |
| `test_gatling_core` | Four different programs interleaved, each golden-identical; every halt kind on its own context (context-lock); Xcell custom-0 locks only its context; run control (lone context, late start, stops at all four rotation phases, restart); the CSR stub (cycle, time, instret, their high halves, mcycle and mhartid read 0, writes dropped, nothing halts) |
| `test_gatling_core_num_harts` | The interleave, context-lock and CSR-stub cases again on an eight-context build (`NUM_HARTS=8`): the TB reads the hart count off the DUT and scales the programs, the window and the rotation check to it, so the parameter is exercised, not just elaborated. The register file is 256 entries there and the rotation counter wraps at 7 |
| `test_gatling_rv32ui` | The riscv-tests rv32ui-p battery: four different images at once, rotated so every context runs all 42 (168 runs); golden full-field diff at every level, spike lockstep at func |
| `test_gatling_fuzz` | kestrel's constrained-random generator; four different streams at once; golden and spike on every stream at every level (5 / 25 / 200 streams) |
| `test_gatling_xcell` | On `gatling_tetrad` with the real cell memories and alu-infer: CFG (element format, credit batch, zeros) and funct3 111 illegal; POP rd / PUSH rs1 over more lines than either memory holds, with POP stalling on an empty memory and PUSH on a full one; POP x0 / PUSH x0 through four ALU row families (add, mul, relu, compare-with-threshold) against alu-infer's golden; a CLEAR-then-ACCUMULATE MAC chain driven by POP's acc_ctrl; FLUSH held behind an unaccepted command; KICK / WAIT as a barrier, a done context satisfying a WAIT, and event bits clearing on hold; one context stalled for hundreds of cycles while three finish. Every context's beats are a whole number of windows apart: a stall retires nothing |
| `test_gatling_tetrad` | The hand-assembled tetrad program (TASK-002's "Done when"): one binary on four contexts over a MAC, an ADD, a RELU and a COMPARE cell -- CLEAR, N ACCUMULATE invocations, KICK, WAIT on all four, FLUSH, ECTX -- with random gaps on the fill, the drain and the drain controller. Checks every result line against alu-infer's golden, the consumed-line ledger, one FLUSH per context after the last KICK, the retired-instruction count and window spacing |
| `test_gatling_mem_bram` | Through AXIL: the map, banks, strobes, alias; a running bank refuses writes; reload one context while another runs; STATUS/CPI; the battery loaded and run entirely over AXIL |

: Table 5.1: DV

Each context's trace is checked with kestrel's own trace checks and against kestrel's golden interpreter and spike: gatling's ISA contract is kestrel's, so its goldens are too.

Mutation (each planted bug must turn a green suite red): register writes ignoring the context fail every directed test and the battery; the W stage ignoring `hart_run` fails run control. Both mutants first exposed weak checks -- the gate battery checked only the verdict, and run control allowed one leaked beat -- which were tightened before the RTL was trusted.

Xcell mutation (2026-11-26), each planted in the RTL and run against the Xcell and tetrad cases at gate: POP x0 ignoring the input memory's occupancy; operand B captured from line A; a stall still writing the PC; WAIT ignoring done; acc_ctrl taken from the wrong instruction bits; FLUSH overwriting an unaccepted command. All six fail the suite. The first was missed at first -- every input line was in memory before the first POP x0 -- and the ALU cases now hold one cell's input back and require its POP x0 to wait.

## Formal (formal/gatling/riscv-formal)

riscv-formal observes one hart. The wrapper reports context 0's retirements and leaves contexts 1-3 free -- their instructions, load data and run bits are unconstrained every cycle -- with context 0 held running. All 42 checks pass. Beyond the RV32I insn checks on context 0, `reg`, `pc_fwd` and `pc_bwd` therefore prove that nothing the other contexts execute, and no way they are started or stopped, can disturb context 0's registers or PC. The rotation treats all four contexts alike, so the proof stands for each.

Depths are on context 0's retirement phase (cycle 3 mod 4): an insn check fires at one cycle and assumes a retirement there, and off-phase that assumption is unsatisfiable (sby PREUNSAT), not a vacuous pass. Non-vacuity was measured: an ADD bug fails insn_add at depth 11; register writes ignoring the context fail `reg`; context 0's PC written by other contexts fails `pc_fwd` and `liveness`.

## Formal: interlock liveness (formal/gatling/xcell_live)

The proof runs the real `gatling_core` (XCELL_EN = 1) and `gatling_xcell`, wired as `gatling_tetrad` wires them, against an abstract cell. Each context's input memory, result memory, ALU and FLUSH acceptor is a counter whose every wait is fair: a fill, a drain, an ALU accept, a returned result and a FLUSH accept each come within K = 4 cycles of being due. The instruction word is free each fetch and constrained to the program contract (Chapter 2, gatling_xcell): ADDI and the Xcell POP, PUSH, FLUSH, KICK and CFG; PUSH x0 only with an invocation outstanding; at most PIPE_DEPTH + 1 POP x0 outstanding; the same word on a refetch of the same PC. WAIT and ECTX are left out because their release is a program property.

| Task | Claim | Result |
|---|---|---|
| prove_live | every context retires at least once every 72 cycles; no halt, no trap; the environment keeps the valid/ready protocol | PASS, BMC depth 100 |
| prove_isolate | context 0's input memory may starve forever, and contexts 1-3 still retire every 72 cycles | PASS, BMC depth 100 |
| cover | an ALU result reaches PUSH x0; a two-line function on context 3; PIPE_DEPTH + 1 invocations outstanding | all reached, steps 12-18 |

: Table 5.2: Interlock liveness

Depth 100 covers the bound plus the core's reset synchronizer, so a context that stops retiring for 72 cycles anywhere in the first 100 is a counterexample. Each wait is at most K cycles, and a context retries every four, so a deadlock shows itself well inside that window. An unbounded run (abc pdr) reached frame 54 after 7 hours without converging and is not kept as a task.

The first clean run failed at step 73 with context 0 stuck on PUSH x0, and the fault was the environment. Its ALU could drop `alu_result_valid` before the result was taken, so the solver offered each result only on cycles that missed context 0's X slot. A valid/ready interface holds valid until ready, and alu-infer's does. The model now does too, and the lesson is in the handbook's formal note. Mutation: a FLUSH that never clears its pending bit fails prove_live at step 82, with all four contexts stuck on FLUSH.

## Board (Nexys A7, build-tetrad)

The tetrad runs on the Nexys A7-100T (`projects/fpga-systems/NexysA7/riscv-ip/gatling`, build-tetrad): `gatling_tetrad` with alu-infer's bf16 profile behind the barrel's block-RAM program memory and a cell harness that configures each cell, fills its input memory, drains its result memory and captures its FLUSH commands, all over UART. The host runs the same tetrad program as `test_gatling_tetrad` (`dv/tbclasses/gatling/tetrad_program.py`, authored once), and a UART-equivalence sim runs the same host code against the same rig.

| Run | Result |
|---|---|
| UART sim, N = 40 | PASS: both 32-line memories overfilled, so refill and PUSH waits happen |
| Board, N = 96, seed 1 | PASS: 97 results per cell, every one golden-identical; one KICK and one FLUSH per context, each FLUSH after all four KICKs; all four DONE |
| Board, N = 384, seed 7 | PASS: 385 results per cell, golden-identical |

: Table 5.3: The tetrad on the board

The clock is 4.6875 MHz (WNS +54.762 ns with 0.2 ns uncertainty): alu-infer's rows are combinational at their default latencies, and the worst path runs 158.1 ns from the Xcell unit's latched function through an ALU row (alu-infer TASK-010). A harness mutant that flips one bit of every drained line fails seven result checks. The first host run answered one read with ERR, unexplained and not reproduced since (ISSUE-001).
