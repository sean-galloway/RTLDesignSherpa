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
