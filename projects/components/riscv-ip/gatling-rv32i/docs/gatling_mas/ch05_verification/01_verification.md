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
| `test_gatling_mem_bram` | Through AXIL: the map, banks, strobes, alias; a running bank refuses writes; reload one context while another runs; STATUS/CPI; the battery loaded and run entirely over AXIL |

: Table 5.1: DV

Each context's trace is checked with kestrel's own trace checks and against kestrel's golden interpreter and spike: gatling's ISA contract is kestrel's, so its goldens are too.

Mutation (each planted bug must turn a green suite red): register writes ignoring the context fail every directed test and the battery; the W stage ignoring `hart_run` fails run control. Both mutants first exposed weak checks -- the gate battery checked only the verdict, and run control allowed one leaked beat -- which were tightened before the RTL was trusted.

## Formal (formal/gatling/riscv-formal)

riscv-formal observes one hart. The wrapper reports context 0's retirements and leaves contexts 1-3 free -- their instructions, load data and run bits are unconstrained every cycle -- with context 0 held running. All 42 checks pass. Beyond the RV32I insn checks on context 0, `reg`, `pc_fwd` and `pc_bwd` therefore prove that nothing the other contexts execute, and no way they are started or stopped, can disturb context 0's registers or PC. The rotation treats all four contexts alike, so the proof stands for each.

Depths are on context 0's retirement phase (cycle 3 mod 4): an insn check fires at one cycle and assumes a retirement there, and off-phase that assumption is unsatisfiable (sby PREUNSAT), not a vacuous pass. Non-vacuity was measured: an ADD bug fails insn_add at depth 11; register writes ignoring the context fail `reg`; context 0's PC written by other contexts fails `pc_fwd` and `liveness`.
