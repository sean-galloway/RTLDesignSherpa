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

<!-- End Header -->

# Verification Summary

This chapter summarizes how the RTL described here was verified. The stage-by-stage record, with every mutant and the failures that changed a test, is riscv-ip/peregrine-rv32im TASK-001 [REF-7]; the hooks the tests use are in the MAS.

## Regression

The suite lives in `peregrine-rv32im/dv/tests` (Pattern B cocotb tests, Verilator, gate / func / full levels). The final run of TASK-001, after the last RTL edit: **88/88 cells at full, from `make clean-all`, no reruns** (seed base 489778646).

| Test | Device under test | What it checks |
|------|-------------------|----------------|
| `test_peregrine_battery` | cacheless core | rv32ui, rv32mi, rv32um from `vendor/riscv-tests`, in spike lockstep (pc, insn, every trap's kind and epc); both `MUL_DSP` builds |
| `test_peregrine_arch` | both builds | riscv-arch-test 3.10.0 `rv32i_m/M` and `Zifencei`, signatures equal to spike's and Sail's |
| `test_peregrine_irq` | cacheless core | Self-checking interrupt program with a seeded random re-raise delay |
| `test_peregrine_mext` | cacheless core | Generated programs of 15 hazard shapes around M instructions; register compare, RVFI shadow regfile, spike lockstep; interrupt and `mem_wait` variants |
| `test_peregrine_predictor` | cacheless core | The PRD §5 predictor streams on both `BP_EN` builds, every retired prediction held to a model; the A/B comparison |
| `test_peregrine_mdu` | `peregrine_mdu` | All eight operations against a spec model: edge cross product plus seeded random; exact stall counts, cancel at every step |
| `test_peregrine_bpred` | `peregrine_bpred` | Against an exact model, cycle by cycle, with randomized initial memory contents |
| `test_peregrine_icache` | `peregrine_icache` | Exact refill counts (cold, warm, conflict, invalidate, last-beat miss), random streams, every word against the memory model |
| `test_peregrine_axi4_arb` | `peregrine_axi4_arb` | Three masters, a slow out-of-order fabric; R/B routing by id, W order |
| `test_peregrine_clint` | `peregrine_clint` | Against a cycle model, `MTIME_DIV` 1 and 3 |
| `test_peregrine_sys` | `peregrine_top` | rv32ui (with `fence_i`), rv32um, rv32mi in spike lockstep on the cached build; a memory-stall soak; interrupts through the CLINT and the pins; self-modifying code through dirty D\$ lines; the uncached window; the interrupt lock |
| `test_peregrine_amber_latency` | amber's pair rig | amber's CPU-port hit latency, asserted at the numbers PRD P13 records |

: The peregrine regression

## ISA Batteries

| Battery | Result | Notes |
|---------|--------|-------|
| rv32ui | 42/42 | `ma_data` is an expected failure (misaligned loads trap), as on spike |
| rv32mi | 12/16 | Four excluded for hardware PRD P6 leaves out: counters (`zicntr`, `instret_overflow`), debug triggers (`breakpoint`), PMP regions (`pmpaddr`) |
| rv32um | 8/8 | Both `MUL_DSP` builds |
| riscv-arch-test `rv32i_m/M` | 8/8 | Cacheless on both `MUL_DSP` settings, and cached |
| riscv-arch-test `Zifencei` | 1/1 | Cached and cacheless |

: ISA battery results

## Formal (PRD P12, TASK-001 Stage 5)

Under `formal/peregrine/`, SymbiYosys BMC on sv2v flats:

| Unit | Build | Result |
|------|-------|--------|
| riscv-formal, `checks` and `checks_dsp` | `peregrine_core`, `CACHE_EN=0`, predictor live with free initial tables, traps in, interrupts tied low | 52/52 on each `MUL_DSP` setting |
| `core_props` | `peregrine_core`, every input free | 22 asserts at depth 20: the predictor training rule and commit precision; 11/11 covers |
| `top_props` | `peregrine_top` with an amber stub whose response data is free on every cycle | Depth 28: every D-side access accepted once and retired with its own data; every fetch carries the memory word; 9/9 covers |
| `mdu_ref` | `peregrine_mdu` against the M reference | Bounded operands, depth 40: six of eight operations pass; `mulh` and `mulhsu` reached steps 38 and 37 in the time cap |

: Formal results

Two scope limits were decided by the owner (2026-11-25):

- **Divide instruction checks at depth 15.** At depth 45 the divide and remainder checks did not finish; at 15 they check the early-out path only. The full 32-step divide is covered by the multiply checks (which pass at 45 and share the unit's control), by `mdu_ref`, and by simulation.
- **A bounded M reference proof.** A full-width proof of the shift-add and shift-subtract against `*`, `/` and `%` is not tractable. The proof limits each operand's upper 24 bits to 0x000000, 0xFFFFFF, 0x800000 or 0x7FFFFF with the low byte free, which still reaches every step, sign case and early-out; full-width arithmetic is simulation's.

The M extension runs under riscv-formal's ALTOPS stand-in results, defined only in the formal build (`RISCV_FORMAL_ALTOPS`), with the real hold-in-EX timing.

## Mutation

Every stage ended with a mutation pass: each mutant rebuilt from clean, the failure read for its cause, the tree restored. The final stage-7 pass caught 26 of 27; the survivor (a D\$ clean issued while an access is in flight) is equivalent, because amber is blocking. The formal units caught 10 of 10 (`core_props`), 8 of 8 (`top_props`), 10 of 11 riscv-formal mutants (one equivalent) and 5 of 6 `mdu_ref` mutants (one equivalent).

## Known Limits

- Interrupts are not in riscv-formal (P12); the directed suites and `core_props` cover them.
- On some beats the predictor check accepts either of two predictions the pipeline timing allows; pinning those needs the lookup cycle modelled exactly.
- No board run: peregrine has been verified in simulation and formal only. The hive-serv HIVE-C integration is its planned system bring-up (TASK-004).

---

**Last Updated:** 2026-11-25
