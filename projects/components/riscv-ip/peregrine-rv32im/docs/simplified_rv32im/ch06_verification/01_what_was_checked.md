# What Was Checked

Each check can see some bugs and is blind to others. The interesting part
of peregrine's verification is which check covers which blind spot.

| Check | What it runs | What it proves | What it cannot see |
|-------|--------------|----------------|--------------------|
| riscv-tests batteries | rv32ui 42/42, rv32um 8/8, rv32mi 12/16 (four need hardware P6 leaves out) | The ISA, self-checked by each test | Timing; anything a test does not exercise |
| spike lockstep | Every battery image, instruction by instruction | Retired PC, instruction and every trap's kind and `mepc` match the reference | Prediction; anything spike cannot model |
| riscv-arch-test | `rv32i_m/M` 8/8 and `Zifencei`, signatures equal to spike's and Sail's | Architectural results | Same as above |
| RVFI shadow checks | A shadow register file and CSR model on every retire | Every operand read and every result, on every beat | Prediction (it is not architectural) |
| Predictor retire-stream check | Every retired guess against the model (Section 2.4) | Prediction and the mispredict flag | Beats where the allowed states disagree |
| riscv-formal | 52 checks on the cacheless build, both multiplier builds | Every instruction, PC flow, register file, liveness, with the predictor and traps live | Interrupts (tied off); CSR checks (no `rvfi_csr_*` ports) |
| Targeted formal | Predictor training, commit precision, D-side and fetch properties | Write rules and commit rules riscv-formal cannot see | Beyond the proof depth |

: The verification set (TASK-001 stages 1 to 5)

## The formal scope, and where it stopped

riscv-formal's M-extension checks use its stand-in operations, so the
arithmetic is checked elsewhere. Two places were not tractable at full
scope; the owner accepted the reduced scope on 2026-11-25:

- **Divide and remainder at depth 15.** At the depth a full 32-step
  divide needs, each check was still unsolved after 30 minutes on the
  last step: the early-out lets about 40 cycles of arbitrary history come
  before the checked divide. Depth 15 checks the early-out path. The
  32-step path shares its control with the multiplies, which pass at
  depth 45, and its arithmetic is covered by the bounded proof below and
  by simulation.
- **The M unit against reference arithmetic over bounded operands.** At
  full 32-bit width the solver sat on the first cycle a result exists for
  59 minutes. With each operand's upper 24 bits limited to four patterns
  and the low byte free, every step, sign case and early-out is reached.

## A stub kinder than the spec

amber keeps its last response on its data port after the valid cycle.
The spec does not promise that. Two stage-7 bugs (an early response not
handed to WB, or handed to the wrong instruction) read that data a cycle
late and still passed every simulation, because the held word happened
to be right. Two fixes, one per tool:

- in simulation, a test-only switch (`RSP_SCRAMBLE`) drives amber's
  response with random data whenever its valid is low;
- in formal, amber is replaced by a stub that drives a free response
  beat every cycle.

Both then caught the bugs at once. A model that is kinder than the spec
hides exactly the bugs the spec allows.
