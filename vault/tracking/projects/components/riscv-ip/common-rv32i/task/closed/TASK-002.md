# TASK-002: riscv-arch-test signatures on the RV32I cores

**Priority:** P2
**Status:** CLOSED (2026-11-22)
**Owner:** Claude (owner, 2026-11-22: "1 and 2 please", the offer to vendor
riscv-arch-test after "I thought there was a specific set of instructions
and a golden output that are out there some where")

## What

RISC-V International's architectural test suite, riscv-arch-test, with
RISCOF's signature compare, on kestrel, merlin and gatling:

- Each test is built twice: once for the DUT, which halts on ecall, and
  once for spike, using the suite's spike plugin env.
- The signature region, read from the TB memory after the halt, must equal
  spike's `+signature` dump.

The method and its traps are in the handbook:
[riscv-arch-test](../../../../../../../handbook/dv/riscv-arch-test.md).

## What landed

1. **The vendor pin.** `vendor/riscv-arch-test` at 3.10.0
   (`fc32e41d4`). It is a shallow clone in the ignored `vendor/` tree, like
   riscv-tests. The harness checks the commit and prints the clone command
   when the tree is missing.
2. **The shared harness.** `common-rv32i/dv/arch_test/rv32_arch_test.py`
   handles discovery, both builds, the spike reference, ELF to image, the
   VPI load and read-back, the compare and the summary. Its
   `dut_model/model_test.h` is the DUT model.
3. **One test file per core.**
   - `kestrel-rv32i/dv/tests/test_kestrel_arch.py` and
     `merlin-rv32i/dv/tests/test_merlin_arch.py` share the runner
     (`run_flat`).
   - `gatling-rv32i/dv/tests/test_gatling_arch.py` runs four different
     tests per round, rotated so every context runs all 39.
4. **TB memory size is a parameter.** `kestrel_tb_top` and `merlin_tb_top`
   now take `MEM_WORDS`. The default stays 64 Ki words; the arch test sets
   512 Ki (2 MiB), because jal-01 is a 1.7 MiB image. gatling's
   `MEM_WORDS` was already a parameter.
5. **Docs.**
   - Falcon-suite design spec: the verification lines for rung 1 and for
     the infrastructure.
   - merlin PRD §5 and gatling PRD §6.
   - kestrel testplan CORE-20.
   - riscv-ip README status rows. merlin's row still said "Planned;
     structure only"; it now lists the battery, the hazard suite,
     riscv-formal and the arch test.

## Result

| Core | gate | func | full |
|---|---|---|---|
| kestrel | 3/3 | 39/39 | 39/39 |
| merlin | 3/3 | 39/39 | 39/39 |
| gatling (context, test) | 12/12 | 156/156 | 156/156 |

- **Mutation check.** kestrel's SH strobe was set to `4'b0001`. That failed
  sh-align-01 alone, 71 of 73 words, and the other 38 tests passed. The RTL
  was then restored.
- **Suites from clean.** `make clean-all && make run-all-full-parallel`
  gave kestrel 66 passed, merlin 60 passed and gatling 45 passed, with no
  failures. The arch cells were green at every level in all three.

## Not done

- **Sail as a second reference.** Sail is RISCOF's default reference model.
  Fetching its release binary was blocked in the session, so spike is the
  only reference. Adding Sail means a second signature that must equal
  spike's.
- **RISCOF itself is not used.** The cocotb flow runs RISCOF's method, and
  the file names match its output. A RISCOF DUT plugin would need a sim
  launch per test.
- **Other extensions.** M, A and F come with peregrine, gyrfalcon and
  garuda.
