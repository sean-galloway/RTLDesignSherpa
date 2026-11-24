---
title: riscv-arch-test signatures
summary: RISC-V International's architectural suite on the falcon cores; RISCOF's DUT-vs-reference signature compare inside the cocotb flow, against spike and Sail, which must agree; the relaxation and memory traps.
---

# riscv-arch-test (the golden-output suite)

riscv-tests (`rv32ui-p-*`) is self-checking: each test computes, compares
and reports pass or fail through `tohost`, so a core that computes the
same wrong answer as the test's own check passes. riscv-arch-test, the
suite RISC-V International publishes for ISA compliance, is not
self-checking: each test stores its results into a signature region
between `begin_signature` and `end_signature`, and a reference model's
signature for the same test is the golden output. RISCOF is the official
driver: a DUT plugin and a reference plugin (Sail or spike) build and run
each test, and RISCOF diffs the two signature files. This repo runs both
references and requires them to agree.

## What this repo runs

- **Pin:** `vendor/riscv-arch-test` at tag 3.10.0
  (`fc32e41d49480fd99ba0a192dfff9c3319b44873`), a shallow clone. Like
  riscv-tests and riscv-formal it is in the ignored `vendor/` tree.
  `rv32_arch_test.ensure_vendor` checks the commit and prints the clone
  command when the tree is missing. 3.10.0 is the last 3.x release; 4.x is
  a different framework, not a version bump.
- **Scope:** `rv32i_m/I`, 39 tests, on kestrel, merlin and gatling;
  `rv32i_m/M`, 8 tests, on peregrine (2026-11-23). The A and F rungs add
  their directories when they land.
  - The extension is a parameter of the runner (`ext="I"` default,
    `ext="M"`). It picks the source directory, `-march` (`rv32i` or
    `rv32im`) and spike's `--isa`, and the gate subset (M: mul-01,
    div-01, remu-01). Sail's default RV32 config already has M.
- **Harness:** `projects/components/riscv-ip/common-rv32i/dv/arch_test/`.
  `rv32_arch_test.py` builds, runs the reference and compares. `dut_model/model_test.h`
  is the DUT model: `RVMODEL_HALT` is `ecall`, which every falcon core
  halts on.
- **Per core:** `test_<core>_arch.py` in kestrel, merlin and gatling. A
  test passes when the core halts with cause 1 at `rvmodel_halt` and every
  signature word read from the TB memory equals the reference's.
- **A core with real traps** cannot halt on `ecall`: peregrine traps it to
  `mtvec`. Its harness builds with `halt="tohost"` and runs `run_tohost`.
  The DUT image is the reference build itself, which ends on the suite
  env's `tohost` store, so the DUT and reference images are identical. A
  test passes on a tohost value of 1 and a signature equal to the
  reference's. `test_peregrine_arch.py` runs it on both `MUL_DSP` builds.
  - Gate runs 3 tests (add-01, lw-align-01, sw-align-01).
  - Func and full run all 39.
  - gatling runs four different tests at once, rotated so each context runs
    all 39 (156 runs).

## The RISCOF method, kept

- **Two builds per test.** The DUT build uses this repo's
  `model_test.h`. The reference build uses the suite's own spike plugin env
  (`riscof-plugins/rv32/spike_simple/env`, which halts on a tohost store).
  Both link with that plugin's `link.ld`, so the two images differ only in
  the halt sequence. The tests are written to be independent of layout.
- **Two references, which must agree.** Both run the same reference ELF.
  - spike, `--isa=rv32i +signature=<f> +signature-granularity=4`: the
    reference RISCOF's spike plugin uses.
  - Sail, RISCOF's default reference model: `sail_riscv_sim --rv32
    --test-signature <f>`, the default RV32 configuration.
  - If the two signatures differ, the build raises: the golden output is
    undefined, so no core result is recorded. Agreement since 2026-11-22:
    39 of 39.
- **Sail pin:** the riscv/sail-riscv 0.16 release tarball, unpacked into
  `vendor/sail-riscv/` (ignored, like the suite). `ensure_sail` checks
  `--version` and prints the curl command when it is missing;
  `RV_ARCH_SAIL` overrides the binary. The 3.x RISCOF Sail plugin calls the
  old `riscv_sim_RV32` name; current Sail ships one `sail_riscv_sim` that
  takes `--rv32` or a JSON `--config`. The harness calls Sail itself, so
  the plugin's name does not matter.
- **Output files:** each test leaves `Reference-spike.signature`,
  `Reference-sail.signature` and `DUT-<core>.signature` side by side under
  `logs/arch_test_<level>/<test>/`. That is RISCOF's naming, so a failing
  pair diffs with any tool.

## Traps

- **Build with `-mno-relax`.** `arch_test.h`'s fixed-length `LA()` pads
  with `.option rvc` alignment. With linker relaxation on, the linker
  shrinks the padding to a 16-bit `c.nop`, which is illegal on RV32I.
  spike `--isa=rv32i` then traps on it in a loop, never reaches the halt,
  and the run looks like a hang (add-01, 2026-11-22). After the fix,
  `objdump` shows zero 16-bit encodings across all 39 tests.
- **spike checks `tohost` only every 5,000 instructions.** A commit log
  from a run that has halted keeps spinning in the halt loop until the next
  poll. Count retired instructions up to the first tohost store, not the
  log length.
- **The images are large.** jal-01 is 1.7 MiB of code, and the six branch
  tests are 225 to 300 KiB. All are bigger than the 256 KiB TB memory, and
  the memory wraps addresses around its size, so an image that is too big
  overwrites its own start with no error. The TB tops take `MEM_WORDS`
  (default 64 Ki words; the arch test sets 512 Ki).
- **Load over VPI, not the clocked backdoor port.** The port writes one
  word per cycle, and jal-01 has 440 Ki non-zero words. `poke` writes
  `dut.mem[i]` directly (cocotb's Verilator build is `--public-flat-rw`).
  Between tests, zero the words the last test could have left set: its
  non-zero image words plus every writable word.
- **Read the signature from memory, not from RVFI.** The signature is what
  is in memory after the halt. Rebuilding it from the stores RVFI reports
  would pass a core whose store port is wrong but whose RVFI is right.
- **Check the check.** One planted bug: kestrel's SH strobe changed to
  `4'b0001`. That failed sh-align-01 alone, 71 of 73 words, and the other
  38 tests stayed green.
  The reference agreement was checked the same way: a wrapper that
  overwrote one word of Sail's signature stopped add-01's build with "the
  references disagree (first at word 4)".

## Related

- [[formal]]: riscv-formal is the other half of ISA compliance. It checks
  every instruction's effect at retirement, symbolically. The arch test
  checks results over concrete programs.
- [[running-regressions]]: the `test_*_arch.py` files run inside each
  core's normal `make clean-all && make run-all-*` suite.
