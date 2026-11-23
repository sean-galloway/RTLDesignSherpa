---
title: Checking precise traps and interrupts
summary: How to prove a core's traps are precise. A self-checking program cannot see a squashed store that still wrote, so count memory requests against retired accesses. Vary the interrupt delay or it always lands on one instruction. Register the TB's interrupt source, and sample after the drive settles. Lockstep against an M-only spike.
---

# Checking precise traps and interrupts

A trap is precise when every instruction older than the trapping one has
committed and nothing younger has touched architectural state. The
batteries (riscv-tests, riscv-arch-test) check the first half well: wrong
results change the control flow, and the test fails. They hardly check the
second half. Everything below was learned on peregrine (riscv-ip
peregrine-rv32im TASK-001 stage 1, 2026-11-23).

## Count side effects; the program cannot see them

**A self-checking program does not notice a store that was squashed but
still wrote.** The interrupt is taken, and the store re-executes after
`mret` with the same data. Writing the same value twice is idempotent.

- **Failure:** a mutant that let an interrupted store reach memory
  (`~mem_irq` dropped from the data-port gate) passed the interrupt test,
  130 interrupts and every sum exact.
- **Check:** the TB counts every data-memory request and compares it with
  the retired beats that report a memory access (`rvfi_mem_rmask` or
  `rvfi_mem_wmask`). The two must be equal: an instruction that trapped,
  or was interrupted or flushed, issues none.
  - The interrupt mutant now fails with 796 requests against 773 retired.
  - The exception mutant (a misaligned store still writing) fails six
    rv32mi tests and `ma_data` with exact counts.
- The check costs nothing and runs on every battery image, not only on the
  interrupt test (`PeregrineTB.check_mem_side_effects`).

## Vary the interrupt delay

**An interrupt source with a fixed period, against a handler of fixed
length, lands on the same instruction every time.**

- **Failure:** with a 23-cycle re-raise, all 130 timer interrupts hit the
  same phase of the loop, never a load or a store. That is why the side
  effect mutant above survived the first time, even after the count check
  existed.
- **Check:** a seeded random delay (11 to 37 cycles) spreads the landing
  points.
  - The test counts the interrupts that landed on a load or store and
    asserts a floor (four).
  - A run reports, for example, "124 taken, 18 on a load/store". A count
    that falls to zero is a test that has stopped testing.

## The TB interrupt source must be registered

**An interrupt pin that rises in the same cycle as the store that asked
for it interrupts that store.**

- **Failure:** the stub saw `sw t0, irq_ctrl` in MEM and raised MTIP at
  once. The pin reaches the commit decision combinationally, so the core
  took the interrupt on that store and suppressed its write. After `mret`
  the store re-executed and raised the pin again: an endless loop.
- **Fix:** a real CLINT changes its outputs at a clock edge, so the stub
  does too. It observes a cycle and drives the pins from the next falling
  edge.

## Drive, then sample after the drive settles

**In cocotb, reading a signal right after writing an input returns the
pre-write value.**

- **Failure:** the loop set `mem_wait` at the falling edge and read
  `dmem_req` in the same step. It counted 12 requests that `mem_wait`
  had in fact suppressed, and the side-effect check fired on clean RTL.
- **Fix:**
  1. At the falling edge, drive the pins and `mem_wait`.
  2. `await ReadOnly()`.
  3. Sample RVFI and the data port. Those values are what the memory sees
     at the next rising edge.
  4. Step to the next falling edge before returning, because the caller
     may write.

## Lockstep against an M-only spike

The pinned spike 1.1.0 is built without the commit log. `-l` still
prints:
- `core 0: 0x<pc> (0x<insn>)` for every executed instruction, trapping or
  not;
- `exception <kind>, epc <pc>` and `tval` for every trap.

That is enough to lock the (pc, insn) stream and every trap's kind, epc
and tval against the RVFI trace. Rules for using it:

- **Pass `--priv=m`.** Without it spike has S and U modes, and the
  riscv-tests take other paths: `trap_supervisor_ecall`, `interrupt #1`.
- **Spike has 16 PMP regions, and 1.1.0 has no option to change that.** A
  core without PMP must still implement the PMP CSRs as read-only zero:
  the privileged spec makes every field WARL. It must not make them
  illegal. The p-env writes `pmpaddr0` and `pmpcfg0` unconditionally.
  peregrine trapped there in every test until the CSRs existed.
  `rv32mi-p-pmpaddr`, which reads a region back, is then an honest
  exclusion.
- **Spike's exit code is `tohost >> 1`, truncated to 8 bits.** An expected
  failure at TESTNUM 668 (`rv32ui-p-ma_data`: misaligned loads trap on
  RV32I, in spike too) exits 156.
- **The riscv-tests ELFs carry everything.** Loading the PT_LOAD segments
  straight from the ELF needs no pre-built hex. The vendor tree had hex
  images only for rv32ui.

## Hand-written test programs: link with `--no-relax`

The riscv-tests convention keeps the test number in `gp`. Linker
relaxation rewrites `la` into `gp`-relative addressing, which silently
points every such load at the wrong address: peregrine's interrupt test
took no interrupts at all. This is the same flag as the arch-test build
([[riscv-arch-test]]), for a different reason.

## Related

- [[riscv-arch-test]]: the golden-signature suite on the falcon cores.
- [[formal]]: targeted properties for exception precision come next on
  peregrine.
- [[seeds-and-determinism]]: the interrupt delay takes `RDS_SEED_BASE`, so
  a failing landing pattern replays.
