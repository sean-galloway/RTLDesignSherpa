---
title: Checking precise traps and interrupts
summary: How to prove a core's traps are precise. A self-checking program cannot see a squashed store that still wrote, so count memory requests against retired accesses. Vary the interrupt delay or it always lands on one instruction. Register the TB's interrupt source, and sample after the drive settles. Lockstep against an M-only spike. For a multi-cycle unit, raise interrupts faster than its latency, make the handler change the operands of the instruction it returns to, and check values with an RVFI shadow regfile.
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

## Bus errors: let spike fault on an unmapped address

spike 1.1.0 cannot be told to answer SLVERR, but it raises access faults
on addresses it does not map. peregrine's sys TB answers by address window
(bits 27:24 = 0xE DECERR, 0xD SLVERR), so a program that touches those
windows at addresses spike leaves unmapped (0x1Dxx_xxxx / 0x1Exx_xxxx
uncached, 0x4Dxx_xxxx / 0x4Exx_xxxx cacheable and fetch) takes the same
load, store and instruction access faults in both (TASK-005). Two details:

- **A fetch fault has no commit line** in spike's log, only the exception
  record (its epc is the fetch target). The lockstep matches the core's
  trap beat (insn 0) against that record alone.
- **The request count still holds** if a load or store access fault counts
  as one request: the error IS the request's response. A faulting access
  issued twice, or a younger access accepted under the fault, is extra.
  Put a load or store directly behind each fault, or a port freed by the
  error response goes unseen ([[bus-faults-at-the-response]]).
- A failed write-back is an interrupt with a custom CSR, which spike does
  not have: that program runs without lockstep, its CSR reads held to the
  TB's shadow trap-CSR model (`csr_shadow.py`).

## Hand-written test programs: link with `--no-relax`

The riscv-tests convention keeps the test number in `gp`. Linker
relaxation rewrites `la` into `gp`-relative addressing, which silently
points every such load at the wrong address: peregrine's interrupt test
took no interrupts at all. This is the same flag as the arch-test build
([[riscv-arch-test]]), for a different reason.

## Multi-cycle units (peregrine TASK-001 stage 2, the M unit)

### Raise interrupts faster than the longest instruction

**An interrupt source slower than the unit's latency never asks the
question that matters: what happens when the interrupt beats the unit?**

- **Failure:** the first M-unit build let an interrupt take an M
  instruction in MEM, discarding 33 cycles of work. With the timer
  re-raised 3 to 40 cycles after each acknowledge, the M instruction was
  caught every time and never retired: the run timed out looping in the
  handler. The stage-1 interrupt test (11 to 37 cycles, no long
  instruction) could not have shown it. The design rule is
  [[interrupts-must-not-discard-finished-work]].
- **Check:** the re-raise delay range includes values below the unit's
  latency. Assert that no interrupt beat is an M instruction, and that
  every interrupted PC executes later. An interrupted `ecall` re-executes
  as an `ecall` trap, so count any later beat at that PC that is not
  another interrupt.

### A re-executed instruction hides a stale result

**A trap in the M instruction's first EX cycle kills it, and it
re-executes after `mret` with the same operands, so a unit that kept
running the killed operation returns the right answer by accident.**

- **Failure:** the cancel mutant (the unit not cancelled by a MEM-stage
  redirect) was invisible until the operands changed between the kill and
  the re-execution.
- **Check:** the generated program's `ecall` handler adds 1 to x29, and
  the M instruction after each planted `ecall` reads x29. A stale result
  is then a value mismatch.

### Check values from RVFI itself

Without spike's commit log, the lockstep sees the PC stream only, and a
wrong M result that does not change a branch passes it. The TB keeps a
shadow regfile from RVFI's own `rd` writes. Every retired beat's
`rs1_rdata` and `rs2_rdata` must equal the last value written to that
register, and every M beat's `rd_wdata` must equal the spec model applied
to those values. One check covers forwarding into every consumer and the M
results. It needs RVFI to report the operands the instruction actually
used. peregrine latches the M operands at start, because the forwarding
selects go stale while the M instruction holds in EX.

### A generator's model must cover every value its program can read

**Failure:** the stage-3 regression failed one gate cell with `tohost = 53`
(x26 differs). spike failed the same program the same way, so the core was
right. The `csr_around` shape read `mie` into a register the generator did
not model, and the M instruction after it could pick that register as a
source. The bad value then propagated to x26, which the final compare
checks. Earlier seeds never chose that source. **Run the failing program on
spike before suspecting the core**; then keep any register holding an
unmodelled value out of every source until it is overwritten.

### Link generated programs with `-N` for spike

Without `-N`, ld page-aligns the text segment and folds the ELF headers
into it, so the first PT_LOAD starts at `LINK_BASE - 0x1000`. The TB's
aliasing memory loads it without complaint. spike's RAM begins at
`LINK_BASE`, so it dies with `trap_store_access_fault` while loading the
image (exit 255).

## Related

- [[riscv-arch-test]]: the golden-signature suite on the falcon cores.
- [[formal]]: targeted properties for exception precision come next on
  peregrine.
- [[seeds-and-determinism]]: the interrupt delay takes `RDS_SEED_BASE`, so
  a failing landing pattern replays.
- [[interrupts-must-not-discard-finished-work]]: the forward-progress
  rule the multi-cycle interrupt check found.
