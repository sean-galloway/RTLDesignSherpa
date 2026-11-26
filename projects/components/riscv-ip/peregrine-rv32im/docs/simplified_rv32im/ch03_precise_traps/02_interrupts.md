# Interrupts

## Sampled at MEM

An interrupt has no instruction of its own, so it attaches to one: a
pending, enabled interrupt attaches to the valid instruction entering
MEM. That instruction does not execute; `mepc` is its PC, and after
`mret` it runs from the start. The interrupt is precise at the oldest
uncommitted instruction, the same point as an exception, so one commit
mechanism serves both. If an instruction carries an exception and an
interrupt arrives, the interrupt wins; the exception is raised again when
the instruction re-executes.

The sources are a CLINT in the SiFive layout (`msip`, `mtimecmp`,
`mtime`) for software and timer interrupts, and an external line (PRD P7).

## The livelock that made M instructions uninterruptible

The first M-unit build let an interrupt attach to an M instruction in MEM
like any other. That discards the instruction, and with it up to 33
cycles of finished multiply or divide work. The directed interrupt test
then ran a timer that re-raised 3 to 40 cycles after each acknowledge.
Each re-raise caught the next M instruction just before it retired; the
handler returned; the M instruction started again; the timer caught it
again. The program never advanced: a **livelock**, found by the test's
timeout.

The fix: an M instruction is not interruptible. It reaches MEM only with
its result done, and the interrupt is taken on the next instruction. The
boundary falls between the M instruction and its successor, and `mepc` is
the successor's PC, so it is still precise.

| | Interruptible M instruction | Uninterruptible (built) |
|-|-----------------------------|-------------------------|
| Precise | Yes | Yes |
| Forward progress under a fast timer | No: livelock | Yes |
| Worst interrupt latency | Lower | About 34 cycles more per back-to-back M instruction |

: The trade (TASK-001 stage 2, ISSUE-001)

The owner kept the simple solution ("do the simple solution first; we can
reevaluate later") and the latency question is open as
riscv-ip/peregrine-rv32im ISSUE-001. The general lesson is a handbook
rule: an interrupt must not discard work that is already finished.

## Two more rules

- **Nothing commits during a hold.** A trap is gated by `~mem_wait`; an
  interrupt pending during a cache miss is taken when the access
  completes.
- **A presented access is not interruptible as its hold drops** (cached
  build). A load or store that has shown its request to the cache, which
  has not yet accepted it, must not be withdrawn: the valid/ready rule
  forbids it. A lock bit makes the instruction uninterruptible on the
  cycle the hold drops. A test aimed the timer at exactly that cycle;
  without the lock, 161 requests were dropped (TASK-001 stage 4).
