---
title: Checking a branch predictor from the retire stream
summary: A predictor only changes timing, so lockstep and self-checking programs prove recovery, not prediction. Report each instruction's guess at retire and hold it to a model under the states pipeline timing allows; model unreset counters as value sets; give every aliasing stream its own table region; write a stream for each mutant the general ones cannot see (peregrine TASK-001 stage 3, 2026-11-24).
---

# Checking a branch predictor from the retire stream

A predictor never changes what a program computes, only how long it takes.
A self-checking program and a spike lockstep therefore prove **recovery**
(no wrong-path instruction retires, every redirect lands where it should).
They prove nothing about **prediction**: a predictor that always guesses
"not taken" passes them, slowly. Counting mispredicts is better but still
weak, because a count can be right for the wrong reasons. Everything below
was learned on peregrine (riscv-ip peregrine-rv32im TASK-001 stage 3).

## Report the guess at retire, and hold every one to a model

The core carries each instruction's prediction (taken, target) and its
mispredict flag down the pipeline and reports them at retire beside RVFI
(`rvfi_bp_pred_taken`, `rvfi_bp_pred_target`, `rvfi_bp_mispredict`). The
TB replays the retired stream through a predictor model and checks every
beat:

- the flag equals "guess != resolved outcome" (direction, or target on a
  taken guess);
- the guess equals one the model gives under a state the pipeline timing
  allows.

**The allowed states.** The core writes the predictor once per instruction
as it leaves EX, in program order, but looks it up in IF, two stages
earlier. So an instruction was predicted from:

- every update from instructions at least three older;
- plus the update from the one two older, only if IF was held while that
  one left EX (an interlock, the M unit);
- never the update from the one immediately older, unless that one
  redirected the fetch (a mispredict, a trap, an `mret`): then the
  instruction was fetched after it resolved.

That needs the write rule to be exact: once per instruction, not under
`mem_wait`, not during an EX hold, and not for an instruction a trap kills
in EX. A predictor written any other way cannot be checked this way, and
two of the mutants below are exactly those write rules.

## Model unreset counters as sets of values

**Failure:** the first core-level run failed on `loop_trip2` with "predicted
taken, model allows only not taken". The RTL was right. The BHT is LUTRAM
with no reset, so its counters carry over a core reset, and `loop_trip1` had
trained the counter at that very PC. A model that starts every counter at
zero is wrong after the first program in a simulation.

**Fix:** hold each counter as the set of values it can have: {0, 1, 2, 3}
after a reset, narrowing as same-direction updates saturate it. A
prediction passes if any allowed state and any counter value give it. The
unit test, which runs once from power-up, keeps exact counters and asserts
that no conditional BTB hit ever reads a counter no update wrote, which is
the invariant that lets the RTL skip the reset.

## Randomize unreset memories, or 2-state simulation hides X

**Failure:** the first predictor stepped a BHT counter from its old value
when it installed a conditional BTB entry, and that old value can be one
nothing ever wrote. Verilator is 2-state and zero-initializes, so every
test passed; the independent RTL review found it by reading. In a 4-state
simulator the counter becomes X and the next lookup drives X onto the
fetch address. On the board it is whatever an earlier program left.

**Check:** build the unit test with `--x-initial unique` and run with
`+verilator+rand+reset+2 +verilator+seed+<SEED>`, so every unreset memory
starts random. The old RTL then failed on every func seed tried (11, 22,
33: "RTL True, model False"). One gate seed passed: a 3,000-cycle run
looks up few such counters, and a random high bit can agree with the
model. The fix (an install writes a fixed value) passes the same seeds.
An "unwritten state is never read" argument needs a test that would fail
if it were false.

**And measure the value the fix writes.** Weakly taken (`10`) was the
obvious install value and passed every correctness check, but the A/B
caught it: an alternating branch then mispredicts every outcome, and
`loop_trip2` and `interlock` fell below predict-not-taken (0.998x, 0.982x).
Weakly not taken (`01`) is a zeroed counter after one taken step, so it
also reproduces the board's power-up behaviour, and both streams win
again. A fix to a correctness finding can still be a performance
regression; keep the A/B in the same run as the model check.

## Give every aliasing stream its own table region

**Failure:** `bht_alias` (an always-taken and a never-taken branch sharing
one counter) showed 9 mispredicts over 40 passes, where the interference it
is named for should cost about one per pass. Its counter shared an index
with `btb_alias`'s always-taken branch, which ran first and left the counter
saturated high. The model passed it, correctly; the stream had simply
stopped demonstrating anything.

**Fix:** place each aliasing pair at table indexes no other stream uses
(`bht_alias` moved to BHT index 128) and check the alias property from the
linked symbols, so a layout change cannot quietly break the pair. The
same stream then shows 48 mispredicts.

## Write the stream the mutant needs

The general streams (loops, aliasing, JALR targets, generated hazard
programs) missed two of the eight mutants until a stream was written for
each:

- **A redirect issued while an M instruction holds in EX** kills it in
  ID/EX, because flush beats stall. It needs a stale taken prediction on an
  M instruction: `stale_entry` rewrites a jump into a `mul` whose result
  feeds the check.
- **A predictor update from an instruction a trap kills in EX** is
  invisible once the counter saturates. `trap_shadow` puts a branch
  directly after an `ecall`, so the killed copy doubles a counter step
  that is still moving. **The direction pattern matters.** The killed
  copy's update lands just before the re-executed copy is looked up, so
  the checked prediction already includes the extra step. With a strictly
  alternating branch, both counters re-converge at 00 on every not-taken
  pass. The alternating version caught the mutant while installs wrote
  `10`, and let it through once they wrote `01`. A T, T, N, N pattern
  (the same direction repeating while the counter moves) catches it under
  either value. Rerun the mutants after any change to the design they
  measure.
- **A predictor written every cycle `mem_wait` holds EX** survived the
  first mutation pass. The only `mem_wait` run was the generated program,
  whose branches mostly execute once at distinct PCs. A repeated BTB write
  is idempotent, and a counter nobody looks up again cannot show extra
  steps. Re-running `loop_trip3`, `interlock` and `trap_shadow` under random
  `mem_wait` caught it at once (`loop_trip3+mem_wait`, beat 164). Hold a
  write rule to a stream where the write is visible: a re-executed branch
  whose counter is still moving.

## Smaller traps

- **Name registers by ABI name in generated assembly.** `x6`, `x7` and `x8`
  are `t1`, `t2` and `s0`; the first `interlock` stream overwrote its own
  loop toggle and accumulator. Run a failing program on spike before
  suspecting the core: spike failed it too.
- **Self-modifying code needs `fence.i` for spike** even on a cacheless
  core. `stale_entry` with the `fence.i` removed fails on spike 1.1.0 (it
  keeps executing the old jump, so the result check fails), and passes
  with it. Without `fence.i` the architecture does not promise the new
  instruction anyway.

## Related

- [[precise-trap-checks]]: the trap and interrupt counterpart, including
  the RVFI shadow-regfile check these programs also run.
- [[riscv-arch-test]]: golden signatures, which cannot see a predictor.
