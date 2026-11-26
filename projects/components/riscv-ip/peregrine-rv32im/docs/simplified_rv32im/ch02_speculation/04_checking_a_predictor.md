# Checking a Predictor

## Passing programs prove recovery, not prediction

A predictor never changes what a program computes, only how long it
takes. A self-checking program and a spike lockstep therefore prove
*recovery* (no wrong-path instruction retires, every redirect lands where
it should). They prove nothing about *prediction*: a predictor that
always guesses "not taken" passes them, slowly.

## Report the guess at retire

peregrine carries each instruction's guess down the pipe and reports it
at retire beside RVFI: `rvfi_bp_pred_taken`, `rvfi_bp_pred_target` and
`rvfi_bp_mispredict`. The test bench replays the retired stream through a
predictor model and checks every beat:

- the mispredict flag equals "guess differs from the resolved outcome";
- the guess equals one the model gives under a predictor state that the
  pipeline timing allows.

The second check has to allow more than one state, because the predictor
is written in EX but read in IF, two stages earlier. An instruction was
predicted from every update by instructions at least three older; from
the one two older only if IF was held while it left EX; and from the one
immediately older only if that one redirected the fetch.

The BHT counters carry over a core reset (they have no reset), so the
model holds each counter as the set of values it can have and narrows the
set as updates saturate it.

## Each write rule needed its own stream

The general streams (loops, aliasing, JALR targets, generated programs)
missed write-rule mutants until a stream was written for each:

| Mutant | Why the general streams missed it | The stream that catches it |
|--------|-----------------------------------|----------------------------|
| Predictor written during `mem_wait` | Only the generated programs ran under `mem_wait`, and their branches run once | `loop_trip3`, `interlock` and `trap_shadow` re-run under random `mem_wait` |
| Predictor written by an instruction a trap kills in EX | Invisible once the counter saturates | `trap_shadow`, with a T, T, N, N direction pattern |
| Redirect issued while an M instruction holds EX | Needs a stale taken guess on an M instruction | `stale_entry`: a jump rewritten into a `mul` |

: Write-rule mutants and the streams written for them (TASK-001 stage 3)

The `trap_shadow` row has a twist. The first version alternated
direction and caught the mutant while installs wrote `10`. Once installs
wrote `01`, both counters re-converged at `00` on every not-taken pass and
the mutant survived. A pattern that repeats a direction while the
counter is still moving catches it under either value: rerun the
mutants after any change to the design they measure.

Formal checks the same rule from the other side (Chapter 6): one update
per retire, in order, with the real outcome.
