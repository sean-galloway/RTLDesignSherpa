# What Prediction Buys

## The A/B

`BP_EN=0` builds no predictor storage and never predicts taken, which is
merlin's behaviour: every taken transfer costs 2. The predictor test runs
every stream on both builds and reports the speedup of `BP_EN=1`.

| Stream | What it stresses | Speedup |
|--------|------------------|---------|
| `loop_trip1` | Inner loop of 1 iteration | 1.32 |
| `loop_trip2` | 2 iterations | 1.18 |
| `loop_trip3` | 3 iterations | 1.28 |
| `loop_trip4` | 4 iterations | 1.35 |
| `bht_alias` | Two branches sharing one counter, opposite directions | 1.81 |
| `btb_alias` | Two branches sharing one BTB entry | 1.33 |
| `jalr_targets` | Indirect call cycling three targets; return alternating | 1.33 |
| `interlock` | Alternating branch with interlocks on the wrong path | 1.04 |
| `trap_shadow` | A branch directly after an `ecall` | 1.05 |
| Generated programs | Branches that mostly execute once | 1.005 |

: BP_EN=1 against BP_EN=0, full level (TASK-001 stage 3)

## Reading the table

- **Loops win most where the back edge is taken most.** A 2-iteration
  loop is taken once and not taken once per pass, the worst case for a
  2-bit counter, and it gains least.
- **Aliasing streams still win**, because the alternative (no
  prediction) pays 2 on every taken transfer anyway. `bht_alias`'s 1.81
  is a property of the stream's shape, not of aliasing being free.
- **Branches that run once gain nothing.** A predictor learns from
  history; the generated programs have almost none, so 1.005.
- **`interlock` gains little by design**: it alternates direction, so
  it mispredicts often, and puts an ID interlock on the wrong path to
  check that recovery is still correct.

## What a mispredict costs in time

Two bubbles at the core clock. At the 13.333 ns period (Chapter 5) that
is 27 ns per mispredict.
