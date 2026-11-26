# The Install Value

When a taken conditional branch first enters the BTB, its counter has to
start somewhere. The first design stepped the counter from whatever it
held. The final design writes a fixed `01` (weakly not taken). The path
between them is two lessons.

## Lesson 1: an unwritten value is read

The BTB valid bits reset; the BTB payload and the BHT are LUTRAM with no
reset. Stepping the counter on install reads a counter nothing may ever
have written. Verilator is a 2-state simulator and zero-initializes
memories, so every test passed. The independent RTL review found it by
reading: in a 4-state simulator the counter is X, and on the board it is
whatever an earlier program left.

The unit test now builds with randomized initial memory
(`--x-initial unique`, `+verilator+rand+reset+2`). The old RTL then
failed on every func seed tried (11, 22, 33). An argument that "an
unwritten state is never read" needs a test that fails if it is false.

## Lesson 2: the obvious fix lost to no prediction

The fix is to write a fixed value on install. Weakly taken (`10`) is the
obvious choice, since the branch was just taken, and it passed every
correctness check. The A/B against `BP_EN=0` caught it: an alternating
branch then mispredicts on every outcome, and two streams ran slower than
predicting nothing at all.

| Install value | `loop_trip2` vs `BP_EN=0` | `interlock` vs `BP_EN=0` |
|---------------|---------------------------|--------------------------|
| `10` (weakly taken) | 0.998x | 0.982x |
| `01` (weakly not taken) | 1.18x | 1.04x |

: The install value against predict-not-taken (TASK-001 stage 3; the `01` row is the final full-level A/B of Section 2.3)

`01` is what a zeroed counter reaches after one taken step, so it is also
the board's behaviour from power-up. It wins on every stream; the owner
approved it on 2026-11-25. A fix to a correctness finding can still be a
performance regression, which is why the A/B runs in the same test as
the correctness check.

## The 2-bit counter

| State | Meaning | Taken | Not taken |
|-------|---------|-------|-----------|
| `00` | Strongly not taken | `01` | `00` |
| `01` | Weakly not taken (install value) | `10` | `00` |
| `10` | Weakly taken | `11` | `01` |
| `11` | Strongly taken | `11` | `10` |

: Counter transitions (COD Fig 4.65); the prediction is bit 1
