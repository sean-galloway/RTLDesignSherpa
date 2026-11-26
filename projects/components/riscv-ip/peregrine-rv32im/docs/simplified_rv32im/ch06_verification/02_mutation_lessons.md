# Mutation Lessons

A mutant is a deliberate bug. Each stage of peregrine ended with a
mutation pass: break one thing, rebuild from clean, and check that a test
fails for the right reason. A mutant that survives is either equivalent
(it changes nothing observable) or a hole in the tests.

| Stage | Mutants | Caught | Survivors, and what they taught |
|-------|---------|--------|---------------------------------|
| 2, M unit | 8 | 8 | Not cancelling the unit on a redirect was caught only after the `ecall` handler changed the operand: re-executing with the same operands hides it |
| 3, predictor | 9 | 9 | Three needed their own streams (Section 2.4) |
| 4, caches | 18 | 17 | The survivor is equivalent: amber cannot accept a clean while an access is in flight |
| 7, timing | 27 | 26 | The early-response bugs survived until the response data was scrambled (Section 6.1) |
| 5, formal (targeted) | 18 | 18 | The JALR `+1` mutant is invisible to riscv-formal (a spurious mispredict redirects to the right place) and caught by the mispredict-flag property |

: Mutation passes (TASK-001 stages 2 to 7)

## The pattern

Every surviving non-equivalent mutant had the same shape: **the bug's
effect was real, but nothing looked at the place it showed.** A
predictor written twice is invisible once the counter saturates. A late
read is invisible while the data holds. A redirect to the right place
through the wrong path is invisible to an architectural check. The fix
was never a bigger test. It was a check aimed at that place.
