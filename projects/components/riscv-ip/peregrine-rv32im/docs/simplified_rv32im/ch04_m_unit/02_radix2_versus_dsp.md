# Radix-2 versus a DSP Multiply

## The iterative unit

The unit is radix-2 for both operations (PRD P8; COD §3.3 and §3.4):

- **Multiply:** shift-add, one bit of the multiplier per step.
- **Divide:** restoring division, one quotient bit per step.
- A start cycle captures the operand magnitudes; 32 steps follow; the
  sign is fixed up on the registered result. The high word of a negated
  product is `~hi + (lo == 0)`.
- **Early out:** divide by zero and -2^31 / -1 finish in the start cycle,
  with the results the M extension defines (quotient all ones and
  remainder the dividend for a zero divisor; -2^31 and 0 for the
  overflow case). RISC-V does not trap on either.

The unit is a busy bit, a done bit and a 5-bit step count: no encoded
state machine.

| Case | Stall cycles |
|------|--------------|
| Multiply or divide, iterative | 33 |
| Divide by zero, -2^31 / -1 | 1 |
| Multiply, `MUL_DSP=1` | 2 |

: M-unit stall cycles (PRD P8)

## The measured contrast

`MUL_DSP=1` replaces the shift-add multiply with one registered product,
which an FPGA maps to DSP blocks. Divides stay iterative.

On one stress program (5,941 instructions, 34% of them M instructions,
the same seed on both builds), the iterative unit took 54,419 cycles (CPI
9.16) and `MUL_DSP=1` took 22,737 (CPI 3.83) (TASK-001 stage 2). That
program is a stress mix, not a benchmark: real code has far fewer M
instructions, and the difference scales with their share.

## The timing worry that did not happen

The stage-2 review flagged the DSP product as a timing risk: it is
combinational between registers that sit behind muxes, so the DSP block
cannot absorb a pipeline register. At the clock peregrine closed at
(18.5 ns, Chapter 5), `MUL_DSP=1` closed with +0.342 ns of slack, better
than the iterative build's +0.100 ns: at that period the multiplier is
not the critical path.
