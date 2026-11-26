# What peregrine Costs

## Cycles

| Cause | Cost | Chapter |
|-------|------|---------|
| Mispredict | 2 cycles | 2 |
| Correctly predicted taken branch | 0 (merlin paid 2) | 2 |
| Trap, `mret`, `fence.i` | 3 cycles, plus `fence.i`'s clean and invalidate | 3, 5 |
| Load-use | 2 cycles (merlin: 1, or 2 to a branch); no load is forwarded WB to EX | 5 |
| CSR behind CSR | up to 2 cycles | 3 |
| M instruction | 33, 1 (early out) or 2 (`MUL_DSP=1` multiply) | 4 |
| Cache hit | 0 extra (1-cycle amber hit) | 5 |
| Cache miss | The line fill, with the whole core held | 5 |

: Where cycles go

On the stage-7 kernels the measured CPI is 1.429 (without `mm`), and on
the rv32ui images 1.998 (TASK-006, the CPI harness; 1.343 and 1.989
before the second load interlock).

## Area and clock

The 13.333 ns build of `peregrine_top` used 4,810 LUTs, 3,009
flip-flops and 9 block RAM tiles on the xc7a100t-1 (TASK-006,
`MUL_DSP=0`). The target period is 13.333 ns, 75 MHz, the
owner's floor; amber's paths still set the margin (Chapter 5).

## What was left out

| Not built | Why | Where it went |
|-----------|-----|---------------|
| Load and store access faults on bus errors | Not needed for the teaching core; bus errors are ignored | riscv-ip/peregrine-rv32im TASK-005 |
| MonBus observation | Not built; counts come from the RVFI stream in simulation | PRD §4.6 (amended) |
| Interruptible M instructions | Livelock risk; latency cost accepted | ISSUE-001 |
| A return-address stack | Out of scope for a bimodal predictor (P5) | |
| A non-blocking cache | One access in flight; it would be invisible (§2) | |

: Deliberate omissions
