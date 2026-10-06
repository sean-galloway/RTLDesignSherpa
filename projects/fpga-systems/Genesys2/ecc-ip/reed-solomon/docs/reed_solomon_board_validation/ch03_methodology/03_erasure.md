# Erasure Campaign

## What erasure decoding adds

When `INJ_CFG.mark` is set, the injector's hit mask rides the decoder
`in_erasure` sideband. The decoder is then told which symbols were corrupted,
so the correction bound doubles: the decoder can correct e errors plus f
erasures whenever 2e + f <= 2t. For RS(252,236) t=8, that means:

- f = t = 8 erasures alone should correct.
- f = 2t = 16 erasures alone should correct.
- f = 2t + 1 = 17 erasures should be refused by inspection.

## Board findings

The `erasure` sequence was run on the Genesys 2 board:

| f | Expected | Observed |
|---|----------|----------|
| 8 (t) | Correct | Correct: 16/16 blocks corrected, A=B solver agreement. |
| 16 (2t) | Correct | Flagged uncorrectable: `ok/corr/unc = 0/0/16`. |
| 17 (2t+1) | Refuse by inspection | Refused: 16/16 blocks uncorrectable. |

: Table 3.2: Reed-Solomon erasure boundary results.

## TASK-005 boundary

The f = 2t case is the known open issue TASK-005
(`vault/Tasks/projects/components/ecc-ip/reed-solomon/task/open/TASK-005.md`):
the B-stage `t_zero` bypass intends to pass f = 16, but the final verdict
fires downstream. The f = t and f = 2t+1 paths are correct; the f = 2t path
must be fixed in the component DV and then re-run on the board. This report
documents the finding exactly as measured and does not fabricate a corrected
result.
