# Honest Limits

## What the board evidence does not cover

- The soak is scheduled but not complete at publication time; Chapter 4
  contains no soak numbers.
- The soak, once complete, will be statistical, not exhaustive. One million
  blocks is large, but it will not visit every possible error pattern.
- The erasure `f = 2t` boundary is an open issue (TASK-005). f = t corrects
  and f = 2t+1 refuses on the board; f = 2t is flagged uncorrectable even
  though the design intent says it should correct.
- The dual-decoder comparator with `ENABLE_COMPARE=1` is sim-only on the board
  matrix. Solver agreement on the board is proven by running identical
  deterministic campaigns on the single-decoder images.
- BCH has no erasure path by design; that comparison is RS-only.
- The board validates only the RS(252,236) t=8, S=4 profile. Other profiles
  are covered in simulation and component DV.
- The component DV matrix exercises the codec in ways the board harness does
  not replicate.

## Traceability

Every quantitative claim in this book can be traced to an artifact under
`stable/`:

| Claim | Artifact |
|-------|----------|
| Four images timing-clean at 100 MHz | `stable/reports/genesys2_{axis_ribm,axis_euclid,axi4_ribm,axi4_euclid}/timing_summary.txt`, all WNS positive, 0 failing endpoints. |
| 7/7 campaigns PASS on all images | `stable/results/2026-10-05_battery/battery.json` and `FINDINGS.md`. |
| e <= 8 corrected, e > 8 uncorrectable | `stable/results/2026-10-05_battery/battery.json`, `sweep` array. |
| Solver agreement matrix all green | `stable/results/2026-10-05_battery/fig_5_solver_agreement.png`. |
| f = 2t erasure boundary open | `vault/Tasks/projects/components/ecc-ip/reed-solomon/task/open/TASK-005.md`. |

: Table 5.1: Traceability from claim to artifact.
