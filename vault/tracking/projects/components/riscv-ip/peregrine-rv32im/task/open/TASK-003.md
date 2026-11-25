# TASK-003: the peregrine book and predictor drill mode 3 (PRD §7 deliverable 5)

**Priority:** P3
**Status:** open (filed 2026-11-25)
**Owner:** TBD

## What

The book *Simplified RV32IM: peregrine -- speculation and traps* ([PRD](../../../../../../../../projects/components/riscv-ip/peregrine-rv32im/PRD.md) §7
item 5), and predictor drill mode 3 in `core_drills`. Starts after
TASK-002, whose MAS chapters it builds on. The book carries the
measurements TASK-001 recorded (the `BP_EN` A/B, the M-unit CPI contrast
of `MUL_DSP`, amber's hit latency, the stage-7 response-path options), and
the COD alignment gaps the PRD assigns to it (G8).

## Done when

- The book builds through the house pipeline at rev 0.1.
- Drill mode 3 runs against the predictor model used by the TB.
