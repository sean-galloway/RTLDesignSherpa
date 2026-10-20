# TASK-003: const/bias row (emit immediate as a result line)

**Priority:** P3
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

Owner ruling 2026-10-19 (architecture review): programs need constant lines
(biases, scale factors) and today the only way to get one is memory traffic.
The compose stage already has the immediate input (`threshold_imm`); a const
row is nearly free and removes a whole class of filler traffic on delta.

## What

Add a const/bias row (PRD v0.50 §3 roadmap, 2026-10-19 addendum): emit the
immediate register (T / threshold_imm) as a result line, both lanes. No
operand lines consumed.

## Done when

Row is in the alu-infer MAS and RTL, func+gate green; a cell program can
materialize a bias line and add it (row 1) without any `mem` packet.

## Notes

Cheapest of the three row additions; natural first candidate when row work
starts after bring-up.
