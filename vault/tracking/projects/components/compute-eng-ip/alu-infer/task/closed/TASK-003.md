# TASK-003: const/bias row (emit immediate as a result line)

**Priority:** P3
**Status:** closed -- 2026-10-20
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

## Closed 2026-10-20

OP_CONST (11): threshold_imm broadcast into every lane, in every format. Test `const`.

Verified: gate (82 cells) and func (184 cells, COVERAGE=1) through the area Makefile, four build configs (default, deep, flat, lean); testplan 25/25 scenarios VERIFIED (--strict). MAS 0.50 reconciled. Sequenced ahead of FPGA bring-up at the owner's request ("implement all of the features in the ALU-infer MAS AND PRD", 2026-10-20).
