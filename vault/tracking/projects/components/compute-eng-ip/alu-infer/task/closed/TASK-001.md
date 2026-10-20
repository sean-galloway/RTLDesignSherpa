# TASK-001: Line-reduce row (sum/max tree into the fp32 accumulator)

**Priority:** P2
**Status:** closed -- 2026-10-20
**Owner:** sean galloway

## Why

Owner ruling 2026-10-19 (architecture review): the v1 function set (copy,
add, sub, mul, mac, min/max, compare/threshold, relu) is the correct minimal
inference core, but real networks also need reductions *across lines/lanes* —
softmax (max-reduce, sum-reduce), layernorm (sum-reduce), pooling (max).
Elementwise min/max between two lines does not cover this.

## What

Add a reduce row to the alu-infer function table (PRD v0.50 §3 roadmap,
2026-10-19 addendum): tree-reduce a span of input lines (sum or max, sub-op
selects) into the per-lane fp32 accumulator, presenting one result line at
the end. Keeps the elastic valid/ready seam and the uniform-presentation
contract; deep tree rows are exactly the case the tag/same-tag alignment
(TASK-006) exists for.

## Done when

Row is in the alu-infer MAS function table and RTL, func+gate green, and a
softmax-shaped sequence (max-reduce, sub, exp via TASK-002, sum-reduce,
reciprocal-multiply) runs in the cell DV environment.

## Notes

Sequenced after FPGA bring-up of the v1 rows (owner: "We will see what we
can do with the latency once the ALU is on the fpga").

## Closed 2026-10-20

REDUCE (opcode 8): sum/max over a span of lines into the accumulator bank in every format; CLEAR loads the identity (+0 / -inf / INT32_MIN); sub_op[1] presents the cross-lane fold broadcast. Tests `reduce` (all four formats) and `softmax` (REDUCE max+fold, SUB, PWL exp, REDUCE sum+fold, RECIP, MUL: worst element error 1.6e-3 vs float softmax). The cell DV environment does not instantiate the ALU yet, so the softmax sequence runs in the alu-infer DV, driven through the same seam.

Verified: gate (82 cells) and func (184 cells, COVERAGE=1) through the area Makefile, four build configs (default, deep, flat, lean); testplan 25/25 scenarios VERIFIED (--strict). MAS 0.50 reconciled. Sequenced ahead of FPGA bring-up at the owner's request ("implement all of the features in the ALU-infer MAS AND PRD", 2026-10-20).
