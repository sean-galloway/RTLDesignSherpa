# alu-infer — Task Index

bf16 inference ALU for the compute cell: 2xbf16 lanes per 32-bit line,
fp32-accumulate MAC, valid/ready elastic pipeline, tag/same-tag alignment
(ratified target). Home: `projects/components/compute-eng-ip/alu-infer/`
(PRD v0.50 + MAS v0.50, revs pinned per owner); v1 RTL lives in
`projects/components/compute-eng-ip/cell/rtl/` (alu_infer_top/rows/pipe/acc,
func+gate green 2026-10-17/18).

## Open

| Task | Summary |
|---|---|
| [TASK-001](task/open/TASK-001.md) | Line-reduce row (sum/max tree into the fp32 accumulator) — softmax/layernorm/pooling |
| [TASK-002](task/open/TASK-002.md) | PWL/LUT activation row (sigmoid/tanh/gelu/exp) |
| [TASK-003](task/open/TASK-003.md) | const/bias row (emit immediate as a result line) |
| [TASK-004](task/open/TASK-004.md) | int8 x4-lane element width (func_sel[8:7], open item M6) |
| [TASK-005](task/open/TASK-005.md) | fp32 single-lane element width (func_sel[8:7], open item M6) |
| [TASK-006](task/open/TASK-006.md) | tag/same-tag alignment in RTL (replaces alu_infer_pipe timer mailbox) |
| [TASK-007](task/open/TASK-007.md) | Close M1-M8 numeric-policy open items at FPGA bring-up |

## Closed

(none yet)
