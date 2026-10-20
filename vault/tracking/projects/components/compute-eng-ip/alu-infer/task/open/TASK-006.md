# TASK-006: tag/same-tag alignment in RTL (replaces the timer mailbox)

**Priority:** P2
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

Ratified 2026-10-17 (owner): "when loading a new function into the ALU
pipeline an 8-bit tag is assigned common to all ops that must happen in
parallel; a FIFO tracks that; valid for each op only asserts when all of the
valids using that tag are ready." This is the alignment architecture for
uneven pipeline depths — and it is still not in the RTL. The as-built v1
uses the alignment-timer mailbox in `cell/rtl/alu_infer_pipe.sv`, which is
correct only while every row presents at the uniform ROW_LATENCY.

## What

Implement the tag mechanism in the alu-infer RTL (home: alu-infer MAS +
`cell/rtl/`): 8-bit tag assigned per invocation group at issue, tag FIFO
tracking in-flight groups, align gate so an op's `result_valid` asserts only
when every op of its tag group is ready. Tags stay inside the ALU block; the
FSM seam (two valid/ready pairs) is unchanged. This is the enabling work for
the deep rows: reduce (TASK-001), PWL (TASK-002), and per-format depth
divergence (TASK-004/005).

## Done when

Tag logic is in the RTL, func+gate green; a mixed-depth row set (add a
deep dummy row if needed) demonstrates group-aligned retirement; the MAS
"ratified, not yet in RTL" wording moves to implemented.

## Notes

Blocks the row/format roadmap items if their latencies diverge; not needed
for the uniform-latency v1 set. Cell MAS v0.12 ch04 records the contract.
