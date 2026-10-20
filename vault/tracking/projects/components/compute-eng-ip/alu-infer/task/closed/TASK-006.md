# TASK-006: tag/same-tag alignment in RTL (replaces the timer mailbox)

**Priority:** P2
**Status:** CLOSED 2026-10-20
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

---

## CLOSED 2026-10-20

Implemented in `cell/rtl/`: `alu_infer_pipe` is now the tag FIFO with an
arrival join — a free-running 8-bit tag counter at issue (`TAG_W = 8`),
`PIPE_DEPTH` entries (default 8, [2,16]) tracked in issue order, and a
result offered only when every op of its tag group has arrived. The
combinational rows land at the issue edge; the pipelined add/sub row
carries the tag through its own `ADDER_LATENCY`-deep (default 3, [0,4])
shift register and re-joins its entry **by tag compare, not position**.
`ROW_LATENCY` is gone (superseded; MAS records it). A stalled consumer no
longer blocks issue until the FIFO is genuinely full — the old
`advance`-gated `ready` was removed with the timers.

Mixed-depth demonstration without a dummy row: new test 13
(`cocotb_test_alu_infer_tag_join`) pins exact natural latencies
(comb rows offered the cycle after issue; add at `ADDER_LATENCY`) and
shows an add issued ahead of a relu and a copy presenting first — the
fast rows wait at the FIFO head. Test 8 gained the FIFO-fill case
(`ready` falls only at `PIPE_DEPTH` in flight). Group-of-1 is v1's
degenerate case; the multi-op group join is the growth path the ruling
targeted.

| Check | Result |
|---|---|
| `test_alu_infer.py` gate, PIPE_DEPTH {4,8} | 13/13 × 2 PASS |
| `test_alu_infer.py` func, PIPE_DEPTH {4,8} | 13/13 × 2 PASS (8 seeds × 256-op soak) |
| cell area `run-all-gate-parallel` | 3/3 PASS |
| verilator lint on `alu_infer_top.f` | clean |
| MAS 0.50 | tag mechanism documented as as-built; PDF + 2 block diagrams + 3 waveforms regenerated |
