# TASK-011: Replace the tag-matched result buffer with per-row slots

**Priority:** P2
**Status:** open -- 2026-11-26
**Owner:** sean galloway

## Why

Measured 2026-11-26 in the gatling tetrad OOC build (gatling-rv32i TASK-002): `gatling_tetrad`, four cells, alu-infer with every `ALU_EN_*` = 0 (bf16 rows, MAC, ADD, RELU, CMP), xc7a100t-1, 10 ns, routed. Vivado optimized ALU logic across the hierarchy and booked it to `u_xcell` (25,501 LUT there against 383 LUT for `gatling_xcell` built alone); grouping every LUT in `u_xcell` by the net it drives puts it back where it belongs. Per cell the ALU is about 8.7k LUT, not the 1.8k the hierarchy report shows.

The largest single term is `alu_infer_pipe`'s result buffer, `mb_data` /
`mb_flags`: **15,108 + 320 LUT for four cells, ~3.9k LUT per cell**, for
8 entries x 32 bits. That is ~15 LUT per stored bit.

The shape is the cause, not the size. Every entry can be written by every row
port, chosen by matching the port's tag against every pending entry
(`alu_infer_pipe.sv` row-arrival loop), and the entries are async-reset flops.
So each data bit is an N_PORTS x PIPE_DEPTH priority mux into a flop, with a
tag comparator per (port, entry) pair, and nothing can go to LUTRAM.

## What

- Each row has a fixed latency (TASK-007 M8 records the per-row table), so the
  arrival order per row is known at issue. One FIFO slot per row, or a result
  buffer indexed by the issue tag (written by the one port that owns it),
  removes the CAM.
- Drop the reset on the data arrays; reset only the valid/arrived bits.
- Re-measure in the same tetrad build and the alu-infer harness.

## Done when

The result buffer is under 300 LUT per cell (bf16 profile) in the tetrad OOC
build, alu-infer DV green from clean-all, and the MAS pipe chapter updated.
