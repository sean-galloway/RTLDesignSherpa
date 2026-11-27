# TASK-003: Build cell_mem_in / cell_mem_out as distributed RAM

**Priority:** P2
**Status:** open -- 2026-11-26
**Owner:** sean galloway

## Why

Measured 2026-11-26 in the gatling tetrad OOC build (gatling-rv32i TASK-002): `gatling_tetrad`, four cells, alu-infer with every `ALU_EN_*` = 0 (bf16 rows, MAC, ADD, RELU, CMP), xc7a100t-1, 10 ns, routed. Vivado optimized ALU logic across the hierarchy and booked it to `u_xcell` (25,501 LUT there against 383 LUT for `gatling_xcell` built alone); grouping every LUT in `u_xcell` by the net it drives puts it back where it belongs. Per cell the ALU is about 8.7k LUT, not the 1.8k the hierarchy report shows.

`cell_mem_in` and `cell_mem_out` are **1,062 FF and ~297 LUT each** for a
32 x 32 memory (four cells: 8,496 FF, ~2,400 LUT). Their arrays are written
inside the async-reset block, so Vivado must build them as flops plus a 32:1
read mux. Written in a clock-only `always_ff`, each is 32 LUTRAM (one
RAM32M-class primitive per 6 bits of width) and a few flops for the
registered read.

Same failure as pumice's CAM and the bridge generator FIFOs (handbook: reset
blocks array inference).

## What

- Move the array writes to a clock-only `always_ff`; keep reset on the
  pointers, occupancy and read-valid only.
- Check the registered-read timing contract is unchanged (gatling's issue
  stager depends on it: one registered read port, data the cycle after).

## Done when

Both memories map to LUTRAM in the tetrad OOC build, cell DV and the
gatling-rv32i suite green from clean-all.
