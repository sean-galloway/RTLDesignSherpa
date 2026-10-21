# TASK-010: Make the accumulate row close at a real FPGA clock

**Priority:** P2
**Status:** open -- 2026-10-20
**Owner:** sean galloway

## Why

The first synthesis of alu-infer anywhere (Nexys A7-100T, xc7a100t-1, full
profile, harness slot `MUL_LATENCY = MAC_LATENCY = 0`) failed post-route at
50 MHz by **-128 ns**: one 148 ns, 222-level path from the harness command
RAM (`r_cmd`, LUT RAM) through the accumulate row's fp32 FMA
(`u_acc/gen_lane[0].gen_f32.u_fma32`, its mantissa multiplier tree) into the
pipe's result FIFO (`u_pipe/mb_data`). 510 failing endpoints: 382 in
`u_pipe`, 128 on the accumulator bank itself (`u_acc/acc_bank`).

Two separate causes:

1. **The slot's latencies are zero.** With `MAC_LATENCY = 0` and
   `MUL_LATENCY = 0` nothing registers the operands between the command RAM
   and the multipliers, or the products before the result FIFO. Raising
   them is a harness-slot change (`build-infer/rtl/alu_slot.sv`).
2. **The accumulate loop is one cycle by design** (MAS: one step per clock).
   `acc_bank -> fma32 -> acc_bank` is a full fp32 FMA in one clock, which
   raising `MAC_LATENCY` does not touch, since it only adds stages ahead
   of the loop. This bounds the clock whatever the slot does.

The Nexys A7 bring-up runs the full profile at 4.6875 MHz to prove function;
that says nothing about the clock the ALU can run at.

## What

- Measure the loop alone: rebuild with `MAC_LATENCY = MUL_LATENCY = 4` and
  report the accumulate-loop path (`acc_bank -> acc_bank`) and the bf16
  loop separately.
- Decide the loop architecture (owner call): keep one step per clock and
  interleave N independent accumulator banks over an N-stage FMA, or accept
  a multi-cycle accumulate and stall the issue. Record it in the MAS.
- Feed M8 of TASK-007 (per-row latency table) from the measured numbers.

## Done when

The full profile closes timing at a stated clock on the Genesys 2 and the
Nexys A7, with the accumulate-loop decision written into the MAS.
