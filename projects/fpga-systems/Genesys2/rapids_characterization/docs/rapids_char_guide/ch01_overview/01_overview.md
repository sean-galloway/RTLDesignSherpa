# Overview

## What it characterizes

This project performs on-silicon characterization of the **split RAPIDS beats
DMA** (`rapids_beats_top`) — refactored into two wholly-separate engines behind
one shared APB decode:

- `rapids_src_beats` — read-only: memory → AXIS network
- `rapids_snk_beats` — write-only: AXIS network → memory

The harness drives both data paths on real hardware over UART and validates
every beat against a deterministic golden CRC-32. It reports per-direction
throughput and channel scaling, with an all-on-chip stimulus/checker so the
board runs at line rate without a host bottleneck.

There is a single flow, `flows-rapids-beats/` (the "beats" fixed-quantum variant
of RAPIDS).

## Boards and tools

| Item | Detail |
|------|--------|
| Default board | Digilent Nexys A7-100T (`xc7a100tcsg324-1`), 100 MHz, `NUM_CHANNELS = 4` |
| Optional board | Genesys 2 (`xc7k325tffg900-2`) via `BOARD=genesys2`, 8 channels (200→100 MHz MMCM) |
| Build | Vivado (synth / impl / bitgen / program) |
| Host | Python 3 + `pyserial` |
| Sim | Verilator + cocotb / cocotb_test / pytest |

: Boards and tool requirements

## Datapath geometry

| Parameter | Value |
|-----------|-------|
| Data width | 512 bits (64 B/beat) |
| Address width | 64 bits |
| Descriptor | fixed 256-bit |
| Peak per direction | 6.4 GB/s (64 B × 100 MHz) |
| Peak full-duplex | 12.8 GB/s |

: Datapath geometry

## Status

Silicon-validated: `make smoke` passes both paths; `make suite` passes 48/48
(channels {1,2,4} × beats {1,4,8,16} × backpressure {off,on} × 2 seeds). Timing
closes at 100 MHz (WNS +0.007 ns, 0 failing endpoints) at the board-fit geometry
`NUM_CHANNELS = 4`, `SRAM_DEPTH = 256`. On Genesys 2 the 8-channel build reaches
99.8–100% line rate (6.40 GB/s per direction) — see `reports/perf/`.
