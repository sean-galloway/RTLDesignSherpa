# Overview

## What it characterizes

This project measures the in-house **STREAM scatter-gather DMA** on a Digilent
Nexys A7-100T (Artix-7 `xc7a100tcsg324-1`, 100 MHz), driven entirely over one
USB-UART link, across four axes:

| Axis | Report | Headline |
|------|--------|----------|
| Performance / utilization | `reports/perf/` | 100% datapath utilization across the 40-config matrix (~1525 MB/s, 128-bit datapath) |
| MonBus trace compression | `reports/compression/` | 63.0% (64-bit codec), 75.7% (half-beat 32-bit) reduction |
| Area | `reports/area/` | bare DMA OOC vs an open-source iDMA comparison |
| Extended addressing | `reports/ext_addressing/` | row/row ≈ 1.5 GB/s vs col/col ≈ 0.26–0.32 GB/s |

: Characterization axes and reports

## The flow matrix

The project is framed as a 2×2 comparison — `{STREAM in-house, Vivado MCDMA} ×
{in-house bridge, Vivado bridge}` — so every cell is measured through the same
shared instrumentation harness:

| Flow | DUT | Status |
|------|-----|--------|
| `flows-stream-bridge/` | STREAM (`stream_top_ch8`) + in-house bridge | **Primary, most complete** — cocotb gate + full FPGA sweeps |
| `flows-vivado-mcdma/` | Vivado AXI-MCDMA IP + in-house bridge | Skeleton (blinks LED; FPGA-only — VHDL IP can't Verilate) |
| `flows-idma-bridge/` | PULP iDMA | Area + datapath-perf cosim only (feeds the iDMA comparison) |
| `flows-stream-vivado-bridge/`, `flows-vivado-mcdma-vivado-bridge/` | future cells | Listed in `make help`; not built |

: The flow matrix

This guide focuses on the primary `flows-stream-bridge` flow; the others are
inventoried in Chapter 6.

## Board and tools

| Item | Detail |
|------|--------|
| Board | Digilent Nexys A7-100T (`xc7a100tcsg324-1`), 100 MHz |
| Build | Vivado 2025.1 |
| Sim | Verilator + cocotb / cocotb_test / pytest |
| Host | Python 3 + `pyserial` over UART (115200 8N1) |

: Board and tool requirements

## Status

The primary `stream-bridge` flow is working — cocotb gate + full FPGA sweeps are
collected, with data in the perf (v1.4) and compression (v1.3) writeups
(`progress/STATUS = 90-DONE`). `flows-vivado-mcdma` is a skeleton;
`flows-idma-bridge` is area + cosim only.
