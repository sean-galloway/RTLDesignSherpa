# Overview

## What it characterizes

This project performs end-to-end, board-level **performance, latency, and
data-integrity characterization** of a DDR2/LPDDR2 memory controller on real
silicon. It drives the onboard Micron `MT47H64M16HR-25E` DDR2 (x16, single-rank,
128 MiB, up to 800 Mbps) through the controller against the real device, and
reports throughput (MB/s), latency histograms, and per-workload CRC integrity
across burst-length / stride / gap / page-policy / scheme sweeps.

There is no soft CPU in the FPGA — an off-board Python **host** drives the
harness over the FTDI USB-UART (115200 8N1). The same host programs run against
a cocotb simulation (Chapter 5).

## The three flows

The project is organized as sibling "flows" plus a shared framework:

| Flow | Controller (DUT) | What it is |
|------|------------------|-----------|
| `flows-ours-uart/` | pumice DDR2 (black box) + DFI + a7ddrphy | **Primary** flow: UART-driven host + Vivado build of the pumice harness on the Nexys A7. |
| `flows-litedram-uart/` | LiteDRAM `litedram_core` | Apples-to-apples baseline: LiteDRAM's own DDR2 controller (self-initializing, own PLL/PHY) driven by the **same** engines/taps/host. |
| `ddr2_char_framework/` | — | Shared instrumentation: harness RTL, the engine wrapper (`ddr2_char_macro`), the 1→4 AXIL bridge, and the cocotb DV. |

: The characterization flows

The naming convention is `flows-<controller>-uart/` for on-Nexys builds (host
over UART, no CPU). pumice is separate IP under
`projects/components/memory-controllers/pumice-ddr2-lpddr2/`.

## Board and tools

| Item | Detail |
|------|--------|
| Board | Digilent Nexys A7-100T, Artix-7 `xc7a100tcsg324-1` |
| DRAM | Onboard Micron `MT47H64M16` DDR2 x16, `ROW_WIDTH = 13` |
| Build | Vivado (batch mode) |
| Host | Python 3 + `pyserial` |
| Sim | Verilator + cocotb / cocotb_test / pytest |
| PHY regen (only) | Python 3.10 + migen / litex 2024.12 / litedram 2024.12 |

: Board and tool requirements

## Workload families

The characterization sweeps four access-pattern families (`host/pumice_char.py`):

| Family | Access | Purpose |
|--------|--------|---------|
| `incremental` | contiguous linear | best-case sequential |
| `row_major` | bounded to one page | guaranteed page HIT |
| `col_major` | stride = one row, same bank | guaranteed page MISS (worst case) |
| `col_major_interleaved` | stride = one bank | activates the bank pipeline |

: Access-pattern families

Controller-config presets (`baseline`, `bank_interleave`, `open_page`,
`inorder`, `reorder`, `happy_hybrid`, `fast_refresh`, `slow_refresh`) each flip
one lever from baseline; they are driven over the pumice APB slave (black box).
Run profiles `smoke` / `matrix` / `full` are shared by sim and board.
