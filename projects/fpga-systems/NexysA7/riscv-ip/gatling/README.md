# gatling on Nexys A7-100T

The gatling four-context barrel RV32I
([`projects/components/riscv-ip/gatling-rv32itetrad`](../../../../components/riscv-ip/gatling-rv32itetrad/))
on the Nexys A7, behind **block RAM**: four harts running four programs at
once on one shared datapath.

gatling interleaves its four contexts through a four-stage F/D/X/W rotation,
one context per stage per cycle, so each hart has exactly one instruction in
flight and retires once every four cycles; the core retires one instruction
per clock with all four running. Every memory it touches is a registered-read
block RAM whose latency is exactly one stage -- fetch (F to D), register read
(D to X), load (X to W) -- so, unlike [kestrel](../kestrel/README.md), there
is no wait state anywhere.

The memory system (`gatling_mem_bram`) gives each hart a private 16 KB
program/data bank and its own run bit, so the host can load and start each
hart separately -- including reloading one while the other three run (a
running hart's bank refuses writes). Status per hart: halted, cause, cycles,
instret, and the last value written to gp (the riscv-tests verdict, since a
hart halts on its final ecall).

| Path | What |
|---|---|
| `rtl/gatling_nexysa7_top.sv` | board top: 100 MHz -> MMCM -> 100 MHz, UART -> AXI4-Lite, gatling_mem_bram, gatling_core, LEDs |
| `build-bram/` | the build (Vivado tcl, constraints, host CLI) |
| `bin/gatling_board.py`, `bin/gatling_programs.py` | host driver + programs, the SAME code in sim and on the board |
| `dv/tests/test_gatling_board_uart.py` | UART-equivalence sim: the programs over the real bridge RTL |

```sh
make sim                  # the UART-equivalence sim
make lint
make bitstream            # IMPL=default: Vivado defaults instead of the explore flow
make program
make host-gatling         # smoke, then the rv32ui battery on all four harts
```

The battery runs four DIFFERENT rv32ui images at once, one per hart, and
rotates them so every hart runs all 42 (168 runs). LEDs: 0-3 a hart running
(on) or halted (blinking), 4 MMCM locked, 5/6 UART activity, 7 heartbeat.

## Board result (2026-10-21)

`make host-gatling` on the Nexys A7-100T (serial 210292BFA3EE) at **100 MHz**:
smoke PASS (every bank distinct; a running hart's bank refused a write),
rv32ui **168/168 PASS** -- all 42 images on each of the four harts, four
different images at once every round (`ma_data` is the expected
misaligned-load halt, cause 4). Two back-to-back runs, identical verdicts
(CPI per hart 4.004-4.005 both times).

| Measure | gatling (4 harts) | kestrel (1 hart) |
|---|---|---|
| Clock | **100 MHz** (+0.152 ns, IMPL=explore) | 75 MHz (+0.156 ns) |
| CPI per hart | **4.004** (4 by construction; the rest is run start/stop) | 1.039 |
| Peak throughput | **100 MIPS** (4 x 25 MIPS) | 72.2 MIPS |
| Battery throughput (instret / round cycles) | 0.688 IPC: 68.8 MIPS | -- |
| LUTs / registers | 2,281 / 1,742 | 1,899 / 1,057 |
| Block RAM tiles | 17 (16 memory, 1 register files) | 4 |
| DSPs | 0 | 0 |

: gatling and kestrel on the Nexys A7, the whole board top

The battery's aggregate (0.688 IPC) is below the core's 1.0 because each
round waits for its longest image: harts that finish early sit halted, and
their slots in the rotation go empty. While all four run, the core retires
one instruction per clock (each hart at CPI 4).

Area by block: gatling_core 1,066 LUTs (decode, immediates and ALU are
flattened into it; its register files are 2 RAMB18), gatling_mem_bram 799
LUTs (four banks of 16 KB = 16 tiles, plus four sets of status counters),
uart_axil_bridge 418.

The worst path (9.4 ns, 10 levels) runs from the register-file block RAM
through the branch comparator and halt logic to the context PC's clock
enable -- the X stage, as expected: every other stage is a fraction of it.
