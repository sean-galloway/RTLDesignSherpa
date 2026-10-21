# kestrel on Genesys 2

The kestrel RV32I core
([`projects/components/riscv-ip/kestrel-rv32i`](../../../../components/riscv-ip/kestrel-rv32i/))
on the board, behind **block RAM**.

kestrel is single-cycle and its memory contract was combinational reads. A
board-sized memory wants block RAM, whose read is registered, so this build
uses `kestrel_mem_bram`: one unified true-dual-port array (16 KB by
default). Port A fetches at the core's next PC (`imem_addr_next`), so the
RAM's output register acts as the instruction register and an instruction
takes one clock; a load holds the core with `mem_wait` for one more while
port B reads. The core holds all state while `mem_wait` is high, so the ISA
is untouched -- riscv-formal proves all 42 checks with `mem_wait` driven
freely (bounded to two consecutive waits), and the rv32ui battery passes
42/42 through this memory path with spike lockstep (`ma_data` is an expected
halt: kestrel halts on misaligned loads/stores, cause 4/5).

**The Nexys A7 is the reference board; this build is not rebuilt (owner,
2026-10-21).** The 80 MHz figure below was closed with the first version of
the wrapper (a fetch / execute / load sequencer, CPI 2-3, and the hardware
misaligned retry). The current design is measured on the Nexys A7
(`../../../NexysA7/riscv-ip/kestrel/README.md`): the same RTL and the same
host battery, on the slower fabric, so a rebuild here adds only a Kintex-7
fmax figure. The UART cosim below still runs from this directory
(`make clean-all && make sim`) and is the part of this build that gates.

The second port is the UART loader: write an image in load mode, set
`CTRL.run`, poll the status (halted, cause, cycles, instret, and the last
value written to gp -- the riscv-tests verdict, since kestrel halts on the
final ecall).

| Path | What |
|---|---|
| `rtl/kestrel_genesys2_top.sv` | board top: 200 MHz LVDS -> MMCM -> 80 MHz, UART -> AXI4-Lite, kestrel_mem_bram, kestrel_core, LEDs |
| `build-bram/` | the build (Vivado tcl, constraints, host CLI) |
| `bin/kestrel_board.py`, `bin/kestrel_programs.py` | host driver + programs, the SAME code in sim and on the board |
| `dv/tests/test_kestrel_board_uart.py` | UART-equivalence sim: the programs over the real bridge RTL |

```sh
make sim                 # the UART-equivalence sim
make lint
make bitstream
make program
make host-kestrel        # smoke, then the full rv32ui battery (~30 s at 115200)
```

LEDs: 0 run, 1 halted, 2 halted on ecall, 3 MMCM locked, 5/6 UART activity,
7 heartbeat.
