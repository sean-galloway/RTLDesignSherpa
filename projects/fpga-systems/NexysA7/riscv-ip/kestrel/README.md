# kestrel on Nexys A7-100T

The kestrel RV32I core
([`projects/components/riscv-ip/kestrel-rv32i`](../../../../components/riscv-ip/kestrel-rv32i/))
on the Nexys A7, behind **block RAM**. This is kestrel's only board build.

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

The second port is the UART loader: write an image in load mode, set
`CTRL.run`, poll the status (halted, cause, cycles, instret, and the last
value written to gp -- the riscv-tests verdict, since kestrel halts on the
final ecall).

A Genesys 2 build of the first wrapper (80 MHz, CPI 2-3) also existed. It
was removed on 2026-10-21 (owner) so kestrel has one board area; its host
driver, programs and UART cosim moved here unchanged, and git history keeps
the rest.

| Path | What |
|---|---|
| `rtl/kestrel_nexysa7_top.sv` | board top: 100 MHz -> MMCM -> 75 MHz (VCO 900 / 12), UART -> AXI4-Lite, kestrel_mem_bram, kestrel_core, LEDs |
| `build-bram/` | the build (Vivado tcl, constraints, host CLI) |
| `bin/kestrel_board.py`, `bin/kestrel_programs.py` | host driver + programs, the SAME code in sim and on the board |
| `dv/tests/test_kestrel_board_uart.py` | UART-equivalence sim: the programs over the real bridge RTL |

```sh
make sim                  # the UART-equivalence sim
make lint
make bitstream            # IMPL=default: Vivado defaults instead of the explore flow
make program
make host-kestrel         # smoke, then the full rv32ui battery
```

LEDs: 0 run, 1 halted, 2 halted on ecall, 3 MMCM locked, 5/6 UART activity,
7 heartbeat.

## Board result (2026-10-20)

`make host-kestrel` on the Nexys A7-100T (serial 210292BFA3EE), current
design at **75 MHz**: smoke PASS, rv32ui **42/42 PASS** (`ma_data` is the
expected misaligned-load halt, cause 4), mean CPI **1.039** (1.00 plus the
load fraction; `ld_st` 1.20): **72.2 MIPS**.

| Design | Clock | Post-route WNS | CPI | Throughput | LUTs | Block RAM |
|---|---|---|---|---|---|---|
| First wrapper: fetch/exec/load sequencer, 128 KB, hardware misaligned retry | 62.5 MHz | -1.70 ns (failed) | -- | -- | 2,776 | 32 |
| First wrapper | 50 MHz | +0.147 ns | 2.049 | 24.4 MIPS | 2,776 | 32 |
| Next-PC fetch, opcode load wait, 16 KB, misaligned halt, parallel immediates | 100 MHz (measurement) | -4.48 ns: worst path 14.5 ns | -- | -- | 2,470 | 4 |
| same | 66.7 MHz | -0.019 ns (failed, 1 endpoint) | -- | -- | 2,346 | 4 |
| same | **62.5 MHz** | **+0.210 ns** | **1.039** | **60.2 MIPS** | **2,341** | **4** |
| + register file without reset (distributed RAM), write gate without the branch comparator | 100 MHz (measurement) | -2.22 ns: worst path 12.2 ns | -- | -- | 2,166 | 4 |
| same, ALU add/sub in one DSP48E1 (option since removed) | 100 MHz (measurement) | -2.50 ns: worst path 12.5 ns | -- | -- | 2,124 | 4 |
| same, fabric ALU | 76.9 MHz | -0.016 ns (failed, 1 endpoint) | -- | -- | 2,080 | 4 |
| same, fabric ALU | 71.4 MHz | +0.510 ns | not run | -- | 2,020 | 4 |
| + x0 kept zero by writes (no read-side zero-select), one shared signed/unsigned comparator per use, OR-combined ALU result | 100 MHz (measurement) | -2.41 ns | -- | -- | 1,982 | 4 |
| same, `IMPL=explore` (directives, phys_opt, placement over-constraint) | 100 MHz (measurement) | -1.63 ns: worst path 11.6 ns | -- | -- | 2,026 | 4 |
| same, `IMPL=explore` | **75 MHz** | **+0.156 ns** | **1.039** | **72.2 MIPS** | **1,899** | **4** |
| same, seven ALU rows in one DSP48E1 (option since removed) | 100 MHz (measurement) | -1.71 ns | -- | -- | 2,029 | 4 |
| same, DSP ALU (removed) | 75 MHz | +0.142 ns | 1.039 | 72.2 MIPS | -- | 4 |

: kestrel on the Nexys A7, before and after the timing rework

The first wrapper's worst path ran block-RAM read -> decode -> immediate ->
ALU -> L/S request -> load wait -> register-file write enable (14-15 levels,
~17.7 ns). After the rework it was block-RAM read -> register read -> branch
comparator -> IALIGN halt -> register-file write enable (14.5 ns); with the
write gate naming only the halts an rd-writing instruction can raise, and the
register file in distributed RAM (flops 2,049 -> 1,057), it is now the core's
load/store address into the data RAM (block-RAM read -> register read -> ALU
add -> port-B address, 12.2 ns). An add/sub-only DSP48 option saved 42 LUTs and cost about 0.3 ns; see
below for the DSP ALU and why it was removed.

The next three changes take ideas from the BRISKI barrel core (no code is
copied): x0 is kept zero by writing it (init-by-write, not a RAM `initial`),
one comparator serves signed and unsigned, and the ALU ORs its rows
instead of muxing them. They cut 184 LUTs; on their own they did not move
the worst path, which became the fetch address (next PC -> port-A address)
at about the same length. The implementation flow did: `IMPL=explore` (opt
`Explore`, place `ExtraPostPlacementOpt` under a temporary 0.3 ns setup
uncertainty, post-place and post-route `phys_opt AggressiveExplore`, route
`AggressiveExplore -tns_cleanup`) gains about 0.8 ns on the same netlist
and is this build's default. Owner: 75 MHz is the target.

A seven-row DSP ALU built ADD, SUB, AND, OR, XOR, SLT and SLTU in one
instantiated DSP48E1 (the logic unit and the subtract's sign; UG193's
compare application; BRISKI's one-DSP ALU idea), shifts in fabric. On the
same netlist and flow it saved no LUTs (1,905 vs 1,908 synthesized, 2,029 vs
2,026 routed), traded 13 CARRY4 for 18 more occupied slices, and was 0.08 ns
slower at 100 MHz; it met 75 MHz and ran 42/42 on the board, as does the
fabric build (A/B 2026-10-20: three batteries and a 46,074-write soak each,
no UART faults). It was removed (owner, 2026-10-20); the kestrel MAS
kestrel_alu chapter, "Why the ALU is not in a DSP", records why.
