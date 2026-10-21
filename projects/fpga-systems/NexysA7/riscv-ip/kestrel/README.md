# kestrel on Nexys A7-100T

The kestrel RV32I core
([`projects/components/riscv-ip/kestrel-rv32i`](../../../../components/riscv-ip/kestrel-rv32i/))
on the Nexys A7, behind **block RAM**. It is the same design as the
[Genesys 2 build](../../../Genesys2/riscv-ip/kestrel/README.md): the
`kestrel_mem_bram` memory system (16 KB, registered read; port A fetches at
the core's next PC, a load waits one cycle on port B), the UART loader and
the run/status registers. Only the board top differs: the clock and the
pins.

The host driver and programs are board-independent and live in the Genesys 2
area's `bin/` (`kestrel_board.py`, `kestrel_programs.py`); `host_kestrel.py`
here imports them from there. The UART-equivalence sim runs in that area too,
since it exercises the same bridge, memory system and core.

| Path | What |
|---|---|
| `rtl/kestrel_nexysa7_top.sv` | board top: 100 MHz -> MMCM -> 75 MHz (VCO 900 / 12), UART -> AXI4-Lite, kestrel_mem_bram, kestrel_core, LEDs |
| `build-bram/` | the build (Vivado tcl, constraints, host CLI) |

```sh
make lint
make bitstream            # ALU_DSP=1: ALU add/sub in one DSP48E1; IMPL=default: Vivado defaults
make program
make host-kestrel        # smoke, then the full rv32ui battery
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
| same, `ALU_DSP=1` (1 DSP48E1) | 100 MHz (measurement) | -2.50 ns: worst path 12.5 ns | -- | -- | 2,124 | 4 |
| same, fabric ALU | 76.9 MHz | -0.016 ns (failed, 1 endpoint) | -- | -- | 2,080 | 4 |
| same, fabric ALU | 71.4 MHz | +0.510 ns | not run | -- | 2,020 | 4 |
| + x0 kept zero by writes (no read-side zero-select), one shared signed/unsigned comparator per use, OR-combined ALU result | 100 MHz (measurement) | -2.41 ns | -- | -- | 1,982 | 4 |
| same, `IMPL=explore` (directives, phys_opt, placement over-constraint) | 100 MHz (measurement) | -1.63 ns: worst path 11.6 ns | -- | -- | 2,026 | 4 |
| same, `IMPL=explore` | **75 MHz** | **+0.156 ns** | **1.039** | **72.2 MIPS** | **1,899** | **4** |

: kestrel on the Nexys A7, before and after the timing rework

The first wrapper's worst path ran block-RAM read -> decode -> immediate ->
ALU -> L/S request -> load wait -> register-file write enable (14-15 levels,
~17.7 ns). After the rework it was block-RAM read -> register read -> branch
comparator -> IALIGN halt -> register-file write enable (14.5 ns); with the
write gate naming only the halts an rd-writing instruction can raise, and the
register file in distributed RAM (flops 2,049 -> 1,057), it is now the core's
load/store address into the data RAM (block-RAM read -> register read -> ALU
add -> port-B address, 12.2 ns). The DSP48 add/sub saves 42 LUTs and costs
about 0.3 ns, so the fabric ALU is the default.

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
