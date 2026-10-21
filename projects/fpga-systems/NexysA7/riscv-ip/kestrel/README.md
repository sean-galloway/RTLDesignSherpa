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
| `rtl/kestrel_nexysa7_top.sv` | board top: 100 MHz -> MMCM -> 62.5 MHz (`CLK_DIV` 16), UART -> AXI4-Lite, kestrel_mem_bram, kestrel_core, LEDs |
| `build-bram/` | the build (Vivado tcl, constraints, host CLI) |

```sh
make lint
make bitstream
make program
make host-kestrel        # smoke, then the full rv32ui battery
```

LEDs: 0 run, 1 halted, 2 halted on ecall, 3 MMCM locked, 5/6 UART activity,
7 heartbeat.

## Board result (2026-10-20)

`make host-kestrel` on the Nexys A7-100T (serial 210292BFA3EE), current
design at 62.5 MHz: smoke PASS, rv32ui **42/42 PASS** (`ma_data` is the
expected misaligned-load halt, cause 4), mean CPI **1.039** (1.00 plus the
load fraction; `ld_st` 1.20).

| Design | Clock | Post-route WNS | CPI | Throughput | LUTs | Block RAM |
|---|---|---|---|---|---|---|
| First wrapper: fetch/exec/load sequencer, 128 KB, hardware misaligned retry | 62.5 MHz | -1.70 ns (failed) | -- | -- | 2,776 | 32 |
| First wrapper | 50 MHz | +0.147 ns | 2.049 | 24.4 MIPS | 2,776 | 32 |
| Next-PC fetch, opcode load wait, 16 KB, misaligned halt, parallel immediates | 100 MHz (measurement) | -4.48 ns: worst path 14.5 ns | -- | -- | 2,470 | 4 |
| same | 66.7 MHz | -0.019 ns (failed, 1 endpoint) | -- | -- | 2,346 | 4 |
| same | **62.5 MHz** | **+0.210 ns** | **1.039** | **60.2 MIPS** | **2,341** | **4** |

: kestrel on the Nexys A7, before and after the timing rework

The first wrapper's worst path ran block-RAM read -> decode -> immediate ->
ALU -> L/S request -> load wait -> register-file write enable (14-15 levels,
~17.7 ns). The current worst path is block-RAM read -> register-file read ->
branch comparator -> next-PC low bits -> instruction-misaligned halt (cause
3) -> register-file write enable (14 levels, 14.5 ns, 67% routing). Branches
never write a register, so taking the branch condition out of the
write-enable gate is the next cut.
