# kestrel on Nexys A7-100T

The kestrel RV32I core
([`projects/components/riscv-ip/kestrel-rv32i`](../../../../components/riscv-ip/kestrel-rv32i/))
on the Nexys A7, behind **block RAM**. It is the same design as the
[Genesys 2 build](../../../Genesys2/riscv-ip/kestrel/README.md): the
`kestrel_mem_bram` memory system (128 KB, registered read, fetch / execute /
load sequencer holding the core with `mem_wait`), the UART loader and the
run/status registers. Only the board top differs: the clock and the pins.

The host driver and programs are board-independent and live in the Genesys 2
area's `bin/` (`kestrel_board.py`, `kestrel_programs.py`); `host_kestrel.py`
here imports them from there. The UART-equivalence sim runs in that area too,
since it exercises the same bridge, memory system and core.

| Path | What |
|---|---|
| `rtl/kestrel_nexysa7_top.sv` | board top: 100 MHz -> MMCM -> 50 MHz, UART -> AXI4-Lite, kestrel_mem_bram, kestrel_core, LEDs |
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

`make host-kestrel` on the Nexys A7-100T (serial 210292BFA3EE): smoke PASS,
rv32ui **42/42 PASS**, mean CPI 2.049 (2.00 for ALU and branch tests, about
2.08 with loads, 2.51 for `ma_data`'s cross-word accesses).

| Clock | Post-route WNS | Notes |
|---|---|---|
| 62.5 MHz | -1.70 ns | failed: the single-cycle path is ~17.7 ns on the Artix-7 -1 |
| 50 MHz | +0.147 ns | met; the router stops optimizing once met, so the same path routes to 19.1 ns |

2,776 LUTs (4%), 32 of 135 block RAMs. The worst path is the one the Genesys 2
build shows: block-RAM read -> decode -> ALU -> load-wait -> register-file
write enable.
