# gatling on Nexys A7-100T

The gatling four-context barrel RV32I
([`projects/components/riscv-ip/gatling-rv32i`](../../../../components/riscv-ip/gatling-rv32i/))
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

Two builds: **build-bram** is the barrel alone (below), **build-tetrad** is
the whole tetrad -- the barrel with Xcell and four cells on alu-infer
([build-tetrad](#build-tetrad-the-tetrad)).

| Path | What |
|---|---|
| `rtl/gatling_nexysa7_top.sv` | build-bram top: 100 MHz -> MMCM -> 100 MHz, UART -> AXI4-Lite, gatling_mem_bram, gatling_core, LEDs |
| `build-bram/` | the build (Vivado tcl, constraints, host CLI) |
| `bin/gatling_board.py`, `bin/gatling_programs.py` | host driver + programs, the SAME code in sim and on the board |
| `dv/tests/test_gatling_board_uart.py` | UART-equivalence sim: the programs over the real bridge RTL |
| `rtl/gatling_tetrad_nexysa7_top.sv`, `rtl/gatling_tetrad_rig.sv` | build-tetrad top (MMCM, reset, LEDs) and everything below its clock |
| `rtl/gatling_tetrad_harness.sv`, `rtl/gatling_tetrad_axil_split.sv` | the cells' host side (cfg, fill, drain, FLUSH/KICK observers) and the AXI4-Lite split |
| `build-tetrad/`, `bin/gatling_tetrad_board.py`, `bin/gatling_tetrad_programs.py` | the tetrad build, host driver and programs |
| `dv/tests/test_gatling_tetrad_board_uart.py` | UART-equivalence sim of build-tetrad (the rig as toplevel) |

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

## build-tetrad: the tetrad

`gatling_tetrad` -- the barrel core, the Xcell unit and per context a cell's
input memory, alu-infer and result memory -- behind the same
`gatling_mem_bram` (programs, run control, status at `0x0_0000`) and a cell
harness at `0x4_0000` that plays the rest of each cell: the configuration
its cfg stream would set, the fill side of the input memory, the drain side
of the result memory, a one-deep drain controller that captures each FLUSH
command, and observers for KICK, stalls and consumed lines. The register map
is in the harness's RTL header.

The ALU is alu-infer's bf16 profile (every `ALU_EN_*` = 0): four full ALUs
are 95.6k LUT and do not fit the part (alu-infer TASK-012). The clock is
**4.6875 MHz**, the functional bring-up clock alu-infer's own Nexys A7 rig
uses: alu-infer's rows are combinational at their default latencies, and the
worst path -- Xcell's latched function into an ALU row and on into the
pipe's result buffer -- is 158.1 ns over 202 levels (alu-infer TASK-010).
The core and the Xcell unit meet 100 MHz on their own.

```sh
make -C build-tetrad sim                    # UART-equivalence sim (smoke + tetrad at N = 40)
make -C build-tetrad bitstream
make -C build-tetrad program
make -C build-tetrad host-gatling_tetrad    # smoke, then the tetrad program at N = 96
make -C build-tetrad host-gatling_tetrad ARGS="--count 384 --seed 7"
```

The tetrad program is gatling-rv32i's (`dv/tbclasses/gatling/tetrad_program.py`,
the one `test_gatling_tetrad` runs): one binary on four contexts over a MAC,
an ADD, a RELU and a COMPARE cell -- CLEAR, N ACCUMULATE, KICK, WAIT on all
four, FLUSH, ECTX. The host starts the contexts before feeding any line, so
every first `POP x0` waits on an empty memory, then feeds and drains over the
UART, which fills and empties both 32-line memories in turn. LEDs: 0-3 a
context running (on), done (slow blink) or halted otherwise (fast blink),
4 MMCM locked, 5/6 UART activity, 7 heartbeat.

### Board result (2026-11-26)

Nexys A7-100T (serial 210292BFA3EE), 4.6875 MHz, 0.2 ns user clock
uncertainty: **WNS +54.762 ns**, 0 failing endpoints, hold +0.009 ns.

| Run | Result |
|---|---|
| smoke | PASS: harness ID, BUILD_ID, every cell's config read back distinct, both memories empty |
| tetrad N = 96, seed 1 | PASS: 97 results per cell, every one golden-identical; 194 / 194 / 97 / 97 lines consumed; one KICK of 1 and one FLUSH with its {tag, dest} per context, each captured after all four KICKs; all four DONE; 394 instructions retired each |
| tetrad N = 384, seed 7 | PASS: 385 results per cell, golden-identical; 770 / 770 / 385 / 385 lines; 1,546 instructions each |

: build-tetrad on the Nexys A7

Every context was seen waiting on `POP x0` (its empty input memory) and on
WAIT; the ADD, RELU and COMPARE contexts were also seen waiting on
`PUSH x0` (a full result memory). The first host run after the first
programming answered one read with `ERR` (gatling-rv32i ISSUE-001); it has
not recurred in three full runs and 160 targeted reads.

| Block | LUTs | Registers |
|---|---|---|
| whole top | 37,601 (59%) | 14,887 |
| gatling_tetrad | 35,491 | 12,463 |
| gatling_tetrad_harness | 1,010 | 1,083 |
| gatling_mem_bram | 675 | 747 |
| uart_axil_bridge | 417 | 530 |

: build-tetrad area (17 block RAM tiles, 0 DSPs)

Vivado books most of alu-infer's logic to `gatling_xcell` across the
hierarchy (24.7k LUT there, 383 LUT built alone); alu-infer TASK-011/012
have the breakdown.
