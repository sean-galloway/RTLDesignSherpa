# LiteDRAM apples-to-apples harness — build plan

Goal: measure LiteDRAM and pumice with the **same** pattern generator, perf taps,
timer, and UART/CSR path, so `pumice_char` bandwidth/latency numbers are directly
comparable. `litedram_core` replaces pumice+DFI+a7ddrphy (it has its own PLL,
a7ddrphy, DDR2 init, and a 64-bit AXI4 user port).

Status: **WIRED** (verilator-lint-clean harness) + build flow present. Remaining is
board bring-up (proper LiteDRAM regen, XDC reconcile, host variant) — see "Board
bring-up TODO" at the end.

Built (commit adds):
- `rtl/char_engine_harness.sv` — DUT-agnostic harness (engines + perf meters +
  bandwidth timer + harness_csr + UART bridge) exposing an AXI4 master. **Passes
  `verilator --lint-only`** standalone (wiring verified).
- `rtl/litedram_char_top.sv` — board top: `litedram_core` + `char_engine_harness`
  on `user_clk`, `init_done`-gated. AXI user port wired (awsize/arsize
  zero-extended 3->4b; addr [26:0]; no user/lock/cache on the litedram port).
- `rtl/filelists/litedram_char_harness.f`, `constraints/litedram_char.xdc`
  (Nexys A7 pins), `tcl/build_all.tcl` + `tcl/program_fpga.tcl`, `Makefile`
  (`make regen|bitstream|program|characterize`).

## litedram_core interface (build_board/gateware/litedram_core.v)

```
input  clk, rst                         # 100 MHz ref + reset (core has its own PLL)
output init_done, init_error, pll_locked
output user_clk, user_rst               # AXI user-port clock domain (== sys clk)
input  uart_rx / output uart_tx         # BIOS console (self-init)  -- see gotcha
output ddram_a[12:0] ba[2:0] ras_n cas_n we_n cs_n cke odt reset_n dm[1:0]
inout  ddram_dq[15:0] dqs_p[1:0] dqs_n[1:0] ; output ddram_clk_p/clk_n
user_port_axi_0_*                       # AXI4: 64b data, id8, 27b addr (128 MiB),
                                        #   wstrb8. Matches the pattern gen 1:1 —
                                        #   NO width/id adapter needed.
```

## Key structural finding

The reusable engine harness (the two engines + the perf timer + `axi_bus_meter` +
`axi_perf_latency_hist` + their `harness_csr` field mapping) is currently
**embedded inside `ddr2_char_framework/rtl/ddr2_char_macro.sv`**, intertwined with
pumice + the DFI adapter + cmd/rddata-delay shims. It is NOT a standalone block.

**Required refactor:** extract a DUT-agnostic `char_engine_harness` from
`ddr2_char_macro` that exposes exactly:
  * one AXI4 master (write channels from `axi4_master_wr_pattern_gen`, read from
    `axi4_master_rd_crc_check`),
  * the `harness_csr` cfg inputs (o_cfg_wr_*/o_cfg_rd_*/o_start_*) and status/perf
    outputs (i_wr_done/i_rd_done/i_crc_*/i_beats_mismatched/i_timer_*/i_obs_*),
  * the perf timer + `axi_bus_meter` + `axi_perf_latency_hist` taps on that AXI.
Then instantiate it in BOTH `ddr2_char_macro` (feed pumice via DFI) and the new
`litedram_char_top` (feed `litedram_core.user_port_axi_0` directly). This keeps
the two flows measuring identically and avoids a divergent copy.

## Reused UNCHANGED (RTL modules)
`axi4_master_wr_pattern_gen`, `axi4_master_rd_crc_check`, `harness_csr`,
`uart_axil_bridge`, `axi_bus_meter`, `axi_perf_latency_hist`, and the host
`pumice_char` **metrics** (perf_meters/timer bandwidth). `led_status_driver`,
`seven_seg_4digit` for status.

## New files
- `rtl/litedram_char_top.sv` — board top: pins + `litedram_core` + the extracted
  `char_engine_harness` + `uart_axil_bridge` -> `harness_csr` (direct AXIL; the
  1->5 bridge is unneeded — litedram has no APB controller CSRs to reach).
- `constraints/litedram_char.xdc` — CLK100MHZ (E3), CPU_RESETN (C12),
  UART_TXD_IN/RXD_OUT (C4/D4), LED/7seg, and the DDR2 `ddram_*` pins. Adapt from
  `build-perf` XDC; `ddram_a` is 13-bit here (litedram core width).
- `tcl/build_all.tcl`, `tcl/program_fpga.tcl`, `Makefile` — mirror build-perf;
  add `litedram_core.v` + the harness sources to the read_verilog list.

## Clock / reset / init / UART
- Run the whole harness on `user_clk` / `~user_rst` (single domain; exists after
  `pll_locked`). Compute `CLKS_PER_BIT` for the user_clk freq (100 MHz -> 868 @
  115200, or lower baud).
- The host waits on `harness_csr.i_init_done` (<= `litedram_core.init_done`) before
  pulsing start — same sequencing as build-perf. No HW start-gate needed.
- **UART gotcha:** litedram's `uart_rx/uart_tx` is its BIOS console. Tie
  `uart_rx=1'b1` (idle) and leave `uart_tx` open; the LiteX BIOS auto-runs `sdram
  init` without console input and asserts `init_done`. The board FTDI UART goes to
  the HARNESS `uart_axil_bridge` (not litedram's console).

## LiteDRAM core regen (functional init REQUIRED)
The default `./regen.sh` uses `--no-compile-software` (empty BIOS ROM) -> the core
NEVER asserts `init_done`. For the board you MUST regen with a functional BIOS:

```
cd flows-litedram-uart
./regen.sh --bios          # needs riscv-gcc; litex-venv310 (proven this session)
```

## Host divergence
`pumice_char`/`ddr2_char.py` `set_controller_cfg` writes pumice CSRs over the APB
slave — litedram has none. Make a litedram host variant that SKIPS the controller-
config writes (litedram self-configs via BIOS) and keeps engine cfg + perf/timer
readout. If `harness_csr` is wired direct (no bridge), its base is 0.

## Build / program / run (once wired)
```
make -C flows-litedram-uart bitstream      # Vivado, ~20-40 min
make -C flows-litedram-uart program        # flash Nexys A7 (displaces current build)
make -C flows-litedram-uart characterize UART=/dev/ttyUSBx   # perf sweep
```

## Lint strategy (before board)
Lint the extracted `char_engine_harness` standalone with verilator (catches the
engine/csr/perf wiring). The board top can't be verilated (real a7ddrphy
primitives in `litedram_core.v`); the `build_sim/gateware/litedram_core_sim.v`
(SDRAMPHYModel) has no `ddram_*` pads, so a small sim-only top variant can
cocotb-drive the AXI user port if a pre-board smoke is wanted.

## Risks
- BIOS auto-init timing/behavior with `uart_rx` idle (verify `init_done` asserts).
- user_clk CDC for the FTDI UART (single-domain design avoids it).
- XDC `ddram_*` pin set must match `litedram_core.xdc` (generated) exactly.

## Board bring-up TODO (before/while building)
1. `make regen` (`./regen.sh --bios`) — the shipped core has an empty BIOS ROM AND
   placeholder `LOC X` pins; a proper Nexys-A7 regen emits a functional BIOS +
   real ddram pins + a7ddrphy IODELAY constraints in `litedram_core.xdc`.
2. XDC reconcile: `constraints/litedram_char.xdc` currently carries the full
   Nexys A7 pin map (copied from the pumice flow). Once `litedram_core.xdc` has
   real ddram pins, REMOVE the `ddram_*` lines from `litedram_char.xdc` and
   uncomment the `read_xdc .../litedram_core.xdc` line in `tcl/build_all.tcl`
   (keeps CLK/UART/LED/7seg here, ddram + PHY there — no double-constraint).
3. Host variant: copy `build-perf/host/ddr2_char.py` + `pumice_master.py`,
   drop the `set_controller_cfg` pumice-CSR writes (litedram self-configures),
   keep engine cfg + perf/timer bandwidth readout. `harness_csr` is at base 0
   (direct UART->CSR, no 1->5 bridge). Wire `make characterize` to it.
4. `make bitstream && make program && make characterize UART=/dev/ttyUSBx`.
