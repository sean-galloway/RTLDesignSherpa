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

## STATUS UPDATE 2026-09-10 — items 1 and 2 are DONE; item 0 is new and blocking

Worked through the TODO below on real hardware. What changed:

**Done:**
- **Item 1 (regen with BIOS): DONE.** `./regen.sh --bios` now produces a board
  core with a functional BIOS (63 KB ROM, 6975 non-zero words) at the CORRECT
  operating point. `litedram_hp.yml` `sys_clk_freq` was changed 100e6 -> 75e6
  so the core runs **75 MHz / 1:2 / 300 MT/s — the same point pumice is
  measured at**. The stock 100 MHz / 1:4 would have made the A/B meaningless.
- **Item 2 (XDC reconcile): NOT NEEDED.** The regenerated
  `build_board/gateware/litedram_core.xdc` contains **no** ddram pins, so the
  harness `constraints/litedram_char.xdc` keeps the full pin map and the
  `read_xdc` line in `build_all.tcl` stays commented. Nothing to reconcile.

**Five flow bugs found and fixed while getting synthesis to run:**
1. `Makefile` `REPO_ROOT ?= $(abspath .../../../..)` was two levels short. That
   count was correct at the old `projects/NexysA7/...` path and broke silently
   when the area moved under `projects/fpga-systems/`. Now `git rev-parse`.
2. `CONVERTERS_ROOT` was never exported, so the filelist chain died on the
   first converters `-f`.
3. `build_all.tcl`'s `read_flist` only substituted `$REPO_ROOT`; any other
   `$VAR` passed through literally. It now expands any environment variable
   and errors clearly if one is unset.
4. `.vlt` Verilator lint-waiver files were handed to Vivado, which parses them
   as Verilog and dies on the first `-`. Now skipped.
5. `litedram_gen` emits `litedram_core.tcl` referencing `VexRiscv.v` by an
   absolute path **inside the LiteX venv**, which does not survive the venv (or
   /tmp) being rebuilt. `regen.sh` now vendors it beside the core and the
   filelist uses that copy.

**Item 0 (NEW, BLOCKING): `char_engine_harness.sv` is wired to a `harness_csr`
that no longer exists.** Synthesis now reaches the harness and stops on **41
port mismatches**. The whole per-generator config surface — `o_cfg_wr_*`,
`o_cfg_rd_*`, `o_start_wr_pulse`/`o_start_rd_pulse`, and the CRC readback
(`i_crc_expected`/`i_crc_actual`/`i_beats_mismatched`) — moved OUT of
`harness_csr` and into `chargen_regs` when the char framework went to a
16-generator array. `harness_csr` is now 75 ports of global/PHY/DFI config
only.

So the harness needs rewiring against the CURRENT framework: `harness_csr` for
the global surface, `chargen_regs` (PeakRDL, see `chargen_regs.rdl`) for
per-generator config, and the generator array rather than one wr + one rd
engine. That is a real piece of integration work, not a patch, and it is what
stands between here and a like-for-like number. The pumice flow's
`ddr2_char_macro.sv` is the reference for how the array is driven today.

---

## Board bring-up TODO (original, before/while building)
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

## STATUS UPDATE 2026-09-10 (later) — item 0 DONE; harness matches build-perf

Sean: "update the litedram harness to match the current one for consistency";
chosen approach: extract a shared engine block.

- `ddr2_char_framework/rtl/char_engine_block.sv` (NEW) holds the DUT-agnostic
  spine that used to sit inline in `ddr2_char_macro.sv`: chargen shim + regs,
  GO logic, the generator arrays, both crossbars, perf meters and latency
  histograms, exposed as one AXI4 master. `ddr2_char_macro` now instantiates it
  (`u_engines`) and wraps pumice around it -- 1238 -> 576 lines, no behaviour
  change (char-framework sim: uart + char green; macro suite on the refactor
  passes the same cases the original does).
- `rtl/char_engine_harness.sv` REWRITTEN as build-perf's `ddr2_char_harness`
  minus the controller: same UART bridge, same `bridge_ddr2_char_axil` (address
  map identical; `ddr2_apb` and `obs_apb` terminated), same `harness_csr`
  (BUILD_ID "LDR2"), same debug_sram/dfi_mon_ram slots, soft-reset stretch,
  timer and LED map, and `char_engine_block` behind `chargen_apb`. The 41 dead
  `harness_csr` connections are gone with the single wr/rd engines.
- `rtl/litedram_char_top.sv`: `FPGA_CLK_HZ` 100 -> 75 MHz (user_clk is the
  75e6 `sys_clk_freq`; the UART divisor was wrong), CFG_* identity words set to
  the LiteDRAM geometry, new AXI sideband outputs left open.
- Filelists split: `litedram_char_harness.f` (lint closure) +
  `litedram_char_board.f` (adds top + core). `make lint` is clean (verilator
  5.045, 136 sources). Makefile is now variables over `make/fpga_flow.mk`
  (`lint`, `bitstream`, `program` via the board registry, `host-*`);
  `tcl/program_fpga.tcl` retired in favour of `make program`.
- `host/host_litedram_char.py`: the pumice host with `LiteDRAMCharDriver`
  (pumice CSR calls -> no-ops, `wait_init` on `STATUS.init_done`) and one
  `litedram` config; `--char-profile` reuses the pumice scenario grids.

DONE the same day: bitstream (timing met after the CRG reset-strobe false
path), programmed, `--char-profile matrix --char-scale 1000` 14/14, CSV +
findings saved beside the pumice results (PUMICE-026). Reads 564-579 MB/s vs
pumice 291.7 on identical RTL: the pumice read ceiling is pumice's.
