# Granite DDR2/LPDDR2 v2 on Nexys A7

This target builds the Granite product controller on the Digilent Nexys A7-100T
side-by-side with the existing `build-perf` pumice target. It reuses the shared
DDR2 characterization framework (UART bridge, harness CSR, a7ddrphy adapter) and
swaps the controller macro for `granite_char_macro` + `granite_top_geared`.

## Files

| File | Purpose |
|---|---|
| `rtl/granite_char_top.sv` | Pin-level FPGA top (clocks, a7ddrphy, pads). |
| `rtl/granite_char_macro.sv` | AXI engines + Granite controller macro. |
| `rtl/granite_char_harness.sv` | UART/AXIL integration, CSR, timer, displays. |
| `rtl/filelists/granite_char_harness.f` | Verilator/Vivado compile closure. |
| `Makefile` | Thin wrapper around `make/fpga_flow.mk`. |

## Frequency plan

Default: **75 MHz sys / 300 MT/s DDR2-300**.
Optional define `GRANITE_SYS_66` selects the 66.67 MHz known-good fallback
(133.3 MHz CK, DDR2-266). The UART baud divisor and timer CSRs must track the
selected frequency.

`GRANITE_SYS_100` (100 MHz sys, sys2x kept at 150 MHz) is a TIMING build,
not a board point: the a7ddrphy serializers take `CLKDIV = sys` and `CLK =
sys2x` and need sys2x = 2 x sys exactly, so at 3:2 read leveling finds no eye
and every beat mismatches (measured 2026-10-29). A 100 MHz board point is the
DDR2-400 plan (sys2x 200 MHz, as pumice's `PUMICE_SYS_100`), which needs its
own build, init and calibration tuple.

## Build

```bash
# Lint only
verilator --lint-only -Wno-MODDUP -f rtl/filelists/granite_char_harness.f --top-module granite_char_top

# Bitstream (uses shared framework XDC)
make bitstream
```
