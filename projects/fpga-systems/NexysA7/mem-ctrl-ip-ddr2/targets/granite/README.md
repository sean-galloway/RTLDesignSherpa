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

`GRANITE_SYS_100` selects 100 MHz sys / 200 MHz sys2x = DDR2-400 (peak 800
MB/s), the same plan as pumice's `PUMICE_SYS_100`. sys2x must be exactly 2 x
sys: the a7ddrphy serializers take `CLKDIV = sys` and `CLK = sys2x`. The
earlier 100 / 150 MHz (3:2) timing-push plan levelled no read eye and
mismatched every beat on the board (2026-10-29) and is gone.

## Build

```bash
# Lint only
verilator --lint-only -Wno-MODDUP -f rtl/filelists/granite_char_harness.f --top-module granite_char_top

# Bitstream (uses shared framework XDC)
make bitstream
```
