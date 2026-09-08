# Troubleshooting

## The host CLI cannot find the board

The USB-UART re-enumerates across reboots and replugs, so the port number
drifts. The CLI defaults to `--port auto`, which resolves the port through the
shared board layer: it narrows to this board's ports by USB serial (the board
registry in `projects/fpga-systems/bin/boards/` knows the FTDI serial) and
keeps the one that answers `BUILD_ID == 0x43434331` ("CDC1"). If autodetect
fails:

- Confirm the board is powered and programmed with the **demo** bitstream
  (`make program`), not build-phase1.
- Run `make ports` to see which ttyUSB this board is on right now, and
  `make board-info` for the registry's serial. A swapped board unit shows up
  as "no UART ports found" quoting a serial that is no longer attached.
- Check the FTDI cable and that no other program holds the port.
- Force a specific device with `--port /dev/ttyUSB1` (still probed, so a stale
  path fails loudly instead of driving the wrong board).

## Values look scrambled / never settle

Expected in **NO-CDC mode at a fast clock** — that is the demonstration. For
coherent reads, put the counter in a safe `CDC_MODE` (2 = SYNC-FIFO, or 3/4 for
the handshakes) before reading `VALUE`. `PRESS_COUNT` always uses Gray-coded CDC
and is coherent regardless of mode.

## `make lint` — Xilinx primitive errors

`cdc_demo_top` instantiates `MMCME2_BASE` / `BUFGMUX_CTRL` / `IBUF` / `BUFG`,
which Verilator cannot find. The shared stub file
(`projects/components/misc/rtl/verilator_xilinx_stubs.sv`, pulled in through
its filelist by `build-demo/rtl/filelists/cdc_demo_top.f`) provides
`` `ifdef VERILATOR ``-guarded pass-through stubs (Vivado uses the real unisims
at synthesis; the create_project tcl drops the stub file from the project). If
lint fails with "Cannot find module" for one of these, confirm the stub
filelist is still included in the build's `.f` closure.

## `make sim BUILD=phase1` fails to compile

Phase 1 uses `clock_divider.sv`, which relies on the `` `ALWAYS_FF_RST `` macro
from `rtl/amba/includes/reset_defs.svh`. The build's filelist
(`build-phase1/rtl/filelists/cdc_counter_display_top.f`) carries the
`+incdir` and the reset-defs sub-filelist; the test resolves its sources from
that same closure. If you see
"Define or directive not defined: `ALWAYS_FF_RST`", that include entry is
missing from the filelist.

## `make consistency` fails after editing registers

The generated regmap drifted from the hand-written SV. Regenerate and re-check:

```bash
make regmap
make consistency
```

If it still fails, the SV header table or the `CTR_OFF_*` localparams in
`cdc_demo_harness.sv` disagree with `build-demo/rtl/cdc_demo_csr.rdl` — reconcile the three.

## Sim runs but nothing advances

If a UART-equivalence test hangs, the transport is almost certainly using a pump
instead of `cocotb.function`, or `CLKS_PER_BIT` was left at the silicon value
(868), making each command hundreds of thousands of clocks. Both are covered in
Chapter 6.
