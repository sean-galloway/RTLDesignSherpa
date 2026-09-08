# Troubleshooting

## The host CLI cannot find the board

The USB-UART re-enumerates across reboots and replugs, so the port number
drifts. The CLI defaults to `--port auto`, which probes every `/dev/ttyUSB*` and
keeps the one that answers `BUILD_ID == 0x43434331` ("CDC1"). If autodetect
fails:

- Confirm the board is powered and programmed with the **phase-2** bitstream
  (`make program-demo`), not phase 1.
- Check the FTDI cable and that no other program holds the port.
- Force a specific device with `--port /dev/ttyUSB1`.

## Values look scrambled / never settle

Expected in **NO-CDC mode at a fast clock** — that is the demonstration. For
coherent reads, put the counter in a safe `CDC_MODE` (2 = SYNC-FIFO, or 3/4 for
the handshakes) before reading `VALUE`. `PRESS_COUNT` always uses Gray-coded CDC
and is coherent regardless of mode.

## `make lint-demo` — Xilinx primitive errors

`cdc_demo_top` instantiates `MMCME2_BASE` / `BUFGMUX_CTRL` / `IBUF` / `BUFG`,
which Verilator cannot find. `rtl/verilator_xilinx_stubs.sv` provides
`` `ifdef VERILATOR ``-guarded pass-through stubs (Vivado uses the real unisims
at synthesis; the stub file is never in a Vivado flow). If lint fails with
"Cannot find module" for one of these, confirm the stub file is first in the
`lint-demo` source list.

## `make sim` (phase 1) fails to compile

Phase 1 uses `clock_divider.sv`, which relies on the `` `ALWAYS_FF_RST `` macro
from `rtl/amba/includes/reset_defs.svh`. The phase-1 test compiles that header
first and adds `+incdir+rtl/amba/includes`. If you see
"Define or directive not defined: `ALWAYS_FF_RST`", that include setup is
missing.

## `make consistency` fails after editing registers

The generated regmap drifted from the hand-written SV. Regenerate and re-check:

```bash
make regmap
make consistency
```

If it still fails, the SV header table or the `CTR_OFF_*` localparams in
`cdc_demo_harness.sv` disagree with `rtl/cdc_demo_csr.rdl` — reconcile the three.

## Sim runs but nothing advances

If a UART-equivalence test hangs, the transport is almost certainly using a pump
instead of `cocotb.function`, or `CLKS_PER_BIT` was left at the silicon value
(868), making each command hundreds of thousands of clocks. Both are covered in
Chapter 6.
