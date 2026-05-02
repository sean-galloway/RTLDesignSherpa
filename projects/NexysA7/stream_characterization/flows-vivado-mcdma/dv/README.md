# dv/  (intentionally empty for cocotb)

This flow is **FPGA-only validated**. There are no pre-silicon cocotb
tests under `dv/tests/`, by design.

## Why no cocotb

The Vivado AXI MCDMA IP ships as VHDL only:

```
projects/NexysA7/stream_characterization/rtl-vivado/axi_mcdma_0/
├── hdl/axi_mcdma_v1_2_vh_rfs.vhd          (VHDL)
├── hdl/axi_datamover_v5_1_vh_rfs.vhd      (VHDL)
├── synth/axi_mcdma_0.vhd                  (VHDL)
└── sim/axi_mcdma_0.vhd                    (VHDL)
```

The repo's cocotb harness runs on Verilator, which is SystemVerilog
only — Verilator cannot simulate VHDL at all, encrypted or otherwise.
Switching this one flow to Vivado's xsim is possible (xsim handles VHDL
+ encrypted IP), but xsim adds a Vivado dependency to the sim flow and
slows compile turnaround substantially.

The trade-off we made: this characterization is about **measuring real
silicon throughput on the Nexys A7-100T**, not about RTL regression
testing of vendor IP. Skipping cocotb here is consistent with that goal.

## Where validation actually happens

1. **The shared harness** (`stream_char_framework/rtl/`) gets cocotb gate
   testing in `flows-stream-bridge/dv/tests/`. Since the instrumentation
   library is identical between flows, any harness-level bug found in
   stream-bridge is automatically fixed for vivado-mcdma.

2. **The Vivado MCDMA wiring** (the per-flow `vivado_mcdma_harness.sv`
   that bolts MCDMA into the framework) is exercised on the actual
   board:
   - `make project` validates the IP elaborates with our parameters.
   - `make synth` validates it fits and synthesises.
   - `make bitstream` validates it routes and meets timing.
   - `make program` + `cmds.sh` / `char_cmds.sh` validates it actually
     moves data correctly under each delay / channel / size sweep, with
     per-channel CRC verification on the read and write paths.

3. **The host-side characterization scripts** (Python, `host/`) are
   tested end-to-end against the live FPGA over UART — no simulator
   needed.

## If you want to add Python-driven validation later

`dv/` itself stays as a directory because **host-driven test scripts**
(Python that talks to the live FPGA over UART, validates CSR maps,
descriptor parsing, IRQ behavior, etc.) belong here. Drop those under
`dv/host_tests/` or similar — keep `dv/tests/` reserved for cocotb if
we ever switch this flow to xsim.

## Tracking

If we later decide to add xsim-based cocotb regression for MCDMA:

1. Convert `test_vivado_mcdma.py` to use `cocotb_test.simulator.run`
   with `simulator="xsim"`.
2. Add the IP's `*_funcsim.vhd` (Vivado generates these from the .xci)
   to the verilog/vhdl source list.
3. Update `flows-vivado-mcdma/Makefile` to remove the `sim` target's
   error message and call into the new test infra.
