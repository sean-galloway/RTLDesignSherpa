# flows-vivado-mcdma

FPGA characterization flow for the **Vivado AXI-MCDMA** IP on the
Digilent Nexys A7-100T. Pairs DMA × bridge as `(Vivado MCDMA, in-house
AXIL bridge)` for direct comparison against `flows-stream-bridge`.

## Status: SKELETON

The directory layout, TCL build flow, Makefile, constraints, and a stub
harness are in place. **The harness does not yet drive MCDMA** — the
stub ties off all status outputs and just blinks the heartbeat LED. The
next session will plumb the IP through the framework's instrumentation.

**Validation is FPGA-only** for this flow (no cocotb regression). See
`dv/README.md` for the rationale. The bring-up loop is `make project →
synth → bitstream → program → cmds.sh`.

What works today:

- `make project` — creates the Vivado project, imports `axi_mcdma_0.xci`,
  upgrades the IP, attaches sources and constraints.
- `make synth` — synthesises the top + the MCDMA IP, emits utilization.
- `make bitstream` — builds; the result programs and blinks LEDs but
  does no transfers.

What's still TODO (next pass):

1. **AXIL fabric.** Generalise `axil_decode_5s.sv` → `axil_decode_n.sv`
   in the framework so the bridge can expose a dedicated AXIL output port
   for MCDMA's `s_axi_lite_*` config interface (per the AXIL-port-on-bridge
   discussion).
2. **Three AXI masters.** Wire `m_axi_sg`, `m_axi_mm2s`, `m_axi_s2mm`
   through three `axi_response_delay` queues into the framework's
   pattern-gen / CRC-check slaves.
3. **AXIS loopback.** Tie `m_axis_mm2s_*` → `s_axis_s2mm_*` so MCDMA
   becomes memory-to-memory like STREAM.
4. **IRQ aggregation.** OR the eight `*_chN_introut` signals into
   `harness_csr.i_irq` so the host can poll completion the same way as
   on the STREAM flow.
5. **Host CSR map.** Adapt `host/characterize.py` to MCDMA's
   buffer-descriptor ring format (separate from STREAM's 256-bit
   descriptor format).
6. **Cycle timer hooks.** Drive the harness's first-AR / first-R / last-B
   edge captures from the MCDMA AXI masters so the same `total / r2r /
   w2w` reporting works.

## Directory layout

```
flows-vivado-mcdma/
├── README.md                         this file
├── Makefile                          build/program targets
├── rtl/
│   ├── vivado_mcdma_top.sv           board top (pin I/O + harness)
│   ├── vivado_mcdma_harness.sv       harness wrapper (currently a stub)
│   └── filelists/
│       └── vivado_mcdma_top.f
├── tcl/                              create_project / build_all / program / synth_only
├── constraints/vivado_mcdma_top.xdc  same Nexys A7 pin set as flows-stream-bridge
├── dv/                               see dv/README.md — FPGA-only, no cocotb
├── host/                             host scripts (TBD — copy + adapt from flows-stream-bridge)
├── csv/                              sweep results (committed)
├── plots/                            rendered PNGs (committed)
├── reports/                          Vivado synth/impl reports (committed)
├── bitstream/                        last built .bit (committed)
└── build/                            ephemeral Vivado work (.gitignored)
```

## Vivado IP source of truth

`projects/NexysA7/stream_characterization/rtl-vivado/axi_mcdma_0/` — committed `.xci` and
generated synth/sim products. `tcl/create_project.tcl` imports the
`.xci` so the generated wrapper is rebuilt on each clean run.

## Running

```bash
cd projects/NexysA7/stream_characterization/flows-vivado-mcdma
make project        # creates the Vivado project; fast (~30 s)
make synth          # synth-only check; ~2-3 min
make bitstream      # full P&R; ~10-30 min
make program        # JTAG flash
```

The Makefile sets these env vars for TCL/filelists:
`REPO_ROOT`, `FRAMEWORK_ROOT`, `RTL_VIVADO_ROOT`, `MCDMA_FLOW_ROOT`,
`STREAM_ROOT`, `CONVERTERS_ROOT`, `MISC_ROOT`.
