# jtag-axil-agent

**Status:** Scaffold (2026-10-11) — spec pending (HAS ch03/ch04)
**Plane:** config poke — the capability most IP needs ("access to their
configs")

TCK-domain command register file (ADDR / WDATA / RDATA / CTRL with busy
+ error) behind a USER DR chain from `jtag-tap`, plus an AXIL4 master
FSM: one read or write transaction per command, readback shifted out on
TDO. A `gaxi_fifo_sync` skid buffer smooths the TCK-to-fabric pacing so
full fabric throughput is preserved under backpressure (same pattern as
`stream_latency_bridge`).

One agent serves every component on the fabric; consumers mount CSRs,
not debug logic. monlite taps on the agent's own AXIL side observe the
debugger's traffic like any other master's — dogfooded observation.

Reference design: the Xilinx debug-bridge / AXI-over-JTAG pattern, and
Zhang, *RISC-V Architecture and DSP Processor Design* ch8 for the
JTAG-to-internal-register plumbing.
