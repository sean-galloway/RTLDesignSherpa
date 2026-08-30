# Document Information

This is the operator / developer guide for the Nexys A7 **STREAM
Characterization** project (`projects/NexysA7/stream_characterization`). It
explains what the project characterizes, how the harness works, how to build /
simulate / program / run it, and how the harness CSR is configured.

The device under test is the in-house **STREAM scatter-gather DMA**
(`stream_top_ch8`, from `projects/components/dmas/stream/`). This guide documents
how the harness drives and measures it — not the DMA core's internals. The
STREAM core's own architecture specifications (HAS/MAS) live under
`projects/components/dmas/stream/docs/`.

---

## References

| Source | Title |
|--------|-------|
| RTL Design Sherpa | `README.md`, `PORT_MAP.md`, `DMA_UTILIZATION_MEASUREMENT.md` |
| RTL Design Sherpa | `flows-stream-bridge/host/ADDRESS_MAP.md` (bridge + CSR map) |
| RTL Design Sherpa | `reports/{perf,compression,area,ext_addressing}/README.md` |
| RTL Design Sherpa | `bin/TBClasses/harness/` (shared UART-char collateral) |
| ARM | AMBA AXI4 / AXI4-Lite / APB Protocol Specifications |

: Reference documents

---

## Terminology

**Flow**

One cell of the characterization matrix — a `{DMA} × {bridge}` pairing built as a
`flows-<dma>-<bridge>/` directory.

**Harness CSR**

The instrumentation register block (`harness_csr`) that arms the pattern
generators, latency model, bus meters, and CRC checkers around the DUT.

**MonBus**

STREAM's internal 64-bit monitoring bus; its packets are drained to `debug_sram`
(bulk trace) and `stream_err` (IRQ FIFO), and optionally compressed.

**Observer**

`axi4_dma_observer` — non-perturbing valid/ready snoops on the DMA payload
buses that feed the utilization buckets and the compression counters.

---

## Revision History

| Version | Date | Notes |
|---------|------|-------|
| 0.90 | 2026-07-18 | Initial project guide |

: Revision history
