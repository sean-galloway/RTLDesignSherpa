# Document Information

This is the operator / developer guide for the Nexys A7 **RAPIDS
Characterization** project (`projects/NexysA7/rapids_characterization`). It
explains what the project characterizes, how the harness works, how to build /
simulate / program / run it, and how the harness CSR is configured.

The device under test is the **RAPIDS beats DMA** (`rapids_beats_top`, from
`projects/components/dmas/rapids/`). This guide documents how the harness drives
it and the harness control surface — not the DMA core's internals.

---

## References

| Source | Title |
|--------|-------|
| RTL Design Sherpa | `README.md` (project overview + quick start) |
| RTL Design Sherpa | `docs/rapids_characterization_findings.md` (architecture, timing, golden CRC) |
| RTL Design Sherpa | `flows-rapids-beats/host/README.md` (AXIL word map + campaign semantics) |
| RTL Design Sherpa | `reports/perf/README.md` (8-channel line-rate performance) |
| RTL Design Sherpa | `bin/TBClasses/` (shared harness / RegisterMap collateral) |
| ARM | AMBA AXI4 / AXI4-Stream / APB Protocol Specifications |

: Reference documents

---

## Terminology

**SRC / SNK**

The two wholly-separate RAPIDS engines: `rapids_src_beats` reads memory and emits
to the AXIS network; `rapids_snk_beats` receives from the network and writes
memory. They share one APB decode (SRC @ 0x0000, SNK @ 0x1000).

**Beats**

The fixed-quantum transfer variant of RAPIDS. `DATA_WIDTH = 512` (64 bytes per
beat); peak per-direction bandwidth = 64 B × 100 MHz = 6.4 GB/s.

**Region**

The top 4 bits of the host word address (`addr[19:16]`) select one of three
regions: DUT-REG (0), DESC-LOAD (1), HARNESS CSR (2).

**Golden CRC**

The deterministic CRC-32 (Ethernet `0x04C11DB7`, LFSR seed `0xDEADBEEF`) that
both the on-chip checkers and the host golden model compute; a pass is a CRC
match.

---

## Revision History

| Version | Date | Notes |
|---------|------|-------|
| 0.90 | 2026-07-18 | Initial project guide |

: Revision history
