# Document Information

This is the operator / developer guide for the Nexys A7 **DDR2/LPDDR2
Characterization** project (`projects/NexysA7/ddr2-characterization`). It
explains what the project characterizes, how the harness works, how to build /
simulate / program / run it, and how the harness CSR is configured.

The memory controller under test — **pumice** — is separate IP
(`projects/components/memory-controllers/pumice-ddr2-lpddr2`). This guide treats
it as a **black box** driven by the characterization harness; it does not
document the controller's internals.

> **Note:** the project's top-level `README.md` still carries an early
> "skeleton — RTL not yet written" status line. That is stale: the harness,
> host, sim, and both flows are built and running. Trust this guide and the
> RTL/host sources over that status.

---

## References

| Source | Title |
|--------|-------|
| RTL Design Sherpa | `build-perf/host/ADDRESS_MAP.md` (bridge + CSR map) |
| RTL Design Sherpa | `build-perf/bin/README_a7ddrphy.md` (PHY regen) |
| RTL Design Sherpa | `flows-litedram-uart/HARNESS_PLAN.md` (baseline flow) |
| RTL Design Sherpa | `bin/TBClasses/harness/` (shared UART-char collateral) |
| Micron | `MT47H64M16HR-25E` DDR2 SDRAM datasheet |
| ARM | AMBA AXI4 / AXI4-Lite / APB Protocol Specifications |

: Reference documents

---

## Terminology

**DFI**

DDR PHY Interface. The command/data protocol between the memory controller and
the PHY. Here pumice emits a phase-packed flat DFI v2.1 bus.

**a7ddrphy**

LiteDRAM's Artix-7 DDR2 PHY (4:1 serdes, 800 Mbps). Uses Xilinx
OSERDESE2/ISERDESE2/IDELAYE2 and therefore does **not** simulate in Verilator.

**GEAR / DFI_RATE**

The DFI phase count. `GEAR_RATIO = log2(DFI_RATE)`. Must match between the RTL
build and the sim model or reads corrupt.

**Engine**

A master-side AXI4 traffic generator: the write engine emits an LFSR data
pattern; the read engine re-reads and CRC-checks it.

**Leveling**

Firmware-driven a7ddrphy read/write training over the PHY-CSR passthrough
window; there is no hardware leveling FSM.

---

## Revision History

| Version | Date | Notes |
|---------|------|-------|
| 0.90 | 2026-07-18 | Initial project guide |

: Revision history
