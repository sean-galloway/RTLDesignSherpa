<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# APB Crossbar Micro-Architecture Specification Index

**Component:** APB Crossbar (MxN Interconnect)
**Version:** 1.0
**Date:** 2026-01-03
**Purpose:** Detailed micro-architecture specification for APB Crossbar component

---

## Document Organization

This specification covers the APB Crossbar: a parametric MxN interconnect that routes multiple APB masters to multiple APB slaves with automatic address-based routing and round-robin arbitration.

### Main Documentation

[README.md](README.md)

## Chapter 1: Architecture

[chapters/01_architecture.md](chapters/01_architecture.md)

## Chapter 2: Address Decode and Arbitration

[chapters/02_address_and_arbitration.md](chapters/02_address_and_arbitration.md)

## Chapter 3: RTL Generator

[chapters/03_rtl_generator.md](chapters/03_rtl_generator.md)

---

## Quick Navigation

### For New Users

1. Start with [README.md](README.md) for overview and quick start
2. Read [01_architecture.md](chapters/01_architecture.md) to understand the design
3. Study [02_address_and_arbitration.md](chapters/02_address_and_arbitration.md) for operational details
4. Reference [03_rtl_generator.md](chapters/03_rtl_generator.md) if you need a custom configuration

### For Integration

- **Pre-generated variants:** See [01_architecture.md](chapters/01_architecture.md) Section "Pre-Generated Variants"
- **Custom generation:** See [03_rtl_generator.md](chapters/03_rtl_generator.md) Section "Quick Start"
- **Address mapping:** See [02_address_and_arbitration.md](chapters/02_address_and_arbitration.md) Section "Address Decode"
- **Arbitration behavior:** See [02_address_and_arbitration.md](chapters/02_address_and_arbitration.md) Section "Arbitration"

### Common Questions

All answered in [README.md](README.md), section "Common Questions".

---

## Visual Assets

Every diagram in this specification is checked in as both source and rendered output:

- **Source Files:**
  - `assets/graphviz/*.gv` - Graphviz source diagrams
  - `assets/wavedrom/*.json` - WaveJSON timing diagrams

- **Rendered Files:**
  - `assets/png/*.png` - PNG format (for document generation)

### Architecture Diagrams

1. **APB Crossbar Architecture (2x4 Example)**
   - Source: [assets/graphviz/apbx_xbar_architecture.gv](assets/graphviz/apbx_xbar_architecture.gv)
   - Rendered: [assets/png/apbx_xbar_architecture.png](assets/png/apbx_xbar_architecture.png)

2. **Address Decode Flow**
   - Source: [assets/graphviz/address_decode_flow.gv](assets/graphviz/address_decode_flow.gv)
   - Rendered: [assets/png/address_decode_flow.png](assets/png/address_decode_flow.png)

### Timing Diagrams

1. **Round-Robin Arbitration**
   - Source: [assets/wavedrom/arbitration_round_robin.json](assets/wavedrom/arbitration_round_robin.json)
   - Rendered: [assets/wavedrom/arbitration_round_robin.png](assets/wavedrom/arbitration_round_robin.png)

---

## Component Overview

### Key Features

- **Parametric MxN Configuration:** Any combination of M masters and N slaves (up to 16x16)
- **Automatic Address Decode:** 64KB per slave, simple offset-based routing
- **Round-Robin Arbitration:** Per-slave fair arbitration, no master starvation
- **Back-to-Back Transactions:** Accepted without master-side idle
  cycles, though they do not overlap inside the fabric (10 pclk cycles
  each for M = 1, 11 for arbitrated variants; one more than that
  variant's single-transfer latency — see HAS 5.2)
- **Grant Persistence:** Grant held through transaction completion
- **RTL Generation:** Python-based generator for custom configurations

### Pre-Generated Variants

| Module | M×N | Use Case |
|--------|-----|----------|
| apbx_xbar_1to1 | 1×1 | Passthrough, protocol conversion |
| apbx_xbar_2to1 | 2×1 | Multi-master arbitration |
| apbx_xbar_1to4 | 1×4 | Simple SoC peripheral bus |
| apbx_xbar_2to4 | 2×4 | Typical SoC with CPU+DMA |
| apbx_xbar_2to2_mixed | 2×2 | Mixed APB4/APB5 (s0 APB5) |

### Design Philosophy

**Proven Building Blocks:**
- Built from production-tested `apb4_slave` and `apb4_master` modules
- No new protocol logic - pure composition
- Each component independently verified

**Parametric Generation:**
- Generator creates any MxN configuration
- Pre-generated common variants for fast integration
- Custom variants generated on-demand

**Clean Separation:**
- Master-side: APB slaves convert protocol → cmd/rsp
- Internal: Arbitration + address decoding
- Slave-side: APB masters convert cmd/rsp → protocol

---

## Related Documentation

### Companion Specifications

- **[APB Crossbar HAS](../apbx_xbar_has/apbx_xbar_has_index.md)** - Hardware Architecture Specification (high-level)

### Project-Level

- **PRD.md:** [../../PRD.md](../../PRD.md) - Complete product requirements document
- **CLAUDE.md:** [../../CLAUDE.md](../../CLAUDE.md) - AI assistant integration guide
- **README.md:** [../../README.md](../../README.md) - Quick start guide

### Test Infrastructure

- **Test Directory:** `../../dv/tests/` - CocoTB + pytest test suite
- **Test Results:** All pre-generated variants 100% passing

### RTL

- **Core Modules:** `../../rtl/apbx_xbar_*.sv` - Pre-generated crossbars
- **Wrappers:** `../../rtl/wrappers/` - testbench scaffolds (pclk/presetn only), not integration wrappers
- **Generator:** `../../bin/generate_xbars.py` - Python generator script

---

## Version History

**Version 1.0 (2025-10-25):**
- Initial specification release
- Complete visual documentation (3 diagrams)
- Generator documentation
- All pre-generated variants verified (100% passing)

---

**Last Updated:** 2026-01-03
**Maintained By:** RTL Design Sherpa Project
