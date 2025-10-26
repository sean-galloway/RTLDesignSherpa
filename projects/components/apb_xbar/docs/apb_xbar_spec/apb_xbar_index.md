# APB Crossbar Specification - Table of Contents

**Component:** APB Crossbar (MxN Interconnect)
**Version:** 1.0
**Last Updated:** 2025-10-25
**Status:** Production Ready (All tests passing)

---

## Document Organization

This specification covers the APB Crossbar component - a parametric MxN interconnect for connecting multiple APB masters to multiple APB slaves with automatic address-based routing and round-robin arbitration.

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
2. Read [01_architecture.md](01_architecture.md) to understand the design
3. Study [02_address_and_arbitration.md](02_address_and_arbitration.md) for operational details
4. Reference [03_rtl_generator.md](03_rtl_generator.md) if custom configuration needed

### For Integration

- **Pre-generated variants:** See [01_architecture.md](01_architecture.md) Section "Pre-Generated Variants"
- **Custom generation:** See [03_rtl_generator.md](03_rtl_generator.md) Section "Quick Start"
- **Address mapping:** See [02_address_and_arbitration.md](02_address_and_arbitration.md) Section "Address Decode"
- **Arbitration behavior:** See [02_address_and_arbitration.md](02_address_and_arbitration.md) Section "Arbitration"

### Common Questions

All answered in [README.md](README.md) Section "Common Questions"

---

## Visual Assets

All diagrams referenced in the documentation are available in:

- **Source Files:**
  - `assets/graphviz/*.gv` - Graphviz source diagrams
  - `assets/wavedrom/*.json` - WaveJSON timing diagrams

- **Rendered Files:**
  - `assets/png/*.png` - PNG format (embedded in markdown)
  - `assets/svg/*.svg` - SVG format (web viewing, scalable)

### Architecture Diagrams

1. **APB Crossbar Architecture (2x4 Example)**
   - Source: [assets/graphviz/apb_xbar_architecture.gv](apb_xbar_spec/assets/graphviz/apb_xbar_architecture.gv)
   - SVG: [assets/svg/apb_xbar_architecture.svg](apb_xbar_spec/assets/svg/apb_xbar_architecture.svg)
   - PNG: [assets/png/apb_xbar_architecture.png](apb_xbar_spec/assets/png/apb_xbar_architecture.png)

2. **Address Decode Flow**
   - Source: [assets/graphviz/address_decode_flow.gv](apb_xbar_spec/assets/graphviz/address_decode_flow.gv)
   - SVG: [assets/svg/address_decode_flow.svg](apb_xbar_spec/assets/svg/address_decode_flow.svg)
   - PNG: [assets/png/address_decode_flow.png](apb_xbar_spec/assets/png/address_decode_flow.png)

### Timing Diagrams

1. **Round-Robin Arbitration**
   - Source: [assets/wavedrom/arbitration_round_robin.json](apb_xbar_spec/assets/wavedrom/arbitration_round_robin.json)
   - PNG: [assets/png/arbitration_round_robin.png](apb_xbar_spec/assets/png/arbitration_round_robin.png)

---

## Component Overview

### Key Features

- **Parametric MxN Configuration:** Any combination of M masters and N slaves (up to 16x16)
- **Automatic Address Decode:** 64KB per slave, simple offset-based routing
- **Round-Robin Arbitration:** Per-slave fair arbitration, no master starvation
- **Zero-Bubble Throughput:** Back-to-back transactions without idle cycles
- **Grant Persistence:** Hold grant through transaction completion
- **RTL Generation:** Python-based generator for custom configurations

### Pre-Generated Variants

| Module | M×N | Use Case |
|--------|-----|----------|
| apb_xbar_1to1 | 1×1 | Passthrough, protocol conversion |
| apb_xbar_2to1 | 2×1 | Multi-master arbitration |
| apb_xbar_1to4 | 1×4 | Simple SoC peripheral bus |
| apb_xbar_2to4 | 2×4 | Typical SoC with CPU+DMA |
| apb_xbar_thin | 1×1 | Minimal overhead passthrough |

### Design Philosophy

**Proven Building Blocks:**
- Built from production-tested `apb_slave` and `apb_master` modules
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

### Project-Level

- **PRD.md:** [../../PRD.md](../../PRD.md) - Complete product requirements document
- **CLAUDE.md:** [../../CLAUDE.md](../../CLAUDE.md) - AI assistant integration guide
- **README.md:** [../../README.md](../../README.md) - Quick start guide

### Test Infrastructure

- **Test Directory:** `../../dv/tests/` - CocoTB + pytest test suite
- **Test Results:** All pre-generated variants 100% passing

### RTL

- **Core Modules:** `../../rtl/apb_xbar_*.sv` - Pre-generated crossbars
- **Wrappers:** `../../rtl/wrappers/` - Pre-configured wrappers
- **Generator:** `../../bin/generate_xbars.py` - Python generator script

---

## Version History

**Version 1.0 (2025-10-25):**
- Initial specification release
- Complete visual documentation (3 diagrams)
- Comprehensive generator documentation
- All pre-generated variants verified (100% passing)

---

**Document Generated:** 2025-10-25
**Maintained By:** RTL Design Sherpa Project
