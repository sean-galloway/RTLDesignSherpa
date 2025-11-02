# APB Crossbar Visual Documentation

**Component:** APB Crossbar (MxN Interconnect)
**Version:** 1.0
**Status:** Production Ready
**Last Updated:** 2025-10-25

---

## Overview

This directory contains visual documentation for the APB Crossbar component, including architecture diagrams, timing waveforms, and generator documentation.

**Component Purpose:** Parametric MxN APB interconnect connecting multiple masters to multiple slaves with automatic address-based routing and round-robin arbitration.

---

## Documentation Structure

### Main Documentation Files

| Document | Description | Contents |
|----------|-------------|----------|
| [01_architecture.md](01_architecture.md) | Architecture Overview | Top-level block diagram, functional blocks, signal flow, parameters |
| [02_address_and_arbitration.md](02_address_and_arbitration.md) | Address Decode & Arbitration | Address map structure, decode algorithm, round-robin timing |
| [03_rtl_generator.md](03_rtl_generator.md) | RTL Generator Guide | Generator architecture, usage, customization, advanced topics |

### Supporting Documentation

| Document | Location | Description |
|----------|----------|-------------|
| PRD.md | [../../PRD.md](../../PRD.md) | Complete product requirements document |
| CLAUDE.md | [../../CLAUDE.md](../../CLAUDE.md) | AI assistant integration guide |
| README.md | [../../README.md](../../README.md) | Quick start guide |

---

## Visual Assets

### Architecture Diagrams

| Diagram | Format | Description |
|---------|--------|-------------|
| [apb_xbar_architecture](apb_xbar_spec/assets/graphviz/apb_xbar_architecture.gv) | Graphviz | 2x4 crossbar showing master-side slaves, arbitration, slave-side masters |
| [address_decode_flow](apb_xbar_spec/assets/graphviz/address_decode_flow.gv) | Graphviz | Step-by-step address decode example (0x10023456 → Slave 2) |

**Rendered Formats:**
- PNG: `assets/png/*.png` (for markdown embedding)
- SVG: `assets/svg/*.svg` (for web viewing, scalable)

### Timing Diagrams

| Diagram | Format | Description |
|---------|--------|-------------|
| [arbitration_round_robin](apb_xbar_spec/assets/wavedrom/arbitration_round_robin.json) | WaveJSON | 2 masters competing for Slave 0 with round-robin arbitration |

**Rendered Format:**
- PNG: `assets/png/arbitration_round_robin.png`

---

## Quick Start

### For New Users

1. **Understand the Architecture**
   - Read [01_architecture.md](01_architecture.md)
   - Study the architecture diagram
   - Understand master-side/slave-side protocol conversion

2. **Learn Address Decode & Arbitration**
   - Read [02_address_and_arbitration.md](02_address_and_arbitration.md)
   - Study address decode flow diagram
   - Study arbitration timing diagram

3. **Generate Custom Crossbar (if needed)**
   - Read [03_rtl_generator.md](03_rtl_generator.md)
   - Use pre-generated variants (1to1, 2to1, 1to4, 2to4) if possible
   - Run generator for custom MxN configurations

4. **Integrate Into Your Design**
   - See integration examples in [CLAUDE.md](../../CLAUDE.md)
   - Reference complete specification in [PRD.md](../../PRD.md)

### For Existing Users

**Need a Crossbar?**
- 1 master, N slaves → Use `apb_xbar_1toN` or generate
- 2 masters, N slaves → Use `apb_xbar_2toN` or generate
- M masters, N slaves → Generate with `generate_xbars.py`

**Understanding Behavior?**
- Address decode issues → See [02_address_and_arbitration.md](02_address_and_arbitration.md#address-decode)
- Arbitration questions → See [02_address_and_arbitration.md](02_address_and_arbitration.md#arbitration)

**Modifying/Generating?**
- Generator usage → See [03_rtl_generator.md](03_rtl_generator.md)

---

## Directory Structure

```
docs/apb_xbar_spec/
├── README.md                              ← This file
├── 01_architecture.md                     ← Architecture overview
├── 02_address_and_arbitration.md          ← Decode & arbitration details
├── 03_rtl_generator.md                    ← Generator documentation
└── assets/
    ├── graphviz/                          ← Source diagrams
    │   ├── apb_xbar_architecture.gv
    │   └── address_decode_flow.gv
    ├── wavedrom/                          ← Source timing diagrams
    │   └── arbitration_round_robin.json
    ├── svg/                               ← Rendered SVG (scalable)
    │   ├── apb_xbar_architecture.svg
    │   └── address_decode_flow.svg
    └── png/                               ← Rendered PNG (embedded)
        ├── apb_xbar_architecture.png
        ├── address_decode_flow.png
        └── arbitration_round_robin.png
```

---

## Key Concepts

### 1. Architecture

**Three-Stage Design:**
1. **Master-Side:** APB slaves convert protocol → cmd/rsp
2. **Internal Logic:** Address decode + arbitration + response routing
3. **Slave-Side:** APB masters convert cmd/rsp → protocol

**Why This Design?**
- Reuses proven `apb_slave` and `apb_master` components
- Clean separation of concerns
- Scalable to any MxN configuration

### 2. Address Decode

**Fixed 64KB Per Slave:**
```
Slave 0: BASE_ADDR + 0x00000 - 0x0FFFF
Slave 1: BASE_ADDR + 0x10000 - 0x1FFFF
Slave 2: BASE_ADDR + 0x20000 - 0x2FFFF
...
```

**Decode Formula:**
```
offset = PADDR - BASE_ADDR
slave_index = offset[19:16]  // Divide by 64KB
```

**See:** [02_address_and_arbitration.md](02_address_and_arbitration.md#address-decode)

### 3. Arbitration

**Per-Slave Round-Robin:**
- Each slave has independent arbiter
- Priority rotates after each grant
- Grant persists through transaction completion
- No master starvation

**See:** [02_address_and_arbitration.md](02_address_and_arbitration.md#arbitration)

### 4. RTL Generation

**All Generator Code in Component Area:**
- **Convenience Wrapper:** `bin/generate_xbars.py` (top-level script)
- **Core Generator:** `bin/apb_xbar_generator.py` (library implementation)

**Usage:**
```bash
# Generate standard variants
python generate_xbars.py

# Generate custom 3x6 crossbar
python generate_xbars.py --masters 3 --slaves 6
```

**See:** [03_rtl_generator.md](03_rtl_generator.md)

---

## Common Questions

### Q: Which pre-generated variant should I use?

**Decision Tree:**
```
1 master, 1 slave  → apb_xbar_1to1 (passthrough)
1 master, 4 slaves → apb_xbar_1to4 (address decode only)
2 masters, 1 slave → apb_xbar_2to1 (arbitration only)
2 masters, 4 slaves → apb_xbar_2to4 (full crossbar)
Other MxN          → Generate with generate_xbars.py
```

### Q: How do I change the base address?

**At Instantiation:**
```systemverilog
apb_xbar_1to4 #(
    .BASE_ADDR(32'h8000_0000)  // Override default 0x10000000
) u_xbar (...);
```

**Or Generate with Custom Base:**
```bash
python generate_xbars.py --masters 2 --slaves 4 --base-addr 0x80000000
```

### Q: Can I change per-slave address sizes?

**No (Current Limitation):** Each slave is fixed at 64KB.

**Workarounds:**
1. Use multiple crossbars with different BASE_ADDR
2. Modify generator's decode logic (advanced)
3. Address translation in slaves

**See:** [03_rtl_generator.md#limitations](03_rtl_generator.md#generator-limitations-and-future-work)

### Q: How does arbitration work with 3+ masters?

**Round-Robin Example (4 Masters, Same Slave):**
```
Initial priority: M0
Transaction 1: M0 requests → M0 granted → Priority rotates to M1
Transaction 2: M0, M1, M2 request → M1 granted → Priority rotates to M2
Transaction 3: M0, M3 request → M2 skipped (not requesting) → M3 granted → Priority rotates to M0
Transaction 4: M0, M1 request → M0 granted → Priority rotates to M1
```

**Key:** Priority rotates after each grant, ensuring fairness.

**See:** [02_address_and_arbitration.md#arbitration](02_address_and_arbitration.md#arbitration-example-walkthrough)

### Q: What's the throughput?

**Single Master:**
- Zero-bubble (back-to-back transactions without gaps)
- Limited only by slave PREADY response time

**Multiple Masters (Same Slave):**
- Fair sharing: Each master gets ~1/M bandwidth
- Example: 2 masters = 50% each, 4 masters = 25% each

**Multiple Masters (Different Slaves):**
- Full parallelism: Each master gets 100% of its target slave
- Total system bandwidth = NUM_SLAVES × slave_bandwidth

**See:** [02_address_and_arbitration.md#performance](02_address_and_arbitration.md#performance-characteristics)

---

## Regenerating Diagrams

### Graphviz Diagrams (Architecture, Address Decode)

```bash
cd assets/graphviz/

# Generate SVG
dot -Tsvg apb_xbar_architecture.gv -o ../svg/apb_xbar_architecture.svg
dot -Tsvg address_decode_flow.gv -o ../svg/address_decode_flow.svg

# Generate PNG
dot -Tpng apb_xbar_architecture.gv -o ../png/apb_xbar_architecture.png
dot -Tpng address_decode_flow.gv -o ../png/address_decode_flow.png
```

### WaveJSON Diagrams (Timing)

```bash
cd assets/wavedrom/

# Generate PNG
wavedrom-cli -i arbitration_round_robin.json -p ../png/arbitration_round_robin.png
```

---

## Version History

**Version 1.0 (2025-10-25):**
- Initial visual documentation release
- 3 main documentation files
- 2 Graphviz architecture diagrams
- 1 WaveJSON timing diagram
- RTL generator documentation

---

## Maintainers

**RTL Design Sherpa Project**

**Questions or Issues:**
1. Check this documentation first
2. Review [PRD.md](../../PRD.md) for complete specification
3. Review [CLAUDE.md](../../CLAUDE.md) for integration guidance
4. Open GitHub issue if problem persists

---

**Last Updated:** 2025-10-25
**Version:** 1.0
**Status:** Production Ready
