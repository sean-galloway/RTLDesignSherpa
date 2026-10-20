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

# Claude Code Guide: DELTA Component

**Version:** 0.3
**Last Updated:** 2025-10-19
**Purpose:** AI-specific guidance for working with DELTA subsystem

---

## Quick Context

**What:** DELTA (Distributed Execution Layer for Tensor Acceleration) - Mesh Network-on-Chip with intelligent packet routing
**Status:** Design draft (v0.3) — NOT implemented in this tree; the live mesh cell RTL exists under `projects/components/fabric-gen-ip/delta/` (see the README in this directory)
**Your Role:** Help users understand NoC architecture, routing algorithms, and system integration

**Complete Specification:** `projects/components/noc-ip/delta_spec/` ← **Always reference this for technical details**

---

## Critical Rules for This Component

### Rule #2: Always Reference Complete Specification

**This subsystem has extensive documentation in** `projects/components/noc-ip/delta_spec/`

**Before answering technical questions:**
```bash
# Check complete specification
ls projects/components/noc-ip/delta_spec/
cat projects/components/noc-ip/delta_spec/delta_index.md
cat projects/components/noc-ip/delta_spec/ch02_blocks/01_router_architecture.md
```

**Your answer should:**
1. Provide direct answer/code
2. **Then link to detailed spec:** "See `projects/components/noc-ip/delta_spec/{file}.md` for complete specification"

### Rule #3: This NoC draft vs. the live Delta AXIS crossbar (fabric-gen-ip)

**2026-10-12 the two "deltas" were separated physically:**

1. **DELTA Network** (the design draft in THIS directory)
   - Location: `projects/components/noc-ip/delta_spec/`
   - 4×4 mesh topology with routers, virtual channels, XY routing
   - Four packet types (DATA, DESC, CONFIG, STATUS)
   - **No RTL exists in this NoC draft** — aspirational design groundwork for a future NoC; the live Delta mesh cell RTL is in `projects/components/fabric-gen-ip/delta/`

2. **Delta AXIS Crossbar** (the implemented component)
   - Location: `projects/components/fabric-gen-ip/delta/`
   - Python-based AXI4-Stream flat crossbar generator with generated SystemVerilog
   - Flat topology only (tree retired 2026-10-12)

**When the user mentions "delta":** today they almost always mean the working
crossbar in fabric-gen-ip. Treat this NoC draft as reference material — do not
extend it unless the user explicitly says NoC.

---

## Architecture Quick Reference

### Block Organization (DELTA Network)

```
DELTA Network Architecture (4×4 Mesh)
├── 16 Router/Tile Combinations
│   ├── 5-Port Router (N/S/E/W/Local)
│   ├── Network Interface (NI)
│   ├── Packet Classifier
│   ├── Virtual Channel Allocator
│   ├── Crossbar Switch (5×5)
│   ├── SERV Monitor
│   └── Compute Element
│
├── Virtual Tiles
│   ├── Tile 16 (RAPIDS DMA) - via Router 12 south
│   └── Tile 17 (HIVE-C) - via Router 3 north
│
└── Packet Types
    ├── PKT_DATA (00) - Compute traffic
    ├── PKT_DESC (01) - DMA descriptors
    ├── PKT_CONFIG (10) - Configuration
    └── PKT_STATUS (11) - Monitoring
```

**See:** `delta_spec/ch02_blocks/00_block_overview.md`

---

## Common User Questions and Responses

### Q: "How does packet routing work?"

**A: XY dimension-ordered routing:**

```verilog
// X-dimension first, then Y-dimension
if (dest_x < curr_x) route_WEST;
else if (dest_x > curr_x) route_EAST;
else if (dest_y < curr_y) route_NORTH;
else if (dest_y > curr_y) route_SOUTH;
else route_LOCAL;  // Arrived
```

**Key Points:**
- Deadlock-free by construction
- Deterministic paths
- 3-4 cycles per hop latency

**See:** `delta_spec/ch02_blocks/01_router_architecture.md`

### Q: "What's the difference between packet types?"

**A: Four packet types with different routing:**

| Type | TUSER | Source | Destination | Purpose |
|------|-------|--------|-------------|---------|
| PKT_DATA | 00 | RAPIDS/Tiles | RAPIDS/Tiles | Compute data |
| PKT_DESC | 01 | HIVE-C | RAPIDS | DMA descriptors |
| PKT_CONFIG | 10 | HIVE-C/SERV | Routers | Configuration |
| PKT_STATUS | 11 | SERV | HIVE-C | Monitoring |

**See:** `delta_spec/ch01_overview/03_packet_type_routing.md`

### Q: "How do I integrate with RAPIDS DMA?"

**A: RAPIDS connects as virtual tile 16:**

```systemverilog
// RAPIDS TX -> DELTA (via Router 12 south port)
logic [127:0] rapids_tx_tdata;
logic         rapids_tx_tvalid;
logic         rapids_tx_tready;
logic [3:0]   rapids_tx_tdest;  // Target tile 0-15

// DELTA -> RAPIDS RX
logic [127:0] rapids_rx_tdata;
logic         rapids_rx_tvalid;
logic [3:0]   rapids_rx_tid;    // Source tile ID
```

**See:** `delta_spec/ch03_interfaces/03_external_entities.md`

---

## Key Documentation Links

### Primary Technical Specification

- `delta_spec/delta_index.md` - Complete specification index
- `delta_spec/ch01_overview/` - Architecture overview
- `delta_spec/ch02_blocks/` - Block specifications
- `delta_spec/ch03_interfaces/` - Interface specifications
- `delta_spec/ch04_programming_models/` - Programming model
- `delta_spec/ch05_registers/` - Register definitions

### Project Files

- `PRD.md` - Requirements overview (older AXIS crossbar project)
- `README.md` - Quick start guide (older AXIS crossbar project)
- `docs/Delta_Specification_v1.0.pdf` - Rendered specification (built from `delta_spec/` chapters; the original flat v0.25 markdown spec was migrated into the chapter structure and removed)

---

## Documentation Generation

The NoC spec renders via `projects/components/noc-ip/generate_pdf.sh`
(usage in `README.md`, this directory). Rendered DOCX/PDF land in `delta_spec/`.

---

## Remember

1. **Link to detailed spec** - `delta_spec/` has complete architecture
2. **Which delta?** - the live AXIS crossbar is in fabric-gen-ip/delta; this NoC draft is unimplemented design material
3. **Four packet types** - DATA, DESC, CONFIG, STATUS with different routing rules
4. **XY routing** - Deadlock-free dimension-ordered routing
5. **Virtual tiles** - RAPIDS=16, HIVE-C=17 for external entities
6. **Chapter organization** - Follows RAPIDS/STREAM convention

---

**Version:** 0.3
**Last Updated:** 2025-10-19
**Maintained By:** RTL Design Sherpa Project
