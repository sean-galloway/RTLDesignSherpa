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

# Claude Code Guide: HIVE Component

**Version:** 0.2
**Last Updated:** 2026-10-12
**Purpose:** AI-specific guidance for working with HIVE subsystem

---

## Quick Context

**What:** HIVE (Hierarchical Intelligent Vector Environment) - Distributed control and monitoring subsystem for RAPIDS/Delta Network
**Status:** HAS/MAS v0.2 published 2026-10-13; Phase 1 RTL in progress (descriptor_gen, axis_cda_master, ctrl_network CN-01..03 verified at gate/func; remaining blocks + the CN-04 rotation issue tracked in vault hive-serv TASK-000)
**Your Role:** Help users understand hierarchical RISC-V architecture, distributed monitoring, and network reconfiguration

**Primary Specifications:**
- HAS (`projects/components/compute-eng-ip/hive-serv/docs/hive_has/`) — external contract
- MAS (`projects/components/compute-eng-ip/hive-serv/docs/hive_mas/`) — block-level implementation intent

---

## Critical Rules for This Component

### Rule #2: Always Reference the Specifications

**This subsystem's technical documentation lives in:**
- `projects/components/compute-eng-ip/hive-serv/docs/hive_has/` — architecture, interfaces, packet formats, programming model
- `projects/components/compute-eng-ip/hive-serv/docs/hive_mas/` — module trees, clocking/reset, cycle-level behavior, verification hooks

**Before answering technical questions:**
```bash
ls projects/components/compute-eng-ip/hive-serv/docs/hive_has/
ls projects/components/compute-eng-ip/hive-serv/docs/hive_mas/
cat projects/components/compute-eng-ip/hive-serv/docs/hive_has/hive_has_index.md
```

**Your answer should:**
1. Provide direct answer/code
2. **Then link to the spec:** "See `projects/components/compute-eng-ip/hive-serv/docs/hive_has/{file}.md` (or `hive_mas/`) for the full specification"

### Rule #3: HIVE System Context

**IMPORTANT:** HIVE is part of the larger RAPIDS/Delta/HIVE ecosystem:

1. **RAPIDS** - DMA engine with inband descriptor injection
   - Virtual Tile 16 in Delta Network
   - Controlled by HIVE-C via CDA packets

2. **Delta Network** - 4×4 mesh Network-on-Chip (`projects/components/fabric-gen-ip/delta/`)
   - 16 physical compute tiles (0-15)
   - 2 virtual tiles (16=RAPIDS, 17=HIVE-C)
   - Four packet types (PKT_DATA, CDA, PKT_CONFIG, PKT_STATUS)

3. **HIVE** - Distributed control and monitoring
   - HIVE-C master controller (VexRiscv) - Virtual Tile 17
   - 16 SERV monitors (one per physical tile)
   - Control network for HIVE-C ↔ SERV communication
   - Configuration manager for network reconfiguration

**When user mentions HIVE:** Clarify whether they're asking about the entire ecosystem or just the HIVE control subsystem.

---

## Architecture Quick Reference

### Block Organization (HIVE System)

```
HIVE System Architecture
├── Block 1: HIVE-C Master Controller (VexRiscv)
│   ├── VexRiscv "Small" RV32IM core
│   ├── 32KB instruction memory
│   ├── 32KB data memory
│   ├── Descriptor generation (CDA packets)
│   ├── Control network master
│   └── AXIS master (to Delta Network)
│
├── Block 2: SERV Monitors (16 instances)
│   ├── SERV bit-serial RISC-V (RV32I)
│   ├── 2KB instruction + 2KB data memory each
│   ├── Traffic counters (pkt_rx/tx_count)
│   ├── Buffer occupancy monitors
│   ├── Congestion detection logic
│   └── AXIS injector (PKT_CONFIG, PKT_STATUS)
│
├── Block 3: Control Network
│   ├── Star topology (HIVE-C ↔ 16 SERVs)
│   ├── Round-robin arbiter (SERV → HIVE-C)
│   ├── Command delivery (HIVE-C → SERV)
│   └── Status aggregation (SERV → HIVE-C)
│
└── Block 4: Configuration Manager
    ├── 4 virtual configuration contexts
    ├── Context 0: Systolic Mode
    ├── Context 1: Packet-Switched Mesh (XY routing)
    ├── Context 2: Tree Reduction
    ├── Context 3: Custom/Debug
    └── Atomic topology switching protocol
```

**See:**
- `docs/hive_has/ch03_architecture/01_subsystem_architecture.md` (block specs)
- `docs/hive_mas/ch02_blocks/` (module trees)

---

## Common User Questions and Responses

### Q: "What's the difference between HIVE-C and SERV monitors?"

**A: Hierarchical control architecture:**

| Aspect | HIVE-C Controller | SERV Monitors (16×) |
|--------|-------------------|---------------------|
| **Core** | VexRiscv RV32IM | SERV RV32I (bit-serial) |
| **Resources** | 1,400 LUTs, 8 BRAM | 125 LUTs, 1 BRAM each |
| **Role** | Global coordination | Per-tile monitoring |
| **Responsibilities** | Descriptor scheduling, network reconfiguration, performance aggregation | Traffic monitoring, congestion detection, local packet injection |
| **Network Position** | Virtual Tile 17 | Co-located with physical tiles 0-15 |

**Key Point:** HIVE-C is the master controller, SERV monitors are lightweight per-tile agents.

**See:**
- `docs/hive_has/ch03_architecture/01_subsystem_architecture.md`
- `docs/hive_mas/ch02_blocks/02_hive_c_controller.md` and `03_serv_monitor.md`

### Q: "How does HIVE-C send descriptors to RAPIDS?"

**A: Inband CDA packet injection via Delta Network:**

```
1. HIVE-C generates 256-bit CDA descriptor
   ↓
2. AXIS master transmits to Delta Network
   - TUSER = 2'b01 (CDA packet type)
   - TDEST = 16 (RAPIDS virtual tile)
   ↓
3. Delta Network routes to RAPIDS (virtual tile 16)
   ↓
4. RAPIDS receives CDA packet
   - Descriptor engine processes
   - Scheduler activates appropriate data path
```

**Advantages over memory-mapped descriptors:**
- Lower latency (~10-20 cycles vs. 100+)
- No memory bus contention
- Inband delivery through existing network

**See:**
- `docs/hive_has/ch04_interfaces/02_packet_formats.md` (descriptor format)
- `docs/hive_mas/ch04_behavior/01_descriptor_injection_cycle.md` (cycle-by-cycle)

### Q: "How does network reconfiguration work?"

**A: Atomic context switching via Configuration Manager:**

```
Switching Sequence:
1. HIVE-C issues CONFIG_PREPARE command
   - Target tiles flush in-flight packets
   - Routers enter quiescent state (5-10 cycles)

2. HIVE-C broadcasts SET_ROUTING_MODE (PKT_CONFIG packet)
   - TUSER = 2'b10 (PKT_CONFIG type)
   - All tiles simultaneously update mode register
   - Context switch occurs in single cycle

3. HIVE-C issues CONFIG_ACTIVATE command
   - Tiles resume operation with new routing
   - Total latency: 10-20 cycles (deterministic)
```

**Virtual Configuration Contexts:**
- Context 0: Systolic Mode (nearest-neighbor)
- Context 1: Packet-Switched Mesh (XY routing)
- Context 2: Tree Reduction (hierarchical aggregation)
- Context 3: Custom/Debug (user-programmable)

**See:**
- `docs/hive_has/ch05_programming_model/04_network_reconfiguration.md` (workflow)
- `docs/hive_mas/ch04_behavior/03_context_switch_sequence.md` (FSM/cycles)

### Q: "What do SERV monitors track?"

**A: Per-tile traffic and congestion metrics:**

**Counters (32-bit, wrapping):**
- `pkt_rx_count[4]` - Received packets per direction (N/S/E/W)
- `pkt_tx_count[4]` - Transmitted packets per direction
- `pkt_local_inject` - Packets injected by local compute element
- `pkt_local_consume` - Packets consumed by local compute element
- `buffer_overflow_count` - FIFO overflow events
- `stall_cycles` - Cycles with valid packet waiting for credits

**Real-Time Metrics:**
- `buffer_occupancy[4]` - Current FIFO fill levels (8-bit per direction)
- `congestion_flag` - Boolean indicating occupancy > threshold
- `error_flags` - Parity errors, protocol violations

**Reporting:**
- Periodic status to HIVE-C (every 1000 cycles, configurable)
- Immediate alerts on congestion/errors via PKT_STATUS packets

**See:**
- `docs/hive_has/ch03_architecture/01_subsystem_architecture.md` (Block 2)
- `docs/hive_mas/ch02_blocks/03_serv_monitor.md` (counter/tap design)

---

## Key Documentation Links

### Primary Technical Specifications

- `docs/hive_has/hive_has_index.md` - Hardware Architecture Specification index
- `docs/hive_mas/hive_mas_index.md` - Micro-Architecture Specification index
- `docs/hive_has/ch04_interfaces/` - Interfaces, packet formats, register maps
- `docs/hive_mas/ch04_behavior/` - Cycle-level behavior of key operations

### Related Component Specifications

- `projects/components/dma-ip/rapids/docs/rapids_beats_has/` and `rapids_beats_mas/` - RAPIDS DMA specification (Beats architecture)
- `projects/components/fabric-gen-ip/delta/docs/delta_has/` and `delta_mas/` - Delta Network specification

---

## Documentation Generation

### Generating PDF/DOCX from the Specifications

**Tool:** `bin/md_to_docx.py` (repo root) via the wrapper scripts:

```bash
cd projects/components/compute-eng-ip/hive-serv/docs
./generate_has_pdf.sh            # HIVE_HAS_v0.2.docx / .pdf
./generate_mas_pdf.sh            # HIVE_MAS_v0.2.docx / .pdf
```

The scripts check dependencies (python-docx, PyYAML, pandoc, LibreOffice),
then invoke `md_to_docx.py` with the book's index, styles yaml, title page,
ToC, and page breaks. Built books are checked in alongside their sources.

**Requirements:** Python 3.6+, pandoc, LibreOffice (PDF export), and the
repo's `bin/md_to_docx.py`.

**Debug mode** (merged markdown inspection):

```bash
python bin/md_to_docx.py \
    projects/components/compute-eng-ip/hive-serv/docs/hive_has/hive_has_index.md \
    -o output.docx --debug-md
```

---

## Remember

1. **Link to the specs** - `docs/hive_has/` (architecture) and `docs/hive_mas/` (implementation intent)
2. **Hierarchical architecture** - HIVE-C (master) + 16 SERV monitors (agents)
3. **Virtual tiles** - RAPIDS=16, HIVE-C=17 in Delta Network topology
4. **Four packet types** - PKT_DATA, CDA, PKT_CONFIG, PKT_STATUS (TUSER[1:0])
5. **Configuration contexts** - 4 virtual routing modes with atomic switching
6. **Control network** - Separate star topology for HIVE-C ↔ SERV communication
7. **Monitoring** - Per-tile traffic stats, congestion detection, error reporting
8. **Pre-RTL** - everything is specification; the MAS marks open items explicitly

---

**Version:** 0.2
**Last Updated:** 2026-10-12
**Maintained By:** RTL Design Sherpa Project
