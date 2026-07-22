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

**Version:** 0.1
**Last Updated:** 2025-10-19
**Purpose:** AI-specific guidance for working with HIVE subsystem

---

## Quick Context

**What:** HIVE (Hierarchical Intelligent Vector Environment) - Distributed control and monitoring subsystem for RAPIDS/Delta Network
**Status:** Early Specification Phase (v0.1)
**Your Role:** Help users understand hierarchical RISC-V architecture, distributed monitoring, and network reconfiguration

**📖 Complete Specification:** `projects/components/hive/docs/hive_spec/` ← **Always reference this for technical details**

---

## Critical Rules for This Component

### Rule #1: Attribution Format for Git Commits

**IMPORTANT:** When creating git commit messages for HIVE documentation or code:

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Rationale:** HIVE is a distributed control system specification where Claude provides documentation organization and implementation assistance, not co-authorship of the underlying design concepts.

### Rule #2: Always Reference Complete Specification

**This subsystem has extensive documentation in** `projects/components/hive/docs/hive_spec/`

**Before answering technical questions:**
```bash
# Check complete specification
ls projects/components/hive/docs/hive_spec/
cat projects/components/hive/docs/hive_spec/hive_index.md
cat projects/components/hive/docs/hive_spec/ch02_blocks/00_overview.md
# Full single-file spec (block/interface/programming detail):
cat projects/components/hive/docs/hive_specification.md
```

**Your answer should:**
1. Provide direct answer/code
2. **Then link to detailed spec:** "See `projects/components/hive/docs/hive_spec/{file}.md` for complete specification"

### Rule #3: HIVE System Context

**IMPORTANT:** HIVE is part of the larger RAPIDS/Delta/HIVE ecosystem:

1. **RAPIDS** - DMA engine with inband descriptor injection
   - Virtual Tile 16 in Delta Network
   - Controlled by HIVE-C via CDA packets

2. **Delta Network** - 4×4 mesh Network-on-Chip
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

**📖 See:** `docs/hive_spec/ch02_blocks/00_overview.md`

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

**📖 See:**
- `docs/hive_spec/ch02_blocks/00_overview.md`
- `docs/hive_specification.md` sections 5-6 (the per-block chapter files 2.1-2.4 are not yet written)

### Q: "How does HIVE-C send descriptors to RAPIDS?"

**A: Inband CDA packet injection via Delta Network:**

```
1. HIVE-C generates 256-bit CDA descriptor
   ↓
2. AXIS master transmits to Delta Network
   - TUSER = 2'b01 (CDA packet type)
   - TDEST = 16 (RAPIDS virtual tile)
   ↓
3. Delta Network routes to Router 12 south port
   ↓
4. RAPIDS receives CDA packet
   - Descriptor engine processes
   - Scheduler activates appropriate data path
```

**Advantages over memory-mapped descriptors:**
- Lower latency (~10-20 cycles vs. 100+)
- No memory bus contention
- Inband delivery through existing network

**📖 See:** `docs/hive_specification.md` section 6 (HIVE-C control software; chapter file 2.1 not yet written)

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

**📖 See:** `docs/hive_specification.md` section 4 (network reconfiguration; chapter file 2.4 not yet written)

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

**📖 See:** `docs/hive_specification.md` section 5 (SERV monitor functionality; chapter file 2.2 not yet written)

---

## Key Documentation Links

### Primary Technical Specification

- `docs/hive_spec/hive_index.md` - Complete specification index
- `docs/hive_spec/ch01_overview/` - Architecture overview
- `docs/hive_spec/ch02_blocks/` - Block specifications (only 00_overview.md written so far)
- `docs/hive_specification.md` - Full single-file specification (interfaces, programming
  models, and performance content; the ch03-ch05 chapter files are not yet written)

### Related Component Specifications

- `projects/components/dmas/rapids/docs/rapids_beats_has/` and `rapids_beats_mas/` - RAPIDS DMA specification (Beats architecture)
- `projects/components/delta/docs/delta_spec/` - Delta Network specification

---

## Documentation Generation

### Generating PDF/DOCX from Specification

**Tool:** `bin/md_to_docx.py` (repo root)

Use this tool to convert the linked specification index into a single all-inclusive PDF or DOCX file. The preferred entry point is the wrapper script `projects/components/hive/docs/generate_pdf.sh`. Note: no built HIVE_Specification docx/pdf is checked in - generate it on demand.

**Basic Usage:**

```bash
# Preferred: use the wrapper script (from the docs/ directory)
cd projects/components/hive/docs
./generate_pdf.sh --rev 0.25
# Outputs: HIVE_Specification_v0.25.docx and HIVE_Specification_v0.25.pdf

# Direct md_to_docx.py invocation (from repo root)
python bin/md_to_docx.py \
    projects/components/hive/docs/hive_spec/hive_index.md \
    -o projects/components/hive/docs/HIVE_Specification_v0.25.docx \
    --toc \
    --title-page \
    --pdf
```

**Key Features:**
- **Recursive Collection:** Follows all markdown links in the index file
- **Heading Demotion:** Automatically adjusts heading levels for included files
- **Table of Contents:** `--toc` flag generates automatic ToC
- **Title Page:** `--title-page` flag creates title page from first heading
- **PDF Export:** `--pdf` flag generates both DOCX and PDF
- **Image Support:** Resolves images relative to source directory
- **Template Support:** Optional custom DOCX/DOTX template via `-t` flag

**Common Workflow:**

```bash
# 1. Update version number in index file (hive_index.md)
# 2. Generate documentation (from repo root)
python bin/md_to_docx.py \
    projects/components/hive/docs/hive_spec/hive_index.md \
    -o projects/components/hive/docs/HIVE_Specification_v0.25.docx \
    --toc --title-page --pdf

# 3. Output files created:
#    - HIVE_Specification_v0.25.docx
#    - HIVE_Specification_v0.25.pdf (if --pdf used)
```

**Debug Mode:**

```bash
# Generate debug markdown to see combined output
python bin/md_to_docx.py \
    projects/components/hive/docs/hive_spec/hive_index.md \
    -o output.docx \
    --debug-md

# This creates debug.md showing the complete merged content
```

**Tool Requirements:**
- Python 3.6+
- Pandoc installed and in PATH
- For PDF generation: LaTeX (e.g., texlive) or use Pandoc's built-in PDF writer

**📖 See:** `bin/md_to_docx.py` (repo root) for complete implementation details

---

## PDF Generation Location

**IMPORTANT: PDF files should be generated in the docs directory:**
```
projects/components/hive/docs/
```

**Quick Command:** Use the provided shell script:
```bash
cd projects/components/hive/docs
./generate_pdf.sh
```

The shell script will automatically:
1. Use the md_to_docx.py tool from bin/
2. Process the hive_spec index file
3. Generate both DOCX and PDF files in the docs/ directory
4. Create table of contents and title page

**📖 See:** `bin/md_to_docx.py` for complete implementation details

---

## Remember

1. 📖 **Link to detailed spec** - `docs/hive_spec/` has complete architecture
2. 🏷️ **Use correct attribution** - "Documentation and implementation support by Claude"
3. 🎯 **Hierarchical architecture** - HIVE-C (master) + 16 SERV monitors (agents)
4. 🔌 **Virtual tiles** - RAPIDS=16, HIVE-C=17 in Delta Network topology
5. 📊 **Four packet types** - PKT_DATA, CDA, PKT_CONFIG, PKT_STATUS
6. 🔄 **Configuration contexts** - 4 virtual routing modes with atomic switching
7. 📡 **Control network** - Separate star topology for HIVE-C ↔ SERV communication
8. 🎛️ **Monitoring** - Per-tile traffic stats, congestion detection, error reporting

---

**Version:** 0.1
**Last Updated:** 2025-10-19
**Maintained By:** RTL Design Sherpa Project
