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
**Status:** Early Proof of Concept (v0.3)
**Your Role:** Help users understand NoC architecture, routing algorithms, and system integration

**📖 Complete Specification:** `projects/components/delta/docs/delta_spec/` ← **Always reference this for technical details**

---

## Critical Rules for This Component

### Rule #1: Attribution Format for Git Commits

**IMPORTANT:** When creating git commit messages for Delta documentation or code:

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Rationale:** Delta is a network-on-chip specification project where Claude provides documentation organization and implementation assistance, not co-authorship of the underlying design concepts.

### Rule #2: Always Reference Complete Specification

**This subsystem has extensive documentation in** `projects/components/delta/docs/delta_spec/`

**Before answering technical questions:**
```bash
# Check complete specification
ls projects/components/delta/docs/delta_spec/
cat projects/components/delta/docs/delta_spec/delta_index.md
cat projects/components/delta/docs/delta_spec/ch02_blocks/01_router_architecture.md
```

**Your answer should:**
1. Provide direct answer/code
2. **Then link to detailed spec:** "See `projects/components/delta/docs/delta_spec/{file}.md` for complete specification"

### Rule #3: DELTA vs Delta AXI-Stream Crossbar

**IMPORTANT:** There are TWO different Delta projects:

1. **DELTA Network** (Network-on-Chip)
   - Location: `docs/delta_spec/`
   - 4×4 mesh topology with routers
   - Four packet types (DATA, DESC, CONFIG, STATUS)
   - XY routing, virtual channels
   - Integrates with RAPIDS DMA and HIVE control

2. **Delta AXIS Crossbar** (older project files in root)
   - Location: Root level markdown files
   - Simple AXI-Stream crossbar generator
   - Flat and tree topologies
   - Python-based RTL generation

**When user mentions "Delta":** Clarify which project they mean if context is unclear.

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

**📖 See:** `docs/delta_spec/ch02_blocks/00_block_overview.md`

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

**📖 See:** `docs/delta_spec/ch02_blocks/01_router_architecture.md`

### Q: "What's the difference between packet types?"

**A: Four packet types with different routing:**

| Type | TUSER | Source | Destination | Purpose |
|------|-------|--------|-------------|---------|
| PKT_DATA | 00 | RAPIDS/Tiles | RAPIDS/Tiles | Compute data |
| PKT_DESC | 01 | HIVE-C | RAPIDS | DMA descriptors |
| PKT_CONFIG | 10 | HIVE-C/SERV | Routers | Configuration |
| PKT_STATUS | 11 | SERV | HIVE-C | Monitoring |

**📖 See:** `docs/delta_spec/ch01_overview/03_packet_type_routing.md`

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

**📖 See:** `docs/delta_spec/ch03_interfaces/03_external_entities.md`

---

## Key Documentation Links

### Primary Technical Specification

- `docs/delta_spec/delta_index.md` - Complete specification index
- `docs/delta_spec/ch01_overview/` - Architecture overview
- `docs/delta_spec/ch02_blocks/` - Block specifications
- `docs/delta_spec/ch03_interfaces/` - Interface specifications
- `docs/delta_spec/ch04_programming_models/` - Programming model
- `docs/delta_spec/ch05_registers/` - Register definitions

### Project Files

- `PRD.md` - Requirements overview (older AXIS crossbar project)
- `README.md` - Quick start guide (older AXIS crossbar project)
- `docs/Delta_Specification_v1.0.pdf` - Rendered specification (built from `docs/delta_spec/` chapters; the original flat v0.25 markdown spec was migrated into the chapter structure and removed)

---

## Documentation Generation

### Generating PDF/DOCX from Specification

**Tool:** `bin/md_to_docx.py` (repo root)

Use this tool to convert the linked specification index into a single all-inclusive PDF or DOCX file. The preferred entry point is the wrapper script `projects/components/delta/docs/generate_pdf.sh`, which invokes md_to_docx.py with the right asset directories.

**Basic Usage:**

```bash
# Preferred: use the wrapper script (from the docs/ directory)
cd projects/components/delta/docs
./generate_pdf.sh --rev 1.0
# Outputs: Delta_Specification_v1.0.docx and Delta_Specification_v1.0.pdf

# Direct md_to_docx.py invocation (from repo root)
python bin/md_to_docx.py \
    projects/components/delta/docs/delta_spec/delta_index.md \
    -o projects/components/delta/docs/Delta_Specification_v1.0.docx \
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
# 1. Update version number in index file (delta_index.md)
# 2. Generate documentation (from repo root)
python bin/md_to_docx.py \
    projects/components/delta/docs/delta_spec/delta_index.md \
    -o projects/components/delta/docs/Delta_Specification_v1.0.docx \
    --toc --title-page --pdf

# 3. Output files created:
#    - Delta_Specification_v1.0.docx
#    - Delta_Specification_v1.0.pdf (if --pdf used)
```

**Debug Mode:**

```bash
# Generate debug markdown to see combined output
python bin/md_to_docx.py \
    projects/components/delta/docs/delta_spec/delta_index.md \
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
projects/components/delta/docs/
```

**Quick Command:** Use the provided shell script:
```bash
cd projects/components/delta/docs
./generate_pdf.sh --rev 1.0
```

The shell script will automatically:
1. Use the md_to_docx.py tool from bin/
2. Process the delta_spec index file
3. Generate both DOCX and PDF files in the docs/ directory
4. Create table of contents and title page

**📖 See:** `bin/md_to_docx.py` for complete implementation details

---

## Remember

1. 📖 **Link to detailed spec** - `docs/delta_spec/` has complete architecture
2. 🏷️ **Use correct attribution** - "Documentation and implementation support by Claude"
3. 🔀 **Clarify which Delta** - Network-on-Chip (NEW) vs AXIS Crossbar (older)
4. 🎯 **Four packet types** - DATA, DESC, CONFIG, STATUS with different routing rules
5. 🗺️ **XY routing** - Deadlock-free dimension-ordered routing
6. 🔌 **Virtual tiles** - RAPIDS=16, HIVE-C=17 for external entities
7. 📊 **Chapter organization** - Follows RAPIDS/STREAM convention

---

**Version:** 0.3
**Last Updated:** 2025-10-19
**Maintained By:** RTL Design Sherpa Project
