# Bridge Graphviz Block Diagrams

This directory contains Graphviz source files (.gv) and generated PNG diagrams for Bridge crossbar configurations.

## Files

### Source Files (.gv)
- **`bridge_2x2.gv`** - 2 masters × 2 slaves configuration
- **`bridge_1x4.gv`** - 1 master × 4 slaves configuration

### Generated Images (.svg)
- **`bridge_2x2.png`** - 2×2 block diagram (427 KB)
- **`bridge_1x4.png`** - 1×4 block diagram (518 KB)

## Regenerating Diagrams

### Prerequisites
- Graphviz installed (`sudo apt install graphviz` on Ubuntu/Debian)
- `dot` command available in PATH

### Generate All Diagrams

```bash
# From this directory
make all

# Or manually
dot -Tpng bridge_2x2.gv -o bridge_2x2.png
dot -Tpng bridge_1x4.gv -o bridge_1x4.png
```

### Generate Single Diagram

```bash
# 2x2 configuration
dot -Tpng bridge_2x2.gv -o bridge_2x2.png

# 1x4 configuration
dot -Tpng bridge_1x4.gv -o bridge_1x4.png
```

### Generate SVG (for web/docs)

```bash
dot -Tsvg bridge_2x2.gv -o bridge_2x2.svg
dot -Tsvg bridge_1x4.gv -o bridge_1x4.svg
```

### Generate PDF (for documentation)

```bash
dot -Tpdf bridge_2x2.gv -o bridge_2x2.pdf
dot -Tpdf bridge_1x4.gv -o bridge_1x4.pdf
```

## Diagram Contents

### bridge_2x2.gv (2 Masters × 2 Slaves)

Shows:
- 2 AXI4 masters (CPU, DMA)
- 2 AXI4 slaves (DDR at 0x0000_0000, SRAM at 0x1000_0000)
- Address decode logic (AW and AR separate)
- Per-slave arbiters (4 total: 2 AW + 2 AR)
- Data multiplexing (W follows AW, R follows AR)
- Response demultiplexing (B and R routing)
- 5-channel AXI4 protocol flow

**Use Case:** Typical dual-master system with memory hierarchy

### bridge_1x4.gv (1 Master × 4 Slaves)

Shows:
- 1 AXI4 master (CPU)
- 4 AXI4 slaves (DDR, SRAM, Peripherals, Flash)
- Address decode logic for 1 GB address space
- Degenerate arbitration (pass-through with 1 master)
- Full address map with 256 MB regions
- All 5 AXI4 channels

**Use Case:** Single-core CPU accessing multiple memory-mapped resources

## Diagram Style

**Colors:**
- **Light green** - Masters (external)
- **Light coral/pink** - Slaves (external)
- **Light yellow** - Internal decode/arbiter logic
- **Blue** - Write path (AW, W, B channels)
- **Green** - Read path (AR, R channels)
- **Purple** - Response routing

**Nodes:**
- **Rounded boxes** - Functional blocks
- **Double octagon** - External masters (single master config)
- **Ellipse** - Clock/reset sources
- **Note boxes** - Annotations and configuration

**Edges:**
- **Bold solid** - Primary data/control flow
- **Dotted** - Secondary connections (multiplexed)
- **Dashed** - Clock/reset distribution

## Adding New Configurations

To add a new configuration (e.g., 4×2):

1. Copy an existing .gv file:
   ```bash
   cp bridge_2x2.gv bridge_4x2.gv
   ```

2. Edit the new file:
   - Update title and module name
   - Adjust NUM_MASTERS and NUM_SLAVES
   - Add/remove master and slave nodes
   - Update arbiter count (2 × NUM_SLAVES)
   - Adjust address map ranges

3. Generate PNG:
   ```bash
   dot -Tpng bridge_4x2.gv -o bridge_4x2.png
   ```

4. Link from documentation:
   ```markdown
   ![Bridge 4x2 Block Diagram](../assets/graphviz/bridge_4x2.svg)
   ```

## Referenced In Documentation

These diagrams are referenced in:
- `ch01_overview/01_introduction.md` - Overview chapter
- `ch03_generated_rtl/01_module_structure.md` - Module structure chapter

## Tools

**Graphviz Version:** Any recent version (tested with 2.43+)

**Alternative Viewers:**
- Online: http://www.webgraphviz.com/ (paste .gv content)
- VS Code: Install "Graphviz Preview" extension
- Command line: `xdg-open bridge_2x2.png` (Linux)

## Notes

- PNG files are version controlled for easy documentation viewing
- Source .gv files are the authoritative source
- Regenerate PNGs after any .gv file changes
- Keep diagrams up-to-date with CSV generator features

---

**Last Updated:** 2025-10-26
**Maintainer:** RTL Design Sherpa Project
