# Converters Graphviz Block Diagrams

This directory contains Graphviz source files (.gv) and generated PNG diagrams for Converters component modules.

## Files

### Data Width Converters

**Generic Building Blocks:**
- **`axi_data_upsize.gv`** - Narrow→Wide accumulator (128→512 example)
- **`axi_data_dnsize_single.gv`** - Wide→Narrow splitter, single buffer (512→128, 80% throughput)
- **`axi_data_dnsize_dual.gv`** - Wide→Narrow splitter, dual buffer (512→128, 100% throughput)

**Full AXI4 Converters:**
- **`axi4_dwidth_converter_wr.gv`** - Write path converter (AW + W + B channels)
- **`axi4_dwidth_converter_rd.gv`** - Read path converter (AR + R channels)

### Protocol Converters

- **`axi4_to_apb.gv`** - AXI4-to-APB protocol bridge
- **`peakrdl_adapter.gv`** - PeakRDL register interface to command/response adapter

### Generated Images (.png)

All diagrams are available as PNG files:
- `axi_data_upsize.png`
- `axi_data_dnsize_single.png`
- `axi_data_dnsize_dual.png`
- `axi4_dwidth_converter_wr.png`
- `axi4_dwidth_converter_rd.png`
- `axi4_to_apb.png`
- `peakrdl_adapter.png`

## Regenerating Diagrams

### Prerequisites

- Graphviz installed (`sudo apt install graphviz` on Ubuntu/Debian)
- `dot` command available in PATH

### Generate All Diagrams

```bash
# From this directory
make all

# Or manually
dot -Tpng axi_data_upsize.gv -o axi_data_upsize.png
dot -Tpng axi_data_dnsize_single.gv -o axi_data_dnsize_single.png
# ... etc
```

### Generate Single Diagram

```bash
# Upsize converter
dot -Tpng axi_data_upsize.gv -o axi_data_upsize.png

# Downsize single buffer
dot -Tpng axi_data_dnsize_single.gv -o axi_data_dnsize_single.png

# Downsize dual buffer
dot -Tpng axi_data_dnsize_dual.gv -o axi_data_dnsize_dual.png
```

### Generate SVG (for web/docs)

```bash
dot -Tsvg axi_data_upsize.gv -o axi_data_upsize.svg
# ... for all diagrams
```

### Generate PDF (for documentation)

```bash
dot -Tpdf axi_data_upsize.gv -o axi_data_upsize.pdf
# ... for all diagrams
```

## Diagram Contents

### axi_data_upsize.gv

**Shows:**
- Narrow input interface (128-bit beats)
- Beat counter (0→3 for 4:1 ratio)
- 512-bit data buffer accumulation
- Wide output interface (512-bit beats)
- Sideband handling (WSTRB concatenation or RRESP OR)
- 100% throughput annotation

**Use Case:** Understanding narrow-to-wide data accumulation

### axi_data_dnsize_single.gv

**Shows:**
- Wide input interface (512-bit beats)
- Single 512-bit buffer
- 4:1 multiplexer for 128-bit slices
- Output counter (0→3)
- Narrow output interface (128-bit beats)
- Timing diagram showing 80% throughput (1-cycle gap)
- Sideband handling (WSTRB slice or RRESP broadcast)

**Use Case:** Understanding wide-to-narrow splitting (area-efficient mode)

### axi_data_dnsize_dual.gv

**Shows:**
- Wide input interface (512-bit beats)
- Dual ping-pong buffers (Buffer 0 and Buffer 1)
- Buffer select logic (write/read muxes)
- Independent counters for each buffer
- Output multiplexing
- Timing diagram showing 100% throughput (no gaps)
- Ping-pong operation (one reads while other writes)

**Use Case:** Understanding dual-buffer high-performance mode

### axi4_dwidth_converter_wr.gv

**Shows:**
- AXI4 slave interface (narrow - 64-bit)
- AW/W/B channel handling
- Address calculator and burst length adjuster
- Skid buffers for flow control
- axi_data_upsize integration
- AXI4 master interface (wide - 512-bit)
- Example transaction (8 narrow beats → 1 wide beat)

**Use Case:** Understanding full write path conversion

### axi4_dwidth_converter_rd.gv

**Shows:**
- AXI4 slave interface (wide - 512-bit)
- AR/R channel handling
- Address calculator and burst length adjuster
- Burst tracker for RLAST generation
- axi_data_dnsize integration (dual buffer)
- AXI4 master interface (narrow - 64-bit)
- Continuous streaming timing (100% throughput)

**Use Case:** Understanding full read path conversion

### axi4_to_apb.gv

**Shows:**
- AXI4 slave interface (64-bit addr, 32-bit data)
- Protocol conversion state machine
- Write path (AW + W → APB write)
- Read path (AR → APB read)
- Address width conversion (64→32 bit)
- Response converter (PSLVERR → BRESP/RRESP)
- APB master interface
- FSM state descriptions
- Example timing diagrams

**Use Case:** Understanding AXI4-to-APB protocol conversion

### peakrdl_adapter.gv

**Shows:**
- PeakRDL register interface (APB-style)
- Command generator
- Response handler
- Command/response interface (custom protocol)
- Write transaction example
- Read transaction example
- Error propagation

**Use Case:** Understanding PeakRDL adapter protocol decoupling

## Diagram Style

**Colors:**
- **Light blue** - Input interfaces (slave/narrow/wide)
- **Light coral/pink** - Output interfaces (master/narrow/wide)
- **Light yellow** - Control logic and notes
- **Light gray** - Data path elements
- **Light green** - Features/highlights
- **Light cyan** - Examples
- **Orange** - Warnings/limitations

**Nodes:**
- **Rounded boxes** - Functional blocks
- **Cylinders** - Registers/buffers
- **Diamonds** - Decision/control points
- **Trapezoids** - Multiplexers
- **Note boxes** - Annotations, examples, timing diagrams
- **Records** - Interfaces with multiple signals

**Edges:**
- **Bold solid** - Primary data flow
- **Dashed** - Control signals
- **Colored** - Protocol-specific paths (blue=write, green=read)

## Adding New Diagrams

To add a new converter diagram:

1. Create new .gv file:
   ```bash
   cp axi_data_upsize.gv my_new_converter.gv
   ```

2. Edit the new file:
   - Update title and module name
   - Adjust nodes for converter functionality
   - Update data flow connections
   - Add timing/example annotations

3. Update Makefile SOURCES list:
   ```makefile
   SOURCES = ... \
             my_new_converter.gv
   ```

4. Generate PNG:
   ```bash
   make all
   ```

5. Link from documentation:
   ```markdown
   ![My Converter Block Diagram](../assets/graphviz/my_new_converter.png)
   ```

## Referenced In Documentation

These diagrams are referenced in:
- `converter_index.md` - Main specification index
- `ch02_data_width_converters/*.md` - Data width converter chapters
- `ch03_protocol_converters/*.md` - Protocol converter chapters
- `ch04_usage_examples/*.md` - Usage and integration examples

## Tools

**Graphviz Version:** Any recent version (tested with 2.43+)

**Alternative Viewers:**
- Online: http://www.webgraphviz.com/ (paste .gv content)
- VS Code: Install "Graphviz Preview" extension
- Command line: `xdg-open <diagram>.png` (Linux)

## Notes

- PNG files are version controlled for easy documentation viewing
- Source .gv files are the authoritative source
- Regenerate PNGs after any .gv file changes
- Keep diagrams up-to-date with module implementations
- Use consistent color scheme across all diagrams

---

**Last Updated:** 2025-10-26
**Maintainer:** RTL Design Sherpa Project
