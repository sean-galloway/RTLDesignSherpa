# IOAPIC Specification - Graphviz Diagrams

This directory contains Graphviz source files for IOAPIC specification diagrams.

## Available Diagrams

### 1. delivery_fsm.dot
**Interrupt Delivery State Machine**
- Shows 3-state FSM: IDLE → DELIVER → WAIT_EOI
- Illustrates edge vs level-triggered paths
- Used in: Ch02 FSM Summary

### 2. apb_ioapic.gv
**Top-Level Block Diagram**
- Shows complete module hierarchy
- Illustrates data flow between blocks
- Used in: Ch01 Architecture, Ch02 Block Overview

### 3. indirect_access.gv
**Indirect Register Access Method**
- Shows IOREGSEL/IOWIN mechanism
- Illustrates Intel 82093AA compatibility
- Used in: Ch03 Interfaces, Ch05 Registers

## Generating Diagrams

### Generate All Diagrams (PNG and SVG)
```bash
make all
```

### Generate PNG Only
```bash
make png
```

### Generate SVG Only
```bash
make svg
```

### Clean Generated Files
```bash
make clean
```

## Output Directories

- **PNG**: `../png/` - Raster images for documentation
- **SVG**: `../svg/` - Vector images for scalability

## Tools Required

- **Graphviz** (dot command)
  - Ubuntu/Debian: `sudo apt install graphviz`
  - macOS: `brew install graphviz`
  - Windows: Download from graphviz.org

## Diagram Formats

- `.dot` files: Standard Graphviz DOT language
- `.gv` files: Graphviz format (same as .dot, different extension)

Both are text-based and can be edited with any text editor.

## Usage in Documentation

The generated PNG/SVG files are referenced in markdown documents:

```markdown
![IOAPIC Block Diagram](../assets/png/apb_ioapic.png)
```

Or for SVG (better for web):

```markdown
![IOAPIC FSM](../assets/svg/delivery_fsm.svg)
```

## Diagram Style Guide

**Colors:**
- Light blue: External interfaces, APB components
- Light green: Register/configuration components
- Light coral: Core logic components
- Light yellow: Sub-blocks

**Line Styles:**
- Solid: Data/signal flow
- Dashed: Control/selection
- Dotted: Optional/conditional paths

**Line Width:**
- Thick (penwidth=2): Primary/critical paths
- Normal: Secondary paths
- Thin/dotted: Optional selections

---

**Related:**
- [Specification Index](../../ioapic_index.md)
- [Architecture Chapter](../../ch01_overview/02_architecture.md)
- [FSM Summary](../../ch02_blocks/05_fsm_summary.md)
