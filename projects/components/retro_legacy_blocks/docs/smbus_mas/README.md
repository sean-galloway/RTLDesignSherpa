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

# SMBUS Specification

**Status:** Written (chapters 1 and 5), reconciled with the GitHub #58 RTL
rewrite on 2026-09-09 (v1.1) - see smbus_mas_index.md for the authoritative
status and the remaining limitations (RLB-011)

---

## Overview

This directory will contain the complete specification for the SMBUS block.
Chapters 1 and 5 are written today; the rest is planned, and the planned
layout is under Navigation below.

## Usage Example

Documentation is written in Markdown and can be converted to PDF:

```bash
cd docs/
./generate_pdf.sh
```

## References

- Intel SMBUS datasheet
- ACPI specification (if applicable)
- Legacy peripheral architecture specifications
- APB protocol specification

## Navigation

### Chapter 1: Overview
- Block purpose and features
- High-level architecture
- Key specifications

### Chapter 2: Block Diagrams
- Top-level block diagram
- Internal block diagrams
- State machines
- Pipeline diagrams

### Chapter 3: Interfaces
- APB interface specification
- External signals
- Interrupt outputs
- Clock and reset

### Chapter 4: Programming Guide
- Register programming sequences
- Common operations
- Example code
- Best practices

### Chapter 5: Register Map
- Complete register descriptions
- Field definitions
- Reset values
- Access types

---

**Last Updated:** 2026-09-09
