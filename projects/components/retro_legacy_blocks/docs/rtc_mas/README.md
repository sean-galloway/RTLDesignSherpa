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

# RTC Specification

**Status:** Written (chapters 1 and 5) - see rtc_mas_index.md for the
authoritative status and known-RTL-deviation notes

---

## Overview

Specification for the RTC block. Chapters 1 and 5 are written; see
rtc_mas_index.md for status and the known-RTL-deviation notes.

## Planned Documentation Structure

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

## Document Generation

Documentation is written in Markdown and can be converted to PDF:

```bash
cd docs/
./generate_pdf.sh
```

## References

- Intel RTC datasheet
- ACPI specification (if applicable)
- Legacy peripheral architecture specifications
- APB protocol specification

---

**Last Updated:** 2025-10-29
