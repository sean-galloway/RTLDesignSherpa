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

# pm_acpi Specification

**Status:** Written (chapters 1 and 5) -- see pm_acpi_mas_index.md for the
authoritative status. The RTL is functional against issue #54 as of
2026-09-09; the chapters describe the fixed hardware.

---

## Overview

This directory will contain the complete specification for the PM_ACPI block.

### Planned Documentation Structure

- **Chapter 1: Overview** -- block purpose and features, high-level
  architecture, key specifications
- **Chapter 2: Block Diagrams** -- top-level block diagram, internal block
  diagrams, state machines, pipeline diagrams
- **Chapter 3: Interfaces** -- APB interface specification, external signals,
  interrupt outputs, clock and reset
- **Chapter 4: Programming Guide** -- register programming sequences, common
  operations, example code, best practices
- **Chapter 5: Register Map** -- complete register descriptions, field
  definitions, reset values, access types

### Document Generation

Documentation will be written in Markdown and can be converted to PDF:

```bash
cd docs/
./generate_pdf.sh
```

## References

- Intel PM_ACPI datasheet
- ACPI specification (if applicable)
- Legacy peripheral architecture specifications
- APB protocol specification

---

**Last Updated:** 2026-09-09
