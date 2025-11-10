# PM_ACPI Specification

**Status:** 📋 Planned - Structure Created

---

## Overview

This directory will contain the complete specification for the PM_ACPI block.

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

Documentation will be written in Markdown and can be converted to PDF:

```bash
cd docs/
./generate_pdf.sh
```

## Reference Documents

- Intel PM_ACPI datasheet
- ACPI specification (if applicable)
- Legacy peripheral architecture specifications
- APB protocol specification

---

**Last Updated:** 2025-10-29
