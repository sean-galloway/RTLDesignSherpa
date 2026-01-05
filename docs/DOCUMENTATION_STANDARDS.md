# Documentation Standards for HAS/MAS Specifications

**Version:** 1.0
**Date:** 2026-01-03
**Purpose:** Define markdown formatting standards for proper PDF generation

---

## Overview

This document defines the markdown formatting standards required for proper generation of PDF documents with working Table of Contents, List of Figures, List of Tables, and List of Waveforms.

The `md_to_docx.py` tool parses the markdown and expects specific patterns to detect and catalog figures, tables, and waveforms.

---

## Table Captions

Tables must use Pandoc's table caption syntax. Add a caption line starting with `: ` immediately after the table.

### Correct Format

```markdown
| Column 1 | Column 2 | Column 3 |
|----------|----------|----------|
| Data A   | Data B   | Data C   |
| Data D   | Data E   | Data F   |

: APB Signal Definitions
```

### Incorrect Format (Will NOT be detected)

```markdown
| Column 1 | Column 2 | Column 3 |
|----------|----------|----------|
| Data A   | Data B   | Data C   |

*Table: APB Signal Definitions*
```

### Key Points

- The `: ` prefix is mandatory
- The caption must be on a blank line immediately after the table
- No blank line between table and caption
- Keep captions concise but descriptive

---

## Figure Captions

Figures must use heading syntax with a specific format to be detected.

### Correct Format

```markdown
### Figure 3.1: APB Crossbar Block Diagram

![APB Crossbar Architecture](../assets/mermaid/02_block_diagram.png)

The figure above shows the top-level architecture...
```

### Incorrect Format (Will NOT be detected)

```markdown
![APB Crossbar Architecture](../assets/mermaid/02_block_diagram.png)

*Figure: APB Crossbar Architecture*
```

### Key Points

- Use a heading level (`##`, `###`, or `####`) with format: `Figure X.X: Title`
- Figure numbers can be simple (1, 2, 3) or hierarchical (3.1, 3.2.1)
- The heading must come BEFORE the image (caption-above style)
- Keep the image on the next line after the heading
- Optional descriptive text can follow the image

---

## Waveform Captions

Waveforms (timing diagrams) use the same heading format as figures but with "Waveform" prefix.

### Correct Format

```markdown
### Waveform 4.1: APB Write Transaction Timing

![APB Write Timing](../assets/wavedrom/apb_write_access.png)

The waveform shows the setup and access phases...
```

### Key Points

- Use a heading level with format: `Waveform X.X: Title`
- Same numbering rules as figures
- Typically used for timing diagrams from WaveDrom
- Heading must come BEFORE the image

---

## Numbering Convention

### Recommended: Chapter-Based Numbering

Use the chapter number as the first digit:

- Chapter 1 figures: Figure 1.1, Figure 1.2, ...
- Chapter 2 figures: Figure 2.1, Figure 2.2, ...
- Chapter 3 tables: Table 3.1, Table 3.2, ...

### Alternative: Document-Wide Numbering

Simple sequential numbering across the document:

- Figure 1, Figure 2, Figure 3, ...
- Table 1, Table 2, Table 3, ...

Pick one style and use it consistently throughout the document.

---

## Complete Example

Here's a complete example showing all three types:

```markdown
# Chapter 3: Architecture

## Block Diagram

### Figure 3.1: APB Crossbar Block Diagram

![Block Diagram](../assets/mermaid/02_block_diagram.png)

The APB Crossbar consists of three main layers...

## Signal Definitions

The following table lists all APB signals:

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| PSEL   | 1     | Input     | Slave select |
| PENABLE| 1     | Input     | Enable signal |
| PADDR  | 32    | Input     | Address bus |
| PWRITE | 1     | Input     | Write enable |

: APB Slave Interface Signals

## Timing

### Waveform 3.1: APB Write Transaction

![APB Write](../assets/wavedrom/apb_write.png)

The write transaction consists of a setup phase followed by an access phase.
```

---

## Checklist for Document Authors

Before generating PDFs, verify:

- [ ] Every table has a `: Caption` line immediately after it
- [ ] Every figure has a `### Figure X.X: Title` heading before the image
- [ ] Every timing diagram has a `### Waveform X.X: Title` heading before the image
- [ ] Numbering is consistent (either chapter-based or document-wide)
- [ ] No blank lines between tables and their captions
- [ ] Captions are descriptive but concise

---

## Troubleshooting

### "List of Figures" is empty

- Check that figures use heading syntax: `### Figure X.X: Title`
- Verify the heading comes BEFORE the image, not after
- Ensure heading uses proper markdown heading syntax (`#`, `##`, `###`)

### "List of Tables" is empty

- Check that tables have `: Caption` on the line after the table
- Ensure no blank line between table and caption
- Caption must start with `: ` (colon + space)

### "List of Waveforms" is empty

- Check that waveforms use heading syntax: `### Waveform X.X: Title`
- Same rules as figures apply

---

## Style Configuration

The `*_styles.yaml` file controls which lists are generated:

```yaml
lists:
  lot: true    # List of Tables
  lof: true    # List of Figures
  low: false   # List of Waveforms (set true for MAS with timing diagrams)
```

---

**Last Updated:** 2026-01-03
**Maintained By:** RTL Design Sherpa Project
