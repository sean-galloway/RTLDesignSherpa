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

# Document Conventions

## Notation

### Signal Naming

| Convention | Meaning | Example |
|------------|---------|---------|
| `m<i>_apb_*` | Master-side APB signals (input to crossbar) | `m0_apb_PSEL` |
| `s<j>_apb_*` | Slave-side APB signals (output from crossbar) | `s2_apb_PREADY` |
| `P*` | APB protocol signal prefix | `PADDR`, `PWRITE`, `PRDATA` |
| `<i>`, `<j>` | Master/slave index placeholder | m0, s3 |

: Signal Naming Conventions

### Parameter Naming

| Convention | Meaning | Example |
|------------|---------|---------|
| `UPPER_CASE` | Module parameters | `ADDR_WIDTH`, `DATA_WIDTH` |
| `NUM_*` | Count parameters | `NUM_MASTERS`, `NUM_SLAVES` |
| `*_WIDTH` | Bit width parameters | `DATA_WIDTH = 32` |
| `BASE_*` | Base address parameters | `BASE_ADDR = 0x10000000` |

: Parameter Naming Conventions

## Diagrams

### Block Diagrams

Block diagrams in this document use:

- **Rectangles** for functional blocks
- **Arrows** showing data flow direction
- **Dashed lines** for configuration/control paths
- **Labels** on connections indicating signal groups

### Address Notation

Addresses are shown in hexadecimal with the `0x` prefix:

- `0x1000_0000` - Underscores separate 16-bit groups for readability
- `[31:0]` - Bit range notation (MSB:LSB)
- `64KB` - Size notation using standard abbreviations

## Table Captions

Tables are numbered sequentially within each chapter. A colon (`:`) followed by the caption text appears below each table.

## Requirement References

When referencing requirements from the PRD:

- **FR-n** - Functional Requirement number n
- **PR-n** - Performance Requirement number n
- **IR-n** - Interface Requirement number n

---

**Next:** [Definitions and Acronyms](03_definitions.md)
