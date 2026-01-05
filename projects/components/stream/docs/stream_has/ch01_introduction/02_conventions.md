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

## Notation Conventions

### Signal Naming

| Prefix/Suffix | Meaning | Example |
|---------------|---------|---------|
| `i_` | Input signal | `i_clk`, `i_data` |
| `o_` | Output signal | `o_valid`, `o_ready` |
| `r_` | Registered signal | `r_state`, `r_count` |
| `w_` | Combinational wire | `w_next_state` |
| `_n` | Active-low signal | `aresetn`, `rst_n` |

### Interface Prefixes

| Prefix | Protocol | Direction |
|--------|----------|-----------|
| `s_apb_` | APB slave | Inbound |
| `m_axi_desc_` | AXI4 descriptor master | Outbound |
| `m_axi_rd_` | AXI4 read master | Outbound |
| `m_axi_wr_` | AXI4 write master | Outbound |
| `monbus_` | Monitor bus | Outbound |

---

## Diagram Conventions

### Block Diagrams

- **Rectangles** - Functional blocks
- **Arrows** - Data flow direction
- **Dashed Lines** - Configuration/control paths
- **Double Lines** - High-bandwidth data paths

### Timing Diagrams

- **High** - Logic 1
- **Low** - Logic 0
- **X** - Don't care / undefined
- **Hatched** - Valid data window

---

## Numeric Conventions

### Units

| Unit | Meaning |
|------|---------|
| Beat | Single data transfer (one clock cycle of valid data) |
| Burst | Sequence of consecutive beats |
| Transaction | Complete AXI transaction (address + all data beats) |

### Address Notation

- All addresses are specified in bytes unless otherwise noted
- Address alignment requirements are specified relative to data width
- Example: 512-bit data width requires 64-byte (512/8) alignment

### Size Notation

| Notation | Value |
|----------|-------|
| KB | 1,024 bytes |
| MB | 1,048,576 bytes |
| Kbit | 1,024 bits |

---

## Requirement Notation

Requirements and constraints are identified using the following format:

| Prefix | Category |
|--------|----------|
| **[REQ-x]** | Functional requirement |
| **[PERF-x]** | Performance requirement |
| **[INTEG-x]** | Integration requirement |
| **[CONST-x]** | Design constraint |

---

## Reference Format

Cross-references to other documents use the format:

- **[MAS-x.y]** - Reference to MAS section x.y
- **[REF-n]** - Reference to document in reference table

---

**Last Updated:** 2026-01-03
