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

# AXI Master Interfaces

## Overview

STREAM includes three AXI4 master interfaces for memory access:

| Interface | Purpose | Data Width | Address Width |
|-----------|---------|------------|---------------|
| `m_axi_desc_*` | Descriptor fetch | 256 bits | 64 bits |
| `m_axi_rd_*` | Source data read | Parameterizable | 64 bits |
| `m_axi_wr_*` | Destination write | Parameterizable | 64 bits |

---

## Descriptor Fetch Master

### Signal Summary

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_desc_arid` | Output | ID_WIDTH | Read transaction ID |
| `m_axi_desc_araddr` | Output | 64 | Read address |
| `m_axi_desc_arlen` | Output | 8 | Burst length (0 = 1 beat) |
| `m_axi_desc_arsize` | Output | 3 | Beat size (5 = 32 bytes) |
| `m_axi_desc_arburst` | Output | 2 | Burst type (INCR) |
| `m_axi_desc_arvalid` | Output | 1 | Address valid |
| `m_axi_desc_arready` | Input | 1 | Address ready |
| `m_axi_desc_rid` | Input | ID_WIDTH | Read data ID |
| `m_axi_desc_rdata` | Input | 256 | Read data |
| `m_axi_desc_rresp` | Input | 2 | Read response |
| `m_axi_desc_rlast` | Input | 1 | Last beat |
| `m_axi_desc_rvalid` | Input | 1 | Read data valid |
| `m_axi_desc_rready` | Output | 1 | Read data ready |

### Transaction Characteristics

| Characteristic | Value | Notes |
|----------------|-------|-------|
| **Burst Length** | 1 beat | Single 256-bit descriptor |
| **Burst Type** | INCR | Fixed increment |
| **Outstanding** | 1-2 | Configurable |
| **Ordering** | In-order | Single ID used |

### Address Alignment

Descriptor addresses must be 32-byte aligned (256-bit boundary).

---

## Data Read Master

### Signal Summary

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_rd_arid` | Output | ID_WIDTH | Read transaction ID |
| `m_axi_rd_araddr` | Output | 64 | Read address |
| `m_axi_rd_arlen` | Output | 8 | Burst length |
| `m_axi_rd_arsize` | Output | 3 | Beat size |
| `m_axi_rd_arburst` | Output | 2 | Burst type (INCR) |
| `m_axi_rd_arvalid` | Output | 1 | Address valid |
| `m_axi_rd_arready` | Input | 1 | Address ready |
| `m_axi_rd_rid` | Input | ID_WIDTH | Read data ID |
| `m_axi_rd_rdata` | Input | DATA_WIDTH | Read data |
| `m_axi_rd_rresp` | Input | 2 | Read response |
| `m_axi_rd_rlast` | Input | 1 | Last beat |
| `m_axi_rd_rvalid` | Input | 1 | Read data valid |
| `m_axi_rd_rready` | Output | 1 | Read data ready |

### Transaction Characteristics

| Characteristic | Value | Notes |
|----------------|-------|-------|
| **Burst Length** | 1-256 beats | AXI4 maximum |
| **Burst Type** | INCR | Fixed increment |
| **Outstanding** | Configurable | 4-16 typical |
| **Ordering** | In-order | Channel-based ID tagging |

### Burst Generation

Large transfers are broken into maximum-length bursts:

| Transfer Size | Burst Count | Burst Lengths |
|---------------|-------------|---------------|
| 256 beats | 1 | 256 |
| 512 beats | 2 | 256, 256 |
| 300 beats | 2 | 256, 44 |

---

## Data Write Master

### Signal Summary

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_wr_awid` | Output | ID_WIDTH | Write transaction ID |
| `m_axi_wr_awaddr` | Output | 64 | Write address |
| `m_axi_wr_awlen` | Output | 8 | Burst length |
| `m_axi_wr_awsize` | Output | 3 | Beat size |
| `m_axi_wr_awburst` | Output | 2 | Burst type (INCR) |
| `m_axi_wr_awvalid` | Output | 1 | Address valid |
| `m_axi_wr_awready` | Input | 1 | Address ready |
| `m_axi_wr_wdata` | Output | DATA_WIDTH | Write data |
| `m_axi_wr_wstrb` | Output | DATA_WIDTH/8 | Byte strobes |
| `m_axi_wr_wlast` | Output | 1 | Last beat |
| `m_axi_wr_wvalid` | Output | 1 | Write data valid |
| `m_axi_wr_wready` | Input | 1 | Write data ready |
| `m_axi_wr_bid` | Input | ID_WIDTH | Response ID |
| `m_axi_wr_bresp` | Input | 2 | Write response |
| `m_axi_wr_bvalid` | Input | 1 | Response valid |
| `m_axi_wr_bready` | Output | 1 | Response ready |

### Transaction Characteristics

| Characteristic | Value | Notes |
|----------------|-------|-------|
| **Burst Length** | 1-256 beats | Matches read bursts |
| **Burst Type** | INCR | Fixed increment |
| **Outstanding** | Configurable | 4-16 typical |
| **Write Strobes** | All-ones | Aligned transfers only |

---

## Common AXI Attributes

### Supported Features

| Feature | Descriptor | Read | Write |
|---------|------------|------|-------|
| INCR Burst | Yes | Yes | Yes |
| WRAP Burst | No | No | No |
| FIXED Burst | No | No | No |
| Exclusive | No | No | No |
| Locked | No | No | No |

### Error Handling

- SLVERR/DECERR on any channel stops the current transfer
- Error logged in channel status register
- Subsequent descriptors in chain not processed
- Software intervention required to clear and resume

---

**Last Updated:** 2026-01-03
