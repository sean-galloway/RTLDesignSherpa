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

# AXI4 Interface Specification

**Last Updated:** 2025-01-10

---

## Overview

The RAPIDS Beats architecture uses three AXI4 master interfaces:
1. **Descriptor AXI:** Fetches descriptors from memory (256-bit data)
2. **Sink AXI Write:** Writes sink data to memory (512-bit data, configurable)
3. **Source AXI Read:** Reads source data from memory (512-bit data, configurable)

---

## Descriptor AXI Master Interface

### Purpose

Fetches descriptor packets from system memory. Shared across all 8 channels with round-robin arbitration.

### Signal Table

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_arvalid` | output | 1 | AR channel valid |
| `m_axi_arready` | input | 1 | AR channel ready |
| `m_axi_araddr` | output | AW | Read address |
| `m_axi_arid` | output | ID_W | Transaction ID |
| `m_axi_arlen` | output | 8 | Burst length (fixed: 0 = 1 beat) |
| `m_axi_arsize` | output | 3 | Burst size (fixed: 5 = 32 bytes) |
| `m_axi_arburst` | output | 2 | Burst type (fixed: INCR) |
| `m_axi_rvalid` | input | 1 | R channel valid |
| `m_axi_rready` | output | 1 | R channel ready |
| `m_axi_rdata` | input | 256 | Read data (descriptor) |
| `m_axi_rid` | input | ID_W | Response ID |
| `m_axi_rresp` | input | 2 | Read response |
| `m_axi_rlast` | input | 1 | Last beat |

: Table 4.1.1: Descriptor AXI Master Interface Signals

### Transaction Characteristics

| Parameter | Value | Description |
|-----------|-------|-------------|
| Data Width | 256 bits | Fixed descriptor size |
| Burst Length | 1 beat | Single descriptor per transaction |
| Burst Type | INCR | Incrementing burst |
| Max Outstanding | 8 | Configurable via parameter |
| ID Usage | Per-channel | ID encodes source channel |

: Table 4.1.2: Descriptor AXI Transaction Characteristics

### Timing Diagram

### Figure 4.1.1: Descriptor Fetch Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    m_axi_arvalid  _/‾\___:_______:_______:_______:_______:_______
    m_axi_arready  _/‾\___:_______:_______:_______:_______:_______
    m_axi_araddr   X|DESC_ADDR|XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
    m_axi_arid     X| CH2 |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    m_axi_rvalid   _______:_/‾\___:_______:_______:_______:_______
    m_axi_rready   _______:_/‾\___:_______:_______:_______:_______
    m_axi_rdata    X:XXXXXXX|=DESCRIPTOR=|XXX:XXXXXXX:XXXXXXX
    m_axi_rid      X:XXXXXXX| CH2 |XXX:XXXXXXX:XXXXXXX:XXXXXXX
    m_axi_rlast    _______:_/‾\___:_______:_______:_______:_______
```

**TODO:** Replace with simulation-generated waveform

---

## Sink AXI Write Master Interface

### Purpose

Writes sink data from SRAM to system memory. Supports burst transactions for efficient memory bandwidth.

### Signal Table

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_awvalid` | output | 1 | AW channel valid |
| `m_axi_awready` | input | 1 | AW channel ready |
| `m_axi_awaddr` | output | AW | Write address |
| `m_axi_awid` | output | ID_W | Transaction ID |
| `m_axi_awlen` | output | 8 | Burst length (0-255) |
| `m_axi_awsize` | output | 3 | Burst size |
| `m_axi_awburst` | output | 2 | Burst type |
| `m_axi_wvalid` | output | 1 | W channel valid |
| `m_axi_wready` | input | 1 | W channel ready |
| `m_axi_wdata` | output | DW | Write data |
| `m_axi_wstrb` | output | DW/8 | Write strobes |
| `m_axi_wlast` | output | 1 | Last beat |
| `m_axi_bvalid` | input | 1 | B channel valid |
| `m_axi_bready` | output | 1 | B channel ready |
| `m_axi_bid` | input | ID_W | Response ID |
| `m_axi_bresp` | input | 2 | Write response |

: Table 4.1.3: Sink AXI Write Master Interface Signals

### Transaction Characteristics

| Parameter | Value | Description |
|-----------|-------|-------------|
| Data Width | 512 bits | Configurable |
| Burst Length | 1-256 beats | Based on transfer size |
| Burst Type | INCR | Incrementing burst |
| Max Outstanding AW | 8 | Configurable |
| W FIFO Depth | 64 | Configurable |
| B FIFO Depth | 16 | Configurable |

: Table 4.1.4: Sink AXI Write Transaction Characteristics

### Timing Diagram

### Figure 4.1.2: Sink AXI Write Burst Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    m_axi_awvalid  _/‾\___:_______:_______:_______:_______:_______
    m_axi_awready  _/‾\___:_______:_______:_______:_______:_______
    m_axi_awaddr   X|ADDR |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
    m_axi_awlen    X| 3  |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    m_axi_wvalid   _/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______:_______
    m_axi_wready   _/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______:_______
    m_axi_wdata    X|=D0=|=D1=|=D2=|=D3=|XXX:XXXXXXX:XXXXXXX
    m_axi_wlast    _______________/‾\___:_______:_______:_______
                    :       :       :       :       :       :
    m_axi_bvalid   ___________________:_/‾\___:_______:_______
    m_axi_bready   _____________________/‾\___:_______:_______
    m_axi_bresp    X:XXXXXXX:XXXXXXX:XXXXXXX|OK |XXX:XXXXXXX
```

**TODO:** Replace with simulation-generated waveform

---

## Source AXI Read Master Interface

### Purpose

Reads source data from system memory into SRAM. Supports burst transactions for efficient memory bandwidth.

### Signal Table

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_arvalid` | output | 1 | AR channel valid |
| `m_axi_arready` | input | 1 | AR channel ready |
| `m_axi_araddr` | output | AW | Read address |
| `m_axi_arid` | output | ID_W | Transaction ID |
| `m_axi_arlen` | output | 8 | Burst length (0-255) |
| `m_axi_arsize` | output | 3 | Burst size |
| `m_axi_arburst` | output | 2 | Burst type |
| `m_axi_rvalid` | input | 1 | R channel valid |
| `m_axi_rready` | output | 1 | R channel ready |
| `m_axi_rdata` | input | DW | Read data |
| `m_axi_rid` | input | ID_W | Response ID |
| `m_axi_rresp` | input | 2 | Read response |
| `m_axi_rlast` | input | 1 | Last beat |

: Table 4.1.5: Source AXI Read Master Interface Signals

### Transaction Characteristics

| Parameter | Value | Description |
|-----------|-------|-------------|
| Data Width | 512 bits | Configurable |
| Burst Length | 1-256 beats | Based on transfer size |
| Burst Type | INCR | Incrementing burst |
| Max Outstanding AR | 8 | Configurable |
| R FIFO Depth | 64 | Configurable |

: Table 4.1.6: Source AXI Read Transaction Characteristics

### Timing Diagram

### Figure 4.1.3: Source AXI Read Burst Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    m_axi_arvalid  _/‾\___:_______:_______:_______:_______:_______
    m_axi_arready  _/‾\___:_______:_______:_______:_______:_______
    m_axi_araddr   X|ADDR |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
    m_axi_arlen    X| 3  |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    m_axi_rvalid   ___________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______
    m_axi_rready   ___________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______
    m_axi_rdata    X:XXXXXXX|=D0=|=D1=|=D2=|=D3=|XXX:XXXXXXX
    m_axi_rlast    _______________________/‾\___:_______:_______
```

**TODO:** Replace with simulation-generated waveform

---

## AXI Protocol Compliance

### Supported Features

| Feature | Descriptor | Sink Write | Source Read |
|---------|------------|------------|-------------|
| Burst Type INCR | Yes | Yes | Yes |
| Burst Type FIXED | No | No | No |
| Burst Type WRAP | No | No | No |
| Exclusive Access | No | No | No |
| Locked Access | No | No | No |
| Unaligned Access | No | Yes | Yes |
| Narrow Transfers | No | Yes | Yes |

: Table 4.1.7: AXI Feature Support

### Error Handling

- **SLVERR:** Transaction aborted, error reported to scheduler
- **DECERR:** Transaction aborted, error reported to scheduler
- **Timeout:** Configurable watchdog, error reported to scheduler

---

**Last Updated:** 2025-01-10
