# AXI4 Interface Specification

## Overview

RAPIDS Beats uses three AXI4 master interfaces for memory access:

1. **Descriptor AXI** - Fetches 256-bit descriptors (read-only)
2. **Sink AXI** - Writes data to memory (write-only)
3. **Source AXI** - Reads data from memory (read-only)

## Descriptor AXI Master

### Purpose

Fetches descriptor structures from system memory for all 8 channels.

### Configuration

| Parameter | Value | Description |
|-----------|-------|-------------|
| Data Width | 256-bit | Fixed descriptor size |
| Address Width | 64-bit | Configurable |
| ID Width | 8-bit | Configurable |
| Burst Length | 1 | Single-beat only |
| Burst Type | INCR | Fixed |

: Descriptor AXI Configuration

### Signal List

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `m_axi_desc_aclk` | 1 | input | Clock |
| `m_axi_desc_aresetn` | 1 | input | Reset (active-low) |
| `m_axi_desc_arid` | 8 | output | Read ID (channel ID) |
| `m_axi_desc_araddr` | 64 | output | Read address |
| `m_axi_desc_arlen` | 8 | output | Burst length (always 0) |
| `m_axi_desc_arsize` | 3 | output | Beat size (5 = 32 bytes) |
| `m_axi_desc_arburst` | 2 | output | Burst type (INCR) |
| `m_axi_desc_arvalid` | 1 | output | Address valid |
| `m_axi_desc_arready` | 1 | input | Address ready |
| `m_axi_desc_rid` | 8 | input | Response ID |
| `m_axi_desc_rdata` | 256 | input | Read data |
| `m_axi_desc_rresp` | 2 | input | Read response |
| `m_axi_desc_rlast` | 1 | input | Last beat |
| `m_axi_desc_rvalid` | 1 | input | Data valid |
| `m_axi_desc_rready` | 1 | output | Data ready |

: Descriptor AXI Signals

### Timing Diagram

![Descriptor Fetch Timing](../assets/wavedrom/desc_axi_timing.svg)

**Source:** [desc_axi_timing.json](../assets/wavedrom/desc_axi_timing.json)

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p........."},
    {},
    ["AR Channel",
      {"name": "arvalid", "wave": "01..0....."},
      {"name": "arready", "wave": "1........."},
      {"name": "araddr", "wave": "x=..x.....", "data": ["DESC_ADDR"]},
      {"name": "arid", "wave": "x=..x.....", "data": ["CH_ID"]}
    ],
    {},
    ["R Channel",
      {"name": "rvalid", "wave": "0....1..0."},
      {"name": "rready", "wave": "1........."},
      {"name": "rdata", "wave": "x....=..x.", "data": ["256-bit DESC"]},
      {"name": "rresp", "wave": "x....=..x.", "data": ["OKAY"]},
      {"name": "rlast", "wave": "0....1..0."}
    ]
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Single Descriptor Fetch"}
}
```

---

## Sink AXI Master (Write)

### Purpose

Writes data from SRAM buffer to system memory.

### Configuration

| Parameter | Default | Range | Description |
|-----------|---------|-------|-------------|
| Data Width | 512-bit | Configurable | Match SRAM width |
| Address Width | 64-bit | Configurable | System address space |
| ID Width | 8-bit | Configurable | Transaction tracking |
| Max Burst | 256 | 1-256 | AXI4 maximum |
| Outstanding | 8 | 1-16 | Concurrent AW requests |

: Sink AXI Configuration

### Signal List

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `m_axi_sink_awid` | 8 | output | Write ID |
| `m_axi_sink_awaddr` | 64 | output | Write address |
| `m_axi_sink_awlen` | 8 | output | Burst length - 1 |
| `m_axi_sink_awsize` | 3 | output | Beat size (6 = 64 bytes) |
| `m_axi_sink_awburst` | 2 | output | Burst type (INCR) |
| `m_axi_sink_awvalid` | 1 | output | Address valid |
| `m_axi_sink_awready` | 1 | input | Address ready |
| `m_axi_sink_wdata` | 512 | output | Write data |
| `m_axi_sink_wstrb` | 64 | output | Write strobes |
| `m_axi_sink_wlast` | 1 | output | Last beat |
| `m_axi_sink_wvalid` | 1 | output | Data valid |
| `m_axi_sink_wready` | 1 | input | Data ready |
| `m_axi_sink_bid` | 8 | input | Response ID |
| `m_axi_sink_bresp` | 2 | input | Write response |
| `m_axi_sink_bvalid` | 1 | input | Response valid |
| `m_axi_sink_bready` | 1 | output | Response ready |

: Sink AXI Signals

### Timing Diagram

![Sink AXI Write Timing](../assets/wavedrom/sink_axi_timing.svg)

**Source:** [sink_axi_timing.json](../assets/wavedrom/sink_axi_timing.json)

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p............"},
    {},
    ["AW Channel",
      {"name": "awvalid", "wave": "01.0........."},
      {"name": "awready", "wave": "1............"},
      {"name": "awaddr", "wave": "x=.x.........", "data": ["ADDR"]},
      {"name": "awlen", "wave": "x=.x.........", "data": ["3"]}
    ],
    {},
    ["W Channel",
      {"name": "wvalid", "wave": "0..1111.0...."},
      {"name": "wready", "wave": "1............"},
      {"name": "wdata", "wave": "x..====.x....", "data": ["D0","D1","D2","D3"]},
      {"name": "wlast", "wave": "0.....1.0...."}
    ],
    {},
    ["B Channel",
      {"name": "bvalid", "wave": "0.......1.0.."},
      {"name": "bready", "wave": "1............"},
      {"name": "bresp", "wave": "x.......=.x..", "data": ["OKAY"]}
    ]
  ],
  "config": {"hscale": 1.2},
  "head": {"text": "4-Beat AXI Write Burst"}
}
```

---

## Source AXI Master (Read)

### Purpose

Reads data from system memory to SRAM buffer.

### Configuration

| Parameter | Default | Range | Description |
|-----------|---------|-------|-------------|
| Data Width | 512-bit | Configurable | Match SRAM width |
| Address Width | 64-bit | Configurable | System address space |
| ID Width | 8-bit | Configurable | Transaction tracking |
| Max Burst | 256 | 1-256 | AXI4 maximum |
| Outstanding | 8 | 1-16 | Concurrent AR requests |

: Source AXI Configuration

### Signal List

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `m_axi_src_arid` | 8 | output | Read ID |
| `m_axi_src_araddr` | 64 | output | Read address |
| `m_axi_src_arlen` | 8 | output | Burst length - 1 |
| `m_axi_src_arsize` | 3 | output | Beat size (6 = 64 bytes) |
| `m_axi_src_arburst` | 2 | output | Burst type (INCR) |
| `m_axi_src_arvalid` | 1 | output | Address valid |
| `m_axi_src_arready` | 1 | input | Address ready |
| `m_axi_src_rid` | 8 | input | Response ID |
| `m_axi_src_rdata` | 512 | input | Read data |
| `m_axi_src_rresp` | 2 | input | Read response |
| `m_axi_src_rlast` | 1 | input | Last beat |
| `m_axi_src_rvalid` | 1 | input | Data valid |
| `m_axi_src_rready` | 1 | output | Data ready |

: Source AXI Signals

### Timing Diagram

![Source AXI Read Timing](../assets/wavedrom/source_axi_timing.svg)

**Source:** [source_axi_timing.json](../assets/wavedrom/source_axi_timing.json)

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p..........."},
    {},
    ["AR Channel",
      {"name": "arvalid", "wave": "01.0........"},
      {"name": "arready", "wave": "1..........."},
      {"name": "araddr", "wave": "x=.x........", "data": ["ADDR"]},
      {"name": "arlen", "wave": "x=.x........", "data": ["3"]}
    ],
    {},
    ["R Channel",
      {"name": "rvalid", "wave": "0...1111.0.."},
      {"name": "rready", "wave": "1..........."},
      {"name": "rdata", "wave": "x...====.x..", "data": ["D0","D1","D2","D3"]},
      {"name": "rresp", "wave": "x...====.x..", "data": ["OK","OK","OK","OK"]},
      {"name": "rlast", "wave": "0......1.0.."}
    ]
  ],
  "config": {"hscale": 1.2},
  "head": {"text": "4-Beat AXI Read Burst"}
}
```

---

## AXI Protocol Constraints

### Address Alignment

| Transfer Type | Alignment Requirement |
|---------------|----------------------|
| Descriptor | 32-byte aligned |
| Sink Data | 64-byte aligned |
| Source Data | 64-byte aligned |

: Address Alignment Requirements

### 4KB Boundary Handling

AXI4 requires burst transactions not to cross 4KB boundaries. RAPIDS automatically splits bursts at 4KB boundaries:

```
Example: 8-beat burst starting at 0x0FE0 (64 bytes/beat)
  Beat 0-1: 0x0FE0 - 0x0FFF (to 4KB boundary)
  Beat 2-7: 0x1000 - 0x117F (after boundary)

Split into two bursts:
  Burst 1: ARLEN=1, ARADDR=0x0FE0
  Burst 2: ARLEN=5, ARADDR=0x1000
```

### Response Handling

| Response | Code | RAPIDS Behavior |
|----------|------|-----------------|
| OKAY | 2'b00 | Normal completion |
| EXOKAY | 2'b01 | Treated as OKAY |
| SLVERR | 2'b10 | Error, transfer aborted |
| DECERR | 2'b11 | Error, transfer aborted |

: AXI Response Handling
