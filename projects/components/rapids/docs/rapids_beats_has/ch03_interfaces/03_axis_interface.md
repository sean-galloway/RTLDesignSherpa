# AXIS Interface Specification

## Overview

RAPIDS Beats uses AXI-Stream interfaces for network data transfer:

1. **Sink AXIS Slave** - Receives data from network (ingress)
2. **Source AXIS Master** - Sends data to network (egress)

## Sink AXIS Slave

### Purpose

Receives streaming data from external network interface and writes to SRAM buffer.

### Configuration

| Parameter | Default | Range | Description |
|-----------|---------|-------|-------------|
| Data Width | 512-bit | Configurable | TDATA width |
| ID Width | 8-bit | 0-8 | TID width (optional) |
| DEST Width | 8-bit | 0-8 | TDEST width (optional) |
| USER Width | 1-bit | 0-16 | TUSER width (optional) |

: Sink AXIS Configuration

### Signal List

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `s_axis_sink_tdata` | 512 | input | Data payload |
| `s_axis_sink_tkeep` | 64 | input | Byte valid mask |
| `s_axis_sink_tstrb` | 64 | input | Byte position (optional) |
| `s_axis_sink_tlast` | 1 | input | End of packet |
| `s_axis_sink_tid` | 8 | input | Transaction ID (channel select) |
| `s_axis_sink_tdest` | 8 | input | Destination (optional) |
| `s_axis_sink_tuser` | 1 | input | User sideband (optional) |
| `s_axis_sink_tvalid` | 1 | input | Data valid |
| `s_axis_sink_tready` | 1 | output | Ready to accept |

: Sink AXIS Signals

### Timing Diagram

![Sink AXIS Timing](../assets/wavedrom/sink_axis_timing.svg)

**Source:** [sink_axis_timing.json](../assets/wavedrom/sink_axis_timing.json)

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p.........."},
    {},
    {"name": "tvalid", "wave": "0.1.1.1.1.0"},
    {"name": "tready", "wave": "1..0..1...."},
    {"name": "tdata", "wave": "x.=.=.=.=.x", "data": ["D0","D1","D2","D3"]},
    {"name": "tkeep", "wave": "x.=.=.=.=.x", "data": ["FF","FF","FF","FF"]},
    {"name": "tlast", "wave": "0.......1.0"},
    {"name": "tid", "wave": "x.=.=.=.=.x", "data": ["CH0","CH0","CH0","CH0"]}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Sink AXIS 4-Beat Packet with Backpressure"}
}
```

### Backpressure Behavior

When SRAM buffer is full, `tready` deasserts:

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p.........."},
    {},
    {"name": "tvalid", "wave": "0.1........"},
    {"name": "tready", "wave": "1...0...1.."},
    {"name": "tdata", "wave": "x.=...=....", "data": ["D0","D0"]},
    {},
    {"name": "sram_full", "wave": "0...1...0.."},
    {"name": "sram_wr_en", "wave": "0.1.0...1.."}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Backpressure Due to Full SRAM"}
}
```

---

## Source AXIS Master

### Purpose

Sends streaming data from SRAM buffer to external network interface.

### Configuration

| Parameter | Default | Range | Description |
|-----------|---------|-------|-------------|
| Data Width | 512-bit | Configurable | TDATA width |
| ID Width | 8-bit | 0-8 | TID width (optional) |
| DEST Width | 8-bit | 0-8 | TDEST width (optional) |
| USER Width | 1-bit | 0-16 | TUSER width (optional) |

: Source AXIS Configuration

### Signal List

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `m_axis_src_tdata` | 512 | output | Data payload |
| `m_axis_src_tkeep` | 64 | output | Byte valid mask |
| `m_axis_src_tstrb` | 64 | output | Byte position (optional) |
| `m_axis_src_tlast` | 1 | output | End of packet |
| `m_axis_src_tid` | 8 | output | Transaction ID (channel) |
| `m_axis_src_tdest` | 8 | output | Destination (optional) |
| `m_axis_src_tuser` | 1 | output | User sideband (optional) |
| `m_axis_src_tvalid` | 1 | output | Data valid |
| `m_axis_src_tready` | 1 | input | Downstream ready |

: Source AXIS Signals

### Timing Diagram

![Source AXIS Timing](../assets/wavedrom/source_axis_timing.svg)

**Source:** [source_axis_timing.json](../assets/wavedrom/source_axis_timing.json)

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p.........."},
    {},
    {"name": "tvalid", "wave": "0.1.1.1.1.0"},
    {"name": "tready", "wave": "1.........."},
    {"name": "tdata", "wave": "x.=.=.=.=.x", "data": ["D0","D1","D2","D3"]},
    {"name": "tkeep", "wave": "x.=.=.=.=.x", "data": ["FF","FF","FF","0F"]},
    {"name": "tlast", "wave": "0.......1.0"},
    {"name": "tid", "wave": "x.=.=.=.=.x", "data": ["CH2","CH2","CH2","CH2"]}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Source AXIS 4-Beat Packet (Partial Last Beat)"}
}
```

### Data Availability

Source AXIS only asserts `tvalid` when data is available in SRAM:

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p.........."},
    {},
    {"name": "data_avail", "wave": "=.=.=.=.=.=", "data": ["0","2","4","3","2","0"]},
    {"name": "sram_rd_en", "wave": "0...1.1.1.0"},
    {},
    {"name": "tvalid", "wave": "0...1.1.1.0"},
    {"name": "tready", "wave": "1.........."},
    {"name": "tdata", "wave": "x...=.=.=.x", "data": ["D0","D1","D2"]}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Source AXIS Driven by Data Availability"}
}
```

---

## AXIS Protocol Notes

### Handshake Rules

Standard AXI-Stream handshake applies:

1. `tvalid` asserts when data is available
2. `tready` asserts when receiver can accept
3. Transfer occurs on clock edge when both are high
4. `tvalid` SHALL NOT depend on `tready`
5. `tready` MAY depend on `tvalid`

### TLAST Semantics

| Scenario | TLAST Behavior |
|----------|----------------|
| Descriptor transfer complete | Assert on last beat |
| Packet boundary | Assert on last beat of packet |
| Continuous stream | Not used (always 0) |

: TLAST Usage

### TKEEP Usage

TKEEP indicates valid bytes within each beat:

| TKEEP Value | Meaning |
|-------------|---------|
| 64'hFFFF_FFFF_FFFF_FFFF | All 64 bytes valid |
| 64'h0000_FFFF_FFFF_FFFF | Upper 16 bytes invalid |
| 64'h0000_0000_0000_000F | Only lower 4 bytes valid |

: TKEEP Examples

### Channel Multiplexing via TID

Multiple channels can share a single AXIS interface using TID:

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p.........."},
    {},
    {"name": "tvalid", "wave": "0.1.1.1.1.0"},
    {"name": "tready", "wave": "1.........."},
    {"name": "tid", "wave": "x.=.=.=.=.x", "data": ["CH0","CH0","CH3","CH3"]},
    {"name": "tdata", "wave": "x.=.=.=.=.x", "data": ["A0","A1","B0","B1"]},
    {"name": "tlast", "wave": "0...1...1.0"}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Interleaved Channels via TID"}
}
```
