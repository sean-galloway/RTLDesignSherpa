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

# MonBus Interface Specification

**Last Updated:** 2025-01-10

---

## Overview

The MonBus (Monitor Bus) is a 64-bit packet-based interface for reporting internal events, status, and performance data. All RAPIDS subsystems generate MonBus packets that are aggregated and output through a unified interface.

---

## MonBus Signal Interface

### Signal Table

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `monbus_pkt_valid` | output | 1 | Packet valid |
| `monbus_pkt_ready` | input | 1 | Consumer ready |
| `monbus_pkt_data` | output | 64 | Packet data |

: Table 4.3.1: MonBus Interface Signals

### Handshaking Protocol

Standard valid/ready handshaking:
- Data transfers when `valid & ready` both high
- Producer holds `valid` until `ready` seen
- Consumer asserts `ready` when able to accept

### Timing Diagram

### Figure 4.3.1: MonBus Packet Transfer Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    pkt_valid      _/‾\___/‾‾‾‾‾‾‾\___/‾\___:_______:_______
    pkt_ready      _/‾\___:_______/‾\___/‾\___:_______:_______
    pkt_data       X|PKT1|X|==PKT2==|X|PKT3|XXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
                    ^       ^       ^       ^
                    |       |       |       |
                  Xfer    Wait   Xfer   Xfer
```

**TODO:** Replace with simulation-generated waveform

---

## MonBus Packet Format

### 64-bit Packet Structure

```
    63      56 55      48 47      40 39      32 31              0
    +--------+---------+---------+---------+-------------------+
    | Type   | Unit ID | Agent ID| Channel | Payload (32 bits) |
    +--------+---------+---------+---------+-------------------+
```

### Figure 4.3.2: MonBus Packet Format

| Field | Bits | Description |
|-------|------|-------------|
| Type | [63:56] | Packet type code |
| Unit ID | [55:48] | Reporting unit identifier |
| Agent ID | [47:40] | Source agent within unit |
| Channel | [39:32] | Channel number (0-7) |
| Payload | [31:0] | Type-specific payload |

: Table 4.3.2: MonBus Packet Fields

---

## Packet Types

### Type Code Definitions

| Type Code | Name | Description |
|-----------|------|-------------|
| 0x01 | DESC_FETCH | Descriptor fetch started |
| 0x02 | DESC_COMPLETE | Descriptor fetch completed |
| 0x03 | SCHED_START | Scheduler started transfer |
| 0x04 | SCHED_DONE | Scheduler transfer complete |
| 0x10 | AXI_RD_START | AXI read burst started |
| 0x11 | AXI_RD_DONE | AXI read burst completed |
| 0x12 | AXI_WR_START | AXI write burst started |
| 0x13 | AXI_WR_DONE | AXI write burst completed |
| 0x20 | SRAM_FILL | SRAM fill event |
| 0x21 | SRAM_DRAIN | SRAM drain event |
| 0x30 | ERROR | Error event |
| 0x31 | TIMEOUT | Timeout event |
| 0xFF | HEARTBEAT | Periodic heartbeat |

: Table 4.3.3: MonBus Packet Types

### Payload Formats by Type

#### DESC_FETCH / DESC_COMPLETE (0x01, 0x02)

| Bits | Description |
|------|-------------|
| [31:16] | Descriptor address [47:32] |
| [15:0] | Descriptor address [31:16] |

: Table 4.3.4: Descriptor Packet Payload

#### SCHED_START / SCHED_DONE (0x03, 0x04)

| Bits | Description |
|------|-------------|
| [31:16] | Transfer ID |
| [15:0] | Beat count |

: Table 4.3.5: Scheduler Packet Payload

#### AXI_RD/WR_START/DONE (0x10-0x13)

| Bits | Description |
|------|-------------|
| [31:24] | AXI ID |
| [23:16] | Burst length |
| [15:0] | Reserved |

: Table 4.3.6: AXI Event Packet Payload

#### ERROR (0x30)

| Bits | Description |
|------|-------------|
| [31:24] | Error code |
| [23:16] | Error source |
| [15:0] | Error details |

: Table 4.3.7: Error Packet Payload

---

## MonBus Source Aggregation

### RAPIDS Core MonBus Sources

| Source ID | Agent | Description |
|-----------|-------|-------------|
| 0-7 | Scheduler[0:7] | Per-channel scheduler events |
| 8-15 | DescEngine[0:7] | Per-channel descriptor events |
| 16-23 | SnkSRAM[0:7] | Sink SRAM controller events |
| 24-31 | SrcSRAM[0:7] | Source SRAM controller events |
| 32 | AXI Write Engine | Write transaction events |
| 33 | AXI Read Engine | Read transaction events |
| 34 | Error Handler | Error events |

: Table 4.3.8: MonBus Source Assignment

### Aggregation Hierarchy

### Figure 4.3.3: MonBus Aggregation Tree

```
    Level 0 (Sources)           Level 1 (Groups)        Level 2 (Top)
    +----------------+
    | Scheduler[0]   |------+
    | DescEngine[0]  |------+---> scheduler_group[0] ---+
    +----------------+                                   |
    +----------------+                                   |
    | Scheduler[1]   |------+                           |
    | DescEngine[1]  |------+---> scheduler_group[1] ---+
    +----------------+                                   |
         ...                            ...              +---> rapids_core
    +----------------+                                   |     monbus_out
    | Scheduler[7]   |------+                           |
    | DescEngine[7]  |------+---> scheduler_group[7] ---+
    +----------------+                                   |
    +----------------+                                   |
    | SnkSRAM[0:7]   |--------> snk_sram_group --------+
    +----------------+                                   |
    +----------------+                                   |
    | SrcSRAM[0:7]   |--------> src_sram_group --------+
    +----------------+                                   |
    +----------------+                                   |
    | AXI Engines    |--------> axi_engine_group ------+
    +----------------+
```

---

## Integration Guidelines

### Consumer Requirements

MonBus consumers must:
1. Provide sufficient ready cycles to prevent packet loss
2. Handle bursty traffic (multiple sources may have packets simultaneously)
3. Process or buffer packets at wire rate

### Recommended Consumer Patterns

```systemverilog
// Pattern 1: Direct FIFO buffering
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(256)
) u_monbus_fifo (
    .i_clk      (clk),
    .i_rst_n    (rst_n),
    .i_valid    (monbus_pkt_valid),
    .i_data     (monbus_pkt_data),
    .o_ready    (monbus_pkt_ready),
    .o_valid    (fifo_valid),
    .o_data     (fifo_data),
    .i_ready    (consumer_ready)
);

// Pattern 2: Software register interface
always_ff @(posedge clk) begin
    if (monbus_pkt_valid && monbus_pkt_ready) begin
        sw_monbus_data <= monbus_pkt_data;
        sw_monbus_valid <= 1'b1;
    end
end
assign monbus_pkt_ready = !sw_monbus_valid || sw_read;
```

---

## Timing Requirements

| Parameter | Value | Description |
|-----------|-------|-------------|
| Min Ready | 1 cycle | Must assert ready within N cycles |
| Max Latency | Configurable | Before packet dropped |
| Packet Rate | Variable | Depends on activity |

: Table 4.3.9: MonBus Timing Parameters

---

**Last Updated:** 2025-01-10
