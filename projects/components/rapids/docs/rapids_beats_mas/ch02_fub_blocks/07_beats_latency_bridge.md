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

# Beats Latency Bridge Specification

**Module:** `beats_latency_bridge.sv`
**Location:** `projects/components/rapids/rtl/fub_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The Beats Latency Bridge provides buffering to compensate for pipeline latency between alloc_ctrl and drain_ctrl in the SRAM controller. It prevents race conditions where drain signals arrive before allocation is complete.

### Key Features

- **Latency Compensation:** Buffers requests to match pipeline delays
- **Configurable Depth:** Matches expected pipeline latency
- **Flow Control:** Standard valid/ready handshaking
- **Pass-Through Data:** Preserves beat count and channel ID

### Block Diagram

### Figure 2.7.1: Beats Latency Bridge Block Diagram

```
                +---------------------------+
    in_valid -->|                           |--> out_valid
    in_ready <--|    BEATS_LATENCY_BRIDGE   |--> out_ready (input)
    in_beats -->|                           |--> out_beats
    in_id    -->|    [Buffered Pipeline]    |--> out_id
                +---------------------------+
```

**Source:** [02_beats_latency_bridge_block.mmd](../assets/mermaid/02_beats_latency_bridge_block.mmd)

---

## Concept: Why Latency Compensation?

The SRAM controller has a timing challenge:

```
Without Bridge:                        With Bridge:

  alloc_ctrl.wr ----+                    alloc_ctrl.wr ----+
                    |                                      |
                    v                                      v
  +----------+  (immediate)              +----------+  +--------+
  |   SRAM   |<--- drain_ctrl.rd         |   SRAM   |  |LATENCY |
  +----------+                           +----------+  | BRIDGE |
                                                       +---+----+
  Problem: drain_ctrl.rd may arrive                        |
  before alloc_ctrl has reserved                           v
  the space -> race condition!            drain_ctrl.rd (delayed)

                                         Solution: Bridge delays drain
                                         signals to match alloc timing
```

---

## Parameters

```systemverilog
parameter int DEPTH = 4;                         // Bridge FIFO depth
parameter int BEATS_WIDTH = 8;                   // Beat count width
parameter int ID_WIDTH = 3;                      // Channel ID width
parameter int REGISTERED = 1;                    // Registered outputs
```

: Table 2.7.1: Beats Latency Bridge Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low reset |

: Table 2.7.2: Clock and Reset

### Input Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `in_valid` | input | 1 | Input request valid |
| `in_ready` | output | 1 | Bridge ready to accept |
| `in_beats` | input | BEATS_WIDTH | Beat count |
| `in_id` | input | ID_WIDTH | Channel ID |

: Table 2.7.3: Input Interface

### Output Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `out_valid` | output | 1 | Output request valid |
| `out_ready` | input | 1 | Downstream ready |
| `out_beats` | output | BEATS_WIDTH | Beat count (delayed) |
| `out_id` | output | ID_WIDTH | Channel ID (delayed) |

: Table 2.7.4: Output Interface

---

## Operation

### Timing Diagram

### Figure 2.7.2: Latency Bridge Timing (Depth=2)

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    in_valid       _/‾\_____/‾\_____:_______:_______:_______:_______
    in_beats       X| 8 |XXX| 4 |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    out_valid      _________:_______/‾\_____/‾\_____:_______:_______
    out_beats      X:XXXXXXX:XXXXXXX| 8 |XXX| 4 |XXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
                    :       :       :       :       :       :
                    +-------+       +-------+
                    | 2-cycle latency through bridge |
```

**TODO:** Replace with simulation-generated waveform

---

## Integration Context

The latency bridge is used within the SRAM controller:

```systemverilog
// In snk_sram_controller_unit
beats_alloc_ctrl u_alloc (
    // Allocation on fill requests
    .wr_valid       (fill_valid),
    .wr_size        (fill_size),
    // Release on actual data write
    .rd_valid       (sram_wr_complete)
);

beats_latency_bridge u_bridge (
    // Input from SRAM write path
    .in_valid       (sram_wr_complete),
    .in_beats       (beats_written),
    // Output to drain controller (delayed)
    .out_valid      (drain_trigger),
    .out_beats      (drain_beats)
);

beats_drain_ctrl u_drain (
    // Delayed notification of data available
    .wr_valid       (drain_trigger),
    // Drain requests from write engine
    .rd_valid       (axi_drain_req),
    .rd_size        (axi_drain_size)
);
```

---

## Design Considerations

| Depth | Use Case | Latency |
|-------|----------|---------|
| 2 | Minimal pipeline | 2 cycles |
| 4 | Standard pipeline | 4 cycles |
| 8 | Deep pipeline | 8 cycles |

: Table 2.7.5: Bridge Depth Selection

The bridge depth should match the maximum pipeline latency from alloc_ctrl write to SRAM data being valid for drain_ctrl.

---

**Last Updated:** 2025-01-10
