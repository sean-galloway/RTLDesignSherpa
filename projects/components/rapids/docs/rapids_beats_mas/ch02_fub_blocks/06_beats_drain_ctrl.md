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

# Beats Drain Control Specification

**Module:** `beats_drain_ctrl.sv`
**Location:** `projects/components/rapids/rtl/fub_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The Beats Drain Control is a "virtual FIFO" that tracks data availability without storing actual data. It complements beats_alloc_ctrl by tracking when data has been written to SRAM and is available for draining.

### Key Features

- **Virtual FIFO:** Pointer tracking without data storage
- **Single-Beat Write:** Data arrivals tracked one beat at a time
- **Variable-Size Drain:** Supports multi-beat drain requests
- **Status Flags:** Full, almost full, empty, almost empty
- **Data Availability:** Reports beats available for drain

### Block Diagram

### Figure 2.6.1: Beats Drain Control Block Diagram

```
                +---------------------------+
    wr_valid -->|                           |--> wr_ready
                |    BEATS_DRAIN_CTRL       |--> data_avail
    rd_valid -->|                           |
    rd_size  -->|     (Virtual FIFO)        |--> wr_full
                |                           |--> wr_almost_full
                |  [No data storage]        |--> rd_empty
                |  [Pointer arithmetic]     |--> rd_almost_empty
                +---------------------------+
```

**Source:** [02_beats_drain_ctrl_block.mmd](../assets/mermaid/02_beats_drain_ctrl_block.mmd)

---

## Concept: Data Availability Tracking

The drain_ctrl tracks when data has been written to SRAM:

```
alloc_ctrl:  Tracks SPACE reservations (allocation -> actual write)
drain_ctrl:  Tracks DATA availability (data write -> drain request)
```

### Complementary Roles

```
Source Path:
  1. Scheduler allocates space (alloc_ctrl.wr)
  2. AXI reads data into SRAM
  3. Data written to SRAM (drain_ctrl.wr)
  4. Drain consumer reads (drain_ctrl.rd)

Sink Path:
  1. Fill allocates space (alloc_ctrl.wr)
  2. Fill writes to SRAM (alloc_ctrl.rd)
  3. Data available in SRAM (drain_ctrl.wr)
  4. AXI write drains SRAM (drain_ctrl.rd)
```

---

## Parameters

```systemverilog
parameter int DEPTH = 512;                      // Virtual FIFO depth
parameter int ALMOST_WR_MARGIN = 1;             // Almost full margin
parameter int ALMOST_RD_MARGIN = 1;             // Almost empty margin
parameter int REGISTERED = 1;                   // Registered outputs

// Derived
parameter int AW = $clog2(DEPTH);               // Address width
```

: Table 2.6.1: Beats Drain Control Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `axi_aclk` | input | 1 | System clock |
| `axi_aresetn` | input | 1 | Active-low reset |

: Table 2.6.2: Clock and Reset

### Write Interface (Data Written to SRAM)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `wr_valid` | input | 1 | One beat written to SRAM |
| `wr_ready` | output | 1 | Can track more data |

: Table 2.6.3: Write Interface

### Read Interface (Drain Requests)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `rd_valid` | input | 1 | Drain request |
| `rd_size` | input | 8 | Number of beats to drain |
| `rd_ready` | output | 1 | Data available for drain |

: Table 2.6.4: Read Interface

### Status Outputs

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `data_avail` | output | AW+1 | Beats available to drain |
| `wr_full` | output | 1 | Tracking full |
| `wr_almost_full` | output | 1 | Near full |
| `rd_empty` | output | 1 | No data to drain |
| `rd_almost_empty` | output | 1 | Near empty |

: Table 2.6.5: Status Outputs

---

## Operation

### Pointer Arithmetic

```
data_avail = wr_ptr - rd_ptr

Full condition:    wr_ptr - rd_ptr >= DEPTH
Empty condition:   wr_ptr == rd_ptr
```

### Timing Diagram

### Figure 2.6.2: Data Arrival and Drain Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    wr_valid       _/‾\_____/‾\_____/‾\_____/‾\_____:_______:_______
                    :       :       :       :       :       :
    rd_valid       _________:_______:_______:_______/‾\_____:_______
    rd_size        X:XXXXXXX:XXXXXXX:XXXXXXX| 4 |XXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    data_avail     |== 0 ===|== 1 ==|== 2 ==|== 3 ==|== 4 ==|== 0 ==
                    :       :       :       :       :       :
    rd_empty       ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾/‾‾‾‾‾‾‾
```

**TODO:** Replace with simulation-generated waveform showing actual flow control

---

## Integration Example

```systemverilog
// Sink path: Track data availability for AXI write engine
beats_drain_ctrl #(
    .DEPTH(SRAM_DEPTH),
    .ALMOST_RD_MARGIN(8)
) u_snk_drain (
    .axi_aclk       (clk),
    .axi_aresetn    (rst_n),

    // Fill writes data to SRAM
    .wr_valid       (fill_valid && fill_ready),
    .wr_ready       (),  // Single-beat, always ready

    // AXI write engine drains data
    .rd_valid       (axi_wr_drain_req),
    .rd_size        (axi_wr_burst_len),
    .rd_ready       (data_ready_for_drain),

    // Status
    .data_avail     (beats_to_write),
    .rd_empty       (no_data_to_write)
);
```

---

## Relationship: alloc_ctrl vs drain_ctrl

| Aspect | beats_alloc_ctrl | beats_drain_ctrl |
|--------|------------------|------------------|
| **Tracks** | Space reservations | Data availability |
| **Write port** | Multi-beat allocation | Single-beat arrival |
| **Read port** | Single-beat release | Multi-beat drain |
| **Output** | `space_free` | `data_avail` |
| **Use case** | Pre-allocate before fill | Know when to drain |

: Table 2.6.6: alloc_ctrl vs drain_ctrl Comparison

---

**Last Updated:** 2025-01-10
