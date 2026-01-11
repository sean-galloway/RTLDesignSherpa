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

# Beats Alloc Control Specification

**Module:** `beats_alloc_ctrl.sv`
**Location:** `projects/components/rapids/rtl/fub_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The Beats Alloc Control is a "virtual FIFO" that tracks space allocation without storing actual data. It uses FIFO pointer logic to manage pre-allocation for AXI engines, preventing race conditions between allocation and actual data arrival.

### Key Features

- **Virtual FIFO:** Pointer tracking without data storage
- **Variable-Size Allocation:** Supports multi-beat allocation requests
- **Single-Beat Release:** Data writes release one beat at a time
- **Status Flags:** Full, almost full, empty, almost empty
- **Space Tracking:** Reports available space for flow control

### Block Diagram

### Figure 2.5.1: Beats Alloc Control Block Diagram

```
                +---------------------------+
    wr_valid -->|                           |--> wr_ready
    wr_size  -->|    BEATS_ALLOC_CTRL       |--> space_free
                |                           |
    rd_valid -->|     (Virtual FIFO)        |--> wr_full
                |                           |--> wr_almost_full
                |  [No data storage]        |--> rd_empty
                |  [Pointer arithmetic]     |--> rd_almost_empty
                +---------------------------+
```

**Source:** [02_beats_alloc_ctrl_block.mmd](../assets/mermaid/02_beats_alloc_ctrl_block.mmd)

---

## Concept: Virtual FIFO

Unlike a traditional FIFO that stores data, beats_alloc_ctrl only tracks **space reservations**:

```
Traditional FIFO:          Virtual FIFO (alloc_ctrl):

  wr_data --> [storage] -> rd_data    wr_size --> [pointers] --> space_free

  Data moves through FIFO             Only pointers move, no data
```

### Use Case: Pre-Allocation for AXI Reads

```
1. AXI engine requests N beats of space
   - alloc_ctrl.wr_valid = 1
   - alloc_ctrl.wr_size = N
   - wr_ptr advances by N

2. As AXI read data arrives (1 beat at a time)
   - alloc_ctrl.rd_valid = 1 (each beat)
   - rd_ptr advances by 1

3. Space becomes available again
   - space_free reflects available capacity
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

: Table 2.5.1: Beats Alloc Control Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `axi_aclk` | input | 1 | System clock |
| `axi_aresetn` | input | 1 | Active-low reset |

: Table 2.5.2: Clock and Reset

### Write Interface (Allocation Requests)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `wr_valid` | input | 1 | Allocate space |
| `wr_size` | input | 8 | Number of beats to allocate |
| `wr_ready` | output | 1 | Space available for allocation |

: Table 2.5.3: Write Interface

### Read Interface (Data Written)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `rd_valid` | input | 1 | One beat of data written |
| `rd_ready` | output | 1 | Not full (can accept) |

: Table 2.5.4: Read Interface

### Status Outputs

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `space_free` | output | AW+1 | Available space in beats |
| `wr_full` | output | 1 | No space available |
| `wr_almost_full` | output | 1 | Near full |
| `rd_empty` | output | 1 | No allocations pending |
| `rd_almost_empty` | output | 1 | Near empty |

: Table 2.5.5: Status Outputs

---

## Operation

### Pointer Arithmetic

```
space_free = DEPTH - (wr_ptr - rd_ptr)

Full condition:    wr_ptr - rd_ptr >= DEPTH
Empty condition:   wr_ptr == rd_ptr
```

### Timing Diagram

### Figure 2.5.2: Allocation and Release Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    wr_valid       _/‾\_____:_______:_______:_______:_______:_______
    wr_size        X| 8 |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    rd_valid       _________/‾\_____/‾\_____/‾\_____/‾\_____/‾\_____
                    :       :       :       :       :       :
    space_free     |==512===|==504==|==505==|==506==|==507==|==508==
                    :       :       :       :       :       :
    wr_ptr         |== 0 ===|== 8 ==|== 8 ==|== 8 ==|== 8 ==|== 8 ==
    rd_ptr         |== 0 ===|== 0 ==|== 1 ==|== 2 ==|== 3 ==|== 4 ==
```

**TODO:** Replace with simulation-generated waveform showing actual flow control

---

## Integration Example

```systemverilog
// Source path: Pre-allocate SRAM space before AXI read
beats_alloc_ctrl #(
    .DEPTH(SRAM_DEPTH),
    .ALMOST_WR_MARGIN(8)
) u_src_alloc (
    .axi_aclk       (clk),
    .axi_aresetn    (rst_n),

    // Scheduler allocates space before issuing AXI read
    .wr_valid       (sched_rd_valid),
    .wr_size        (sched_rd_beats[7:0]),
    .wr_ready       (alloc_ready),

    // AXI read data arrival releases allocation
    .rd_valid       (m_axi_rvalid && m_axi_rready),
    .rd_ready       (),  // Not used for single-beat

    // Status
    .space_free     (sram_space_available),
    .wr_full        (sram_full),
    .wr_almost_full (sram_almost_full)
);
```

---

**Last Updated:** 2025-01-10
