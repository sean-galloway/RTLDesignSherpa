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

# Sink SRAM Controller Unit Specification

**Module:** `snk_sram_controller_unit.sv`
**Location:** `projects/components/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The Sink SRAM Controller Unit manages a single channel's SRAM buffer with beat-level flow control using virtual FIFOs (alloc_ctrl and drain_ctrl).

### Key Features

- **Single-Channel SRAM:** Dedicated SRAM buffer for one channel
- **Virtual FIFO Flow Control:** beats_alloc_ctrl + beats_drain_ctrl
- **Latency Bridge:** Compensates for pipeline timing
- **Simple SRAM:** No reset on memory, only on control logic

### Block Diagram

### Figure 3.6.1: Sink SRAM Controller Unit Block Diagram

```
                    snk_sram_controller_unit
    +------------------------------------------------------------------+
    |                                                                  |
    |  Fill Interface                                                  |
    |       |                                                          |
    |       v                                                          |
    |  +-----------------+                                             |
    |  | beats_alloc_ctrl|  <- Space allocation                        |
    |  +--------+--------+                                             |
    |           |                                                      |
    |           v                                                      |
    |  +-----------------+     +------------------+                    |
    |  |   SRAM Write    |---->|   simple_sram    |                    |
    |  |     Logic       |     |                  |                    |
    |  +-----------------+     +--------+---------+                    |
    |                                   |                              |
    |                                   v                              |
    |  +-----------------+     +------------------+                    |
    |  |beats_latency_   |<----|   SRAM Read      |                    |
    |  |    bridge       |     |     Logic        |                    |
    |  +--------+--------+     +------------------+                    |
    |           |                                                      |
    |           v                                                      |
    |  +-----------------+                                             |
    |  | beats_drain_ctrl|  <- Data availability                       |
    |  +--------+--------+                                             |
    |           |                                                      |
    +-----------|------------------------------------------------------+
                v
          Drain Interface (to AXI Write Engine)
```

**Source:** [03_snk_sram_controller_unit_block.mmd](../assets/mermaid/03_snk_sram_controller_unit_block.mmd)

---

## Parameters

```systemverilog
parameter int DATA_WIDTH = 512;
parameter int SRAM_DEPTH = 512;
parameter int ADDR_WIDTH = $clog2(SRAM_DEPTH);
parameter int LATENCY_BRIDGE_DEPTH = 4;
```

: Table 3.6.1: Sink SRAM Controller Unit Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low reset |

: Table 3.6.2: Clock and Reset

### Fill Interface (from Network)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `fill_alloc_req` | input | 1 | Allocate space |
| `fill_alloc_size` | input | 16 | Beats to allocate |
| `fill_space_free` | output | 16 | Available space |
| `fill_valid` | input | 1 | Fill data valid |
| `fill_ready` | output | 1 | Ready for fill data |
| `fill_data` | input | DW | Fill data |
| `fill_last` | input | 1 | Last beat marker |

: Table 3.6.3: Fill Interface

### Drain Interface (to AXI Write Engine)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `drain_req` | output | 1 | Data available to drain |
| `drain_gnt` | input | 1 | Drain grant |
| `drain_beats` | output | 16 | Beats available |
| `sram_rd_en` | input | 1 | SRAM read enable |
| `sram_rd_addr` | input | AW | SRAM read address |
| `sram_rd_data` | output | DW | SRAM read data |

: Table 3.6.4: Drain Interface

### Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `data_avail` | output | 1 | Data available flag |
| `empty` | output | 1 | Buffer empty |
| `full` | output | 1 | Buffer full |

: Table 3.6.5: Status Interface

---

## Internal Architecture

### Figure 3.6.2: Internal Data Flow

```
Fill Path:

   fill_alloc_req -----> beats_alloc_ctrl -----> wr_ptr management
                              |
   fill_valid/data ---------> | -----> SRAM write
                              |
   fill_ready <-------------- | <----- space_free > 0


Drain Path:

   SRAM read <--------------- | <----- sram_rd_en
        |                     |
        v                     |
   beats_latency_bridge ------+-----> timing compensation
        |                     |
        v                     |
   beats_drain_ctrl ----------+-----> data_avail tracking
        |
        v
   drain_req -----------------> channel arbiter
```

---

## Timing Diagram

### Figure 3.6.3: Fill and Drain Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    fill_alloc_req _/‾\___:_______:_______:_______:_______:_______
    fill_alloc_size| 4 |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
    fill_space_free|512|508|XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    fill_valid     _______/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______:_______
    fill_data      X:XXXXX|=D0=|=D1=|=D2=|=D3=|XXX:XXXXXXX:XXXXXXX
    fill_ready     _‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______
                    :       :       :       :       :       :
    (latency)       :       :       :       :       :       :
                    :       :       :       :       :       :
    data_avail     _______________:_______:_/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
    drain_req      _______________:_______:_/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
    drain_beats    X:XXXXXXX:XXXXXXX:XXXXXXX| 4 |XXXXXXXXX:XXXXXXX
```

**TODO:** Replace with simulation-generated waveform showing complete fill-to-drain flow

---

## Virtual FIFO Concept

The controller uses "virtual FIFOs" - pointer-based flow control without duplicating data storage:

### Figure 3.6.4: Virtual FIFO Operation

```
                    SRAM Buffer (actual data storage)
    +-----------------------------------------------------------+
    |  [0]  |  [1]  |  [2]  |  [3]  |  [4]  | ... | [511]      |
    +-----------------------------------------------------------+
         ^                      ^
         |                      |
      rd_ptr                 wr_ptr

    beats_alloc_ctrl: Tracks wr_ptr, manages free space
    beats_drain_ctrl: Tracks rd_ptr, manages data availability

    No data duplication - just pointer arithmetic!
```

---

## Integration Example

```systemverilog
snk_sram_controller_unit #(
    .DATA_WIDTH(512),
    .SRAM_DEPTH(512),
    .LATENCY_BRIDGE_DEPTH(4)
) u_snk_sram_unit (
    .clk                (clk),
    .rst_n              (rst_n),

    // Fill interface
    .fill_alloc_req     (fill_alloc_req[ch]),
    .fill_alloc_size    (fill_alloc_size[ch]),
    .fill_space_free    (fill_space_free[ch]),
    .fill_valid         (fill_valid[ch]),
    .fill_ready         (fill_ready[ch]),
    .fill_data          (fill_data[ch]),
    .fill_last          (fill_last[ch]),

    // Drain interface
    .drain_req          (drain_req[ch]),
    .drain_gnt          (drain_gnt[ch]),
    .drain_beats        (drain_beats[ch]),
    .sram_rd_en         (sram_rd_en[ch]),
    .sram_rd_addr       (sram_rd_addr[ch]),
    .sram_rd_data       (sram_rd_data[ch]),

    // Status
    .data_avail         (data_avail[ch]),
    .empty              (empty[ch]),
    .full               (full[ch])
);
```

---

**Last Updated:** 2025-01-10
