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

# Source SRAM Controller Unit Specification

**Module:** `src_sram_controller_unit.sv`
**Location:** `projects/components/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The Source SRAM Controller Unit manages a single channel's SRAM buffer for the source data path, with beat-level flow control using virtual FIFOs.

### Key Features

- **Single-Channel SRAM:** Dedicated SRAM buffer for one channel
- **Virtual FIFO Flow Control:** beats_alloc_ctrl + beats_drain_ctrl
- **Latency Bridge:** Compensates for pipeline timing
- **Simple SRAM:** No reset on memory, only on control logic

### Block Diagram

### Figure 3.10.1: Source SRAM Controller Unit Block Diagram

```
                    src_sram_controller_unit
    +------------------------------------------------------------------+
    |                                                                  |
    |  Fill Interface (from AXI Read Engine)                           |
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
          Drain Interface (to Network)
```

**Source:** [03_src_sram_controller_unit_block.mmd](../assets/mermaid/03_src_sram_controller_unit_block.mmd)

---

## Parameters

```systemverilog
parameter int DATA_WIDTH = 512;
parameter int SRAM_DEPTH = 512;
parameter int ADDR_WIDTH = $clog2(SRAM_DEPTH);
parameter int LATENCY_BRIDGE_DEPTH = 4;
```

: Table 3.10.1: Source SRAM Controller Unit Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low reset |

: Table 3.10.2: Clock and Reset

### Fill Interface (from AXI Read Engine)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `fill_alloc_req` | input | 1 | Allocate space |
| `fill_alloc_size` | input | 16 | Beats to allocate |
| `fill_space_free` | output | 16 | Available space |
| `fill_valid` | input | 1 | Fill data valid |
| `fill_ready` | output | 1 | Ready for fill data |
| `fill_data` | input | DW | Fill data |
| `fill_last` | input | 1 | Last beat marker |

: Table 3.10.3: Fill Interface

### Drain Interface (to Network)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `drain_req` | output | 1 | Data available to drain |
| `drain_gnt` | input | 1 | Drain grant from arbiter |
| `drain_beats` | output | 16 | Beats available |
| `drain_valid` | output | 1 | Drain data valid |
| `drain_ready` | input | 1 | Network ready |
| `drain_data` | output | DW | Drain data |
| `drain_last` | output | 1 | Last beat marker |

: Table 3.10.4: Drain Interface

### Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `data_avail` | output | 16 | Data available count |
| `empty` | output | 1 | Buffer empty |
| `full` | output | 1 | Buffer full |

: Table 3.10.5: Status Interface

---

## Internal Architecture

### Figure 3.10.2: Internal Data Flow

```
Fill Path (from AXI Read Engine):

   fill_alloc_req -----> beats_alloc_ctrl -----> wr_ptr management
                              |
   fill_valid/data ---------> | -----> SRAM write
                              |
   fill_ready <-------------- | <----- space_free > 0


Drain Path (to Network):

   SRAM read <--------------- | <----- drain_gnt && drain_ready
        |                     |
        v                     |
   beats_latency_bridge ------+-----> timing compensation
        |                     |
        v                     |
   beats_drain_ctrl ----------+-----> data_avail tracking
        |
        v
   drain_req -----------------> channel arbiter
   drain_valid/data ----------> network interface
```

---

## Comparison: Sink vs Source Unit

| Aspect | Sink Unit | Source Unit |
|--------|-----------|-------------|
| Fill Source | Network | AXI Read Engine |
| Drain Destination | AXI Write Engine | Network |
| Fill Handshake | fill_valid/ready | fill_valid/ready |
| Drain Handshake | SRAM read interface | drain_valid/ready |
| Primary Direction | Network -> SRAM -> AXI | AXI -> SRAM -> Network |

: Table 3.10.6: Sink vs Source Unit Comparison

---

## Timing Diagram

### Figure 3.10.3: Source Unit Fill and Drain Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    fill_alloc_req _/‾\___:_______:_______:_______:_______:_______
    fill_alloc_size| 4 |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    fill_valid     _______/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______:_______
    fill_data      X:XXXXX|=D0=|=D1=|=D2=|=D3=|XXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    (latency bridge)
                    :       :       :       :       :       :
    data_avail     _______________:_______:_| 4  |XXXXXXXXX:XXXXXXX
    drain_req      _______________:_______:_/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
    drain_gnt      _______________:_______:_______/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
    drain_valid    _______________:_______:_______/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
    drain_data     X:XXXXXXX:XXXXXXX:XXXXXXX:XXXXX|=D0=|=D1=|=D2=|
```

**TODO:** Replace with simulation-generated waveform showing complete flow

---

## Integration Example

```systemverilog
src_sram_controller_unit #(
    .DATA_WIDTH(512),
    .SRAM_DEPTH(512),
    .LATENCY_BRIDGE_DEPTH(4)
) u_src_sram_unit (
    .clk                (clk),
    .rst_n              (rst_n),

    // Fill interface (from AXI read engine)
    .fill_alloc_req     (fill_alloc_req[ch]),
    .fill_alloc_size    (fill_alloc_size[ch]),
    .fill_space_free    (fill_space_free[ch]),
    .fill_valid         (fill_valid[ch]),
    .fill_ready         (fill_ready[ch]),
    .fill_data          (fill_data[ch]),
    .fill_last          (fill_last[ch]),

    // Drain interface (to network)
    .drain_req          (drain_req[ch]),
    .drain_gnt          (drain_gnt[ch]),
    .drain_beats        (drain_beats[ch]),
    .drain_valid        (drain_valid[ch]),
    .drain_ready        (drain_ready[ch]),
    .drain_data         (drain_data[ch]),
    .drain_last         (drain_last[ch]),

    // Status
    .data_avail         (data_avail[ch]),
    .empty              (empty[ch]),
    .full               (full[ch])
);
```

---

**Last Updated:** 2025-01-10
