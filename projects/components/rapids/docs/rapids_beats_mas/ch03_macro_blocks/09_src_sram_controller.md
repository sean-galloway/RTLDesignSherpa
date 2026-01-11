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

# Source SRAM Controller Specification

**Module:** `src_sram_controller.sv`
**Location:** `projects/components/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The Source SRAM Controller manages 8 SRAM controller units for the source data path, providing per-channel buffering with channel arbitration for data delivery to the network.

### Key Features

- **8-Channel SRAM Array:** Instantiates 8 `src_sram_controller_unit` modules
- **Channel Arbitration:** Round-robin access for drain requests
- **Flow Control Integration:** Per-channel alloc_ctrl and drain_ctrl
- **Data Availability Tracking:** Reports available data per channel

### Block Diagram

### Figure 3.9.1: Source SRAM Controller Block Diagram

```
                    src_sram_controller
    +------------------------------------------------------------------+
    |                                                                  |
    |    SRAM Write Interface (from AXI Read Engine)                   |
    |         |         |                   |                          |
    |         v         v                   v                          |
    |  +----------+ +----------+     +----------+                      |
    |  |src_sram_ | |src_sram_ | ... |src_sram_ |                      |
    |  |ctrl_unit | |ctrl_unit |     |ctrl_unit |                      |
    |  |   [0]    | |   [1]    |     |   [7]    |                      |
    |  +----+-----+ +----+-----+     +----+-----+                      |
    |       |            |                |                            |
    |       |drain_req   |drain_req       |drain_req                   |
    |       v            v                v                            |
    |  +----------------------------------------------------------+   |
    |  |         Round-Robin Channel Arbiter                      |   |
    |  +----------------------------+-----------------------------+   |
    |                               |                                  |
    |                               v                                  |
    |                    Drain Interface                               |
    |                    (to Network Master)                           |
    |                                                                  |
    +------------------------------------------------------------------+
```

**Source:** [03_src_sram_controller_block.mmd](../assets/mermaid/03_src_sram_controller_block.mmd)

---

## Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;
parameter int DATA_WIDTH = 512;
parameter int SRAM_DEPTH = 512;                  // Per-channel depth
parameter int ADDR_WIDTH = $clog2(SRAM_DEPTH);
```

: Table 3.9.1: Source SRAM Controller Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low reset |

: Table 3.9.2: Clock and Reset

### Per-Channel Fill Interface (from AXI Read Engine)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_fill_alloc_req` | input | NC | Allocation request per channel |
| `src_fill_alloc_size` | input | NC*16 | Beats to allocate |
| `src_fill_space_free` | output | NC*16 | Available space per channel |
| `src_fill_valid` | input | NC | Fill data valid |
| `src_fill_ready` | output | NC | Ready for fill data |
| `src_fill_data` | input | NC*DW | Fill data |
| `src_fill_last` | input | NC | Last beat marker |

: Table 3.9.3: Per-Channel Fill Interface

### Arbitrated Drain Interface (to Network)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `drain_valid` | output | 1 | Drain data valid |
| `drain_ready` | input | 1 | Ready for drain |
| `drain_data` | output | DW | Drain data |
| `drain_id` | output | 3 | Source channel ID |
| `drain_last` | output | 1 | Last beat of transfer |

: Table 3.9.4: Arbitrated Drain Interface

### Per-Channel Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `channel_data_avail` | output | NC*16 | Data available per channel |
| `channel_empty` | output | NC | Channel empty flags |
| `channel_full` | output | NC | Channel full flags |

: Table 3.9.5: Per-Channel Status

---

## Arbitration Logic

### Figure 3.9.2: Source Channel Arbitration

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    data_avail[0]  _/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______:_______
    data_avail[1]  _______/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______
    data_avail[2]  _______________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___
                    :       :       :       :       :       :
    drain_valid    _/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
    drain_id       X| CH0 | CH0 | CH1 | CH1 | CH2 | CH2 |XXXXX
    drain_ready    _/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
```

**TODO:** Replace with simulation-generated waveform showing round-robin drain

---

## Comparison: Sink vs Source SRAM Controller

| Aspect | Sink Controller | Source Controller |
|--------|-----------------|-------------------|
| Fill Source | Network ingress | AXI read data |
| Drain Destination | AXI write engine | Network egress |
| Fill Interface | Per-channel from network | Per-channel from AXI R |
| Drain Interface | Arbitrated SRAM read | Arbitrated drain to network |
| Primary Use | Network -> Memory | Memory -> Network |

: Table 3.9.6: Sink vs Source Controller Comparison

---

## Integration Example

```systemverilog
src_sram_controller #(
    .NUM_CHANNELS(8),
    .DATA_WIDTH(512),
    .SRAM_DEPTH(512)
) u_src_sram_ctrl (
    .clk                    (clk),
    .rst_n                  (rst_n),

    // Per-channel fill interface (from AXI read engine)
    .src_fill_alloc_req     (fill_alloc_req),
    .src_fill_alloc_size    (fill_alloc_size),
    .src_fill_space_free    (fill_space_free),
    .src_fill_valid         (fill_valid),
    .src_fill_ready         (fill_ready),
    .src_fill_data          (fill_data),
    .src_fill_last          (fill_last),

    // Arbitrated drain interface (to network)
    .drain_valid            (src_drain_valid),
    .drain_ready            (src_drain_ready),
    .drain_data             (src_drain_data),
    .drain_id               (src_drain_id),
    .drain_last             (src_drain_last),

    // Status
    .channel_data_avail     (channel_data_avail),
    .channel_empty          (channel_empty),
    .channel_full           (channel_full)
);
```

---

**Last Updated:** 2025-01-10
