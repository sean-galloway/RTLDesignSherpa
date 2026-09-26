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

**Module:** `src_sram_controller_beats.sv`
**Location:** `projects/components/dmas/rapids/rtl/macro_beats/`
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

### Fill Interface (ID-Selected, from AXI Read Engine)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `fill_alloc_req` | input | 1 | Allocation request (single, ID-selected) |
| `fill_alloc_size` | input | 8 | Beats to allocate |
| `fill_alloc_id` | input | CIW | Transaction ID selects the channel |
| `fill_space_free` | output | NC x SCW | Available space per channel |
| `fill_valid` | input | 1 | Fill data valid |
| `fill_ready` | output | 1 | Ready for fill data |
| `fill_id` | input | CIW | Transaction ID selects the channel |
| `fill_data` | input | DW | Fill data |

: Table 3.9.3: Fill Interface (ID-Selected)

### Arbitrated Drain Interface (to Network)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `drain_data_avail` | output | NC x SCW | Data available per channel |
| `drain_req` | input | NC | Drain reservation request per channel |
| `drain_size` | input | NC x 8 | Beats to reserve |
| `drain_valid` | output | NC | Drain data valid per channel |
| `drain_read` | input | 1 | Consumer read strobe |
| `drain_id` | input | CIW | Channel ID select for drain |
| `drain_data` | output | DW | Drain data (muxed from selected channel) |

: Table 3.9.4: Arbitrated Drain Interface

### Debug Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `dbg_bridge_pending` | output | NC | Bridge has a pending beat per channel |
| `dbg_bridge_out_valid` | output | NC | Bridge output valid per channel |

: Table 3.9.5: Debug Interface

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
src_sram_controller_beats #(
    .NUM_CHANNELS(8),
    .DATA_WIDTH(512),
    .SRAM_DEPTH(512)
) u_src_sram_ctrl (
    .clk                    (clk),
    .rst_n                  (rst_n),

    // Per-channel fill interface (from AXI read engine)
    .fill_alloc_req         (fill_alloc_req),
    .fill_alloc_size        (fill_alloc_size),
    .fill_space_free        (fill_space_free),
    .fill_valid             (fill_valid),
    .fill_ready             (fill_ready),
    .fill_data              (fill_data),

    // Arbitrated drain interface (to network)
    .drain_valid            (src_drain_valid),
    .drain_data             (src_drain_data),
    .drain_id               (src_drain_id),

    // Status
    .drain_data_avail       (channel_data_avail),
    .dbg_bridge_pending     (channel_empty),
    .dbg_bridge_out_valid   (channel_full)
);
```

---

**Last Updated:** 2025-01-10
