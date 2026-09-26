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

# Sink SRAM Controller Specification

**Module:** `snk_sram_controller_beats.sv`
**Location:** `projects/components/dmas/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The Sink SRAM Controller manages 8 SRAM controller units, providing per-channel buffering with channel arbitration for the shared AXI write engine.

### Key Features

- **8-Channel SRAM Array:** Instantiates 8 `snk_sram_controller_unit` modules
- **Channel Arbitration:** Round-robin access to shared AXI write engine
- **Flow Control Integration:** Per-channel alloc_ctrl and drain_ctrl
- **Space Tracking:** Reports available space per channel

### Block Diagram

### Figure 3.5.1: Sink SRAM Controller Block Diagram

```
                    snk_sram_controller
    +------------------------------------------------------------------+
    |                                                                  |
    |  Fill Interface (per-channel)                                    |
    |         |         |                   |                          |
    |         v         v                   v                          |
    |  +----------+ +----------+     +----------+                      |
    |  |snk_sram_ | |snk_sram_ | ... |snk_sram_ |                      |
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
    |                    SRAM Read Interface                           |
    |                    (to AXI Write Engine)                         |
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

: Table 3.5.1: Sink SRAM Controller Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low reset |

: Table 3.5.2: Clock and Reset

### Fill Interface (ID-Selected)

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

: Table 3.5.3: Fill Interface (ID-Selected)

### Arbitrated Drain Interface (to AXI Write Engine)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `drain_data_avail` | output | NC x SCW | Data available per channel |
| `drain_req` | input | NC | Drain reservation request per channel |
| `drain_size` | input | NC x 8 | Beats to reserve |
| `drain_valid` | output | NC | Drain valid, registered (for arbitration) |
| `drain_valid_comb` | output | NC | Drain valid, combinational (gates `m_axi_wvalid`) |
| `drain_read` | input | 1 | Consumer read strobe |
| `drain_id` | input | CIW | Channel ID select for drain |
| `drain_data` | output | DW | Drain data (muxed from selected channel) |

: Table 3.5.4: Arbitrated Drain Interface

### Debug Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `dbg_bridge_pending` | output | NC | Bridge has a pending beat per channel |
| `dbg_bridge_out_valid` | output | NC | Bridge output valid per channel |

: Table 3.5.5: Debug Interface

---

## Arbitration Logic

### Figure 3.5.2: Channel Arbitration Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    drain_req[0]   _/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______:_______:_______
    drain_req[1]   _______/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______:_______
    drain_req[2]   _______________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______
                    :       :       :       :       :       :
    drain_id       X| CH0  | CH0  | CH1  | CH1  | CH2  | CH2  |XXXXX
    drain_gnt      _/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___
                    :       :       :       :       :       :
```

**TODO:** Replace with simulation-generated waveform showing round-robin arbitration

---

## Integration with AXI Write Engine

```systemverilog
snk_sram_controller #(
    .NUM_CHANNELS(8),
    .DATA_WIDTH(512),
    .SRAM_DEPTH(512)
) u_snk_sram_ctrl (
    .clk                    (clk),
    .rst_n                  (rst_n),

    // Per-channel fill interface
    .snk_fill_alloc_req     (fill_alloc_req),
    .snk_fill_alloc_size    (fill_alloc_size),
    .snk_fill_space_free    (fill_space_free),
    .snk_fill_valid         (fill_valid),
    .snk_fill_ready         (fill_ready),
    .snk_fill_data          (fill_data),
    .snk_fill_last          (fill_last),

    // Arbitrated drain interface
    .drain_req              (sram_drain_req),
    .drain_gnt              (sram_drain_gnt),
    .drain_id               (sram_drain_id),
    .drain_beats            (sram_drain_beats),
    .sram_rd_en             (sram_rd_en),
    .sram_rd_addr           (sram_rd_addr),
    .sram_rd_data           (sram_rd_data),

    // Status
    .channel_data_avail     (channel_data_avail),
    .channel_empty          (channel_empty),
    .channel_full           (channel_full)
);
```

---

**Last Updated:** 2025-01-10
