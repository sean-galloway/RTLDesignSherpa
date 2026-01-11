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

# Source Data Path AXIS Wrapper Specification

**Module:** `source_data_path_axis.sv`
**Location:** `projects/components/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The Source Data Path AXIS wrapper adds an AXI-Stream master interface to the source data path, enabling standard AXIS egress for memory-to-network transfers.

### Key Features

- **AXI-Stream Master Interface:** Standard AXIS for data egress
- **Per-Channel TID Mapping:** Drain channel ID maps to AXIS TID
- **TLAST Generation:** Packet boundary marking
- **Core Source Integration:** Wraps source_data_path module

### Block Diagram

### Figure 3.8.1: Source Data Path AXIS Block Diagram

```
                        source_data_path_axis
    +-------------------------------------------------------+
    |                                                       |
    |    AXI Read Master (from System Memory)               |
    |         |                                             |
    |         v                                             |
    |    +-------------------------------------------+      |
    |    |           source_data_path                |      |
    |    |  (axi_read_engine + src_sram_controller)  |      |
    |    +--------------------+----------------------+      |
    |                         |                             |
    |                         v                             |
    |    +-------------------------------------------+      |
    |    |          Drain to AXIS Converter          |      |
    |    |  - drain_id -> TID                        |      |
    |    |  - drain_last -> TLAST                    |      |
    |    |  - drain handshaking -> TVALID/TREADY    |      |
    |    +--------------------+----------------------+      |
    |                         |                             |
    |                         v                             |
    |    +-------------------------------------------+      |
    |    | m_axis_tvalid   m_axis_tready             |      |
    |    | m_axis_tdata    m_axis_tlast              |      |
    |    | m_axis_tid      m_axis_tkeep              |      |
    |    +-------------------------------------------+      |
    |    AXI-Stream Master Interface                        |
    |                                                       |
    +-------------------------------------------------------+
```

**Source:** [03_source_data_path_axis_block.mmd](../assets/mermaid/03_source_data_path_axis_block.mmd)

---

## Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;
parameter int ADDR_WIDTH = 64;
parameter int DATA_WIDTH = 512;
parameter int AXI_ID_WIDTH = 8;
parameter int SRAM_DEPTH = 512;
parameter int TID_WIDTH = 3;                     // log2(NUM_CHANNELS)
parameter int TDEST_WIDTH = 1;
parameter int TUSER_WIDTH = 1;
```

: Table 3.8.1: Source Data Path AXIS Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low reset |

: Table 3.8.2: Clock and Reset

### Scheduler Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_rd_valid` | input | 1 | Read request |
| `sched_rd_addr` | input | AW | Source address |
| `sched_rd_beats` | input | 32 | Beats to read |
| `sched_rd_id` | input | 3 | Channel ID |
| `sched_rd_done_strobe` | output | 1 | Read complete |
| `sched_rd_beats_done` | output | 32 | Beats completed |
| `sched_rd_error` | output | 1 | Error flag |

: Table 3.8.3: Scheduler Interface

### AXI Read Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_arvalid` | output | 1 | AR channel valid |
| `m_axi_arready` | input | 1 | AR channel ready |
| `m_axi_araddr` | output | AW | Read address |
| `m_axi_arlen` | output | 8 | Burst length |
| `m_axi_arsize` | output | 3 | Burst size |
| `m_axi_arburst` | output | 2 | Burst type |
| `m_axi_arid` | output | ID_W | Transaction ID |
| `m_axi_rvalid` | input | 1 | R channel valid |
| `m_axi_rready` | output | 1 | R channel ready |
| `m_axi_rdata` | input | DW | Read data |
| `m_axi_rresp` | input | 2 | Read response |
| `m_axi_rid` | input | ID_W | Response ID |
| `m_axi_rlast` | input | 1 | Last beat |

: Table 3.8.4: AXI Read Master Interface

### AXI-Stream Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axis_tvalid` | output | 1 | Data valid |
| `m_axis_tready` | input | 1 | Ready for data |
| `m_axis_tdata` | output | DATA_WIDTH | Data payload |
| `m_axis_tkeep` | output | DATA_WIDTH/8 | Byte enables |
| `m_axis_tlast` | output | 1 | Last beat of packet |
| `m_axis_tid` | output | TID_WIDTH | Stream ID (channel) |
| `m_axis_tdest` | output | TDEST_WIDTH | Destination |
| `m_axis_tuser` | output | TUSER_WIDTH | User sideband |

: Table 3.8.5: AXI-Stream Master Interface

---

## Signal Mapping

### Figure 3.8.2: Drain to AXIS Interface Mapping

```
    Drain Interface               AXIS Master
    +----------------+            +----------------+
    | src_drain_valid|----------->| m_axis_tvalid  |
    | src_drain_ready|<-----------| m_axis_tready  |
    | src_drain_data |----------->| m_axis_tdata   |
    | src_drain_last |----------->| m_axis_tlast   |
    | src_drain_id   |----------->| m_axis_tid     |
    | src_drain_strb |----------->| m_axis_tkeep   |
    +----------------+            +----------------+
```

**Source:** [03_source_axis_mapping.mmd](../assets/mermaid/03_source_axis_mapping.mmd)

---

## Timing Diagram

### Figure 3.8.3: AXIS Egress Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    sched_rd_valid _/‾‾‾‾‾‾‾\___:_______:_______:_______:_______
    sched_rd_id    X| CH3 |XXXXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    (AXI read + SRAM buffering)
                    :       :       :       :       :       :
    m_axis_tvalid  _______________:_/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___
    m_axis_tready  _______________:_/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
    m_axis_tdata   X:XXXXXXX:XXXXX|=D0=|=D1=|=D2=|=D3=|XXXXXXX
    m_axis_tid     X:XXXXXXX:XXXXX| CH3| CH3| CH3| CH3|XXXXXXX
    m_axis_tlast   _______________:_______________/‾\___:_______
                    :       :       :       :       :       :
    sched_rd_done  _________________________________:_/‾\___:___
```

**TODO:** Replace with simulation-generated waveform showing AXIS packet transmission

---

## Usage Notes

1. **TID Generation:** Drain channel ID directly maps to AXIS TID
2. **TLAST Generation:** Drain last signal maps to AXIS TLAST
3. **Backpressure:** Network TREADY backpressure propagates to SRAM drain
4. **Packet Boundaries:** TLAST marks end of AXIS packets

---

## Integration Example

```systemverilog
source_data_path_axis #(
    .NUM_CHANNELS(8),
    .ADDR_WIDTH(64),
    .DATA_WIDTH(512),
    .TID_WIDTH(3)
) u_source_axis (
    .clk                    (clk),
    .rst_n                  (rst_n),

    // Scheduler interface
    .sched_rd_valid         (sched_rd_valid),
    .sched_rd_addr          (sched_rd_addr),
    .sched_rd_beats         (sched_rd_beats),
    .sched_rd_id            (sched_rd_id),
    .sched_rd_done_strobe   (sched_rd_done_strobe),

    // AXI read master
    .m_axi_arvalid          (src_axi_arvalid),
    .m_axi_arready          (src_axi_arready),
    .m_axi_araddr           (src_axi_araddr),
    .m_axi_rvalid           (src_axi_rvalid),
    .m_axi_rready           (src_axi_rready),
    .m_axi_rdata            (src_axi_rdata),

    // AXIS master
    .m_axis_tvalid          (network_tvalid),
    .m_axis_tready          (network_tready),
    .m_axis_tdata           (network_tdata),
    .m_axis_tlast           (network_tlast),
    .m_axis_tid             (network_tid)
);
```

---

**Last Updated:** 2025-01-10
