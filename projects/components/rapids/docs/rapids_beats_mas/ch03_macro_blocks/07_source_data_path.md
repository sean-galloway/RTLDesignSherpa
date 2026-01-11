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

# Source Data Path Specification

**Module:** `source_data_path.sv`
**Location:** `projects/components/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The Source Data Path integrates the AXI read engine and SRAM controller for memory-to-network transfers. Data is read from system memory via AXI4, buffered in SRAM, and delivered through the drain interface to the network.

### Key Features

- **AXI Read Engine:** Streaming burst reads from system memory
- **8-Channel SRAM Controller:** Per-channel buffering with flow control
- **Beat-Level Tracking:** Precise flow control at beat granularity
- **Scheduler Integration:** Receives transfer requests from scheduler

### Block Diagram

### Figure 3.7.1: Source Data Path Block Diagram

```
                        source_data_path
    +-------------------------------------------------------+
    |                                                       |
    |    AXI Read Master (from System Memory)               |
    |         |                                             |
    |         v                                             |
    |  +---------------------------------------------+      |
    |  |            axi_read_engine                  |      |
    |  |  - AR channel management                    |      |
    |  |  - R channel streaming                      |      |
    |  |  - Burst generation                         |      |
    |  +------------------+------------------------+        |
    |                     |                                 |
    |                     v                                 |
    |  +---------------------------------------------+      |
    |  |         src_sram_controller                 |      |
    |  |  +-------+  +-------+       +-------+       |      |
    |  |  | unit  |  | unit  |  ...  | unit  |       |      |
    |  |  |  [0]  |  |  [1]  |       |  [7]  |       |      |
    |  |  +-------+  +-------+       +-------+       |      |
    |  +------------------+------------------------+        |
    |                     |                                 |
    |                     v                                 |
    +---------------------|--------------------------------+
                          |
                   Drain Interface
                 (to Network Master)
```

**Source:** [03_source_data_path_block.mmd](../assets/mermaid/03_source_data_path_block.mmd)

---

## Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;
parameter int ADDR_WIDTH = 64;
parameter int DATA_WIDTH = 512;
parameter int AXI_ID_WIDTH = 8;
parameter int SRAM_DEPTH = 512;
parameter int AR_MAX_OUTSTANDING = 8;
parameter int R_PHASE_FIFO_DEPTH = 64;
```

: Table 3.7.1: Source Data Path Parameters

---

## Data Flow

### Figure 3.7.2: Source Path Data Flow Sequence

```
1. Scheduler Read Request
   - sched_rd_valid = 1
   - sched_rd_addr = source address
   - sched_rd_beats = N
   - sched_rd_id = channel
        |
        v
2. Space Check (beats_alloc_ctrl)
   - Check src_drain_space_free[channel] >= N
   - Allocate N beats of space
        |
        v
3. AXI Read Transaction
   - axi_read_engine issues AR
   - m_axi_araddr = sched_rd_addr
   - m_axi_arlen = calculated from beats
        |
        v
4. R Channel Data
   - Data arrives on m_axi_rdata
   - Written to channel's SRAM partition
        |
        v
5. SRAM Write Complete
   - beats_drain_ctrl notified via latency bridge
   - Data available for drain
        |
        v
6. Drain Interface
   - src_drain_valid = 1
   - Data delivered to network master
        |
        v
7. Completion
   - sched_rd_done_strobe = 1
   - Scheduler notified of completion
```

**Source:** [03_source_data_flow.mmd](../assets/mermaid/03_source_data_flow.mmd)

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low reset |

: Table 3.7.2: Clock and Reset

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

: Table 3.7.3: Scheduler Interface

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

: Table 3.7.4: AXI Read Master Interface

### Drain Interface (Output to Network)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_drain_valid` | output | 1 | Drain data valid |
| `src_drain_ready` | input | 1 | Ready for drain data |
| `src_drain_data` | output | DW | Drain data |
| `src_drain_last` | output | 1 | Last beat marker |
| `src_drain_id` | output | 3 | Channel ID |
| `src_drain_data_avail` | output | NC*16 | Available data per channel |

: Table 3.7.5: Drain Interface

---

## Timing Diagram

### Figure 3.7.3: Source Path Transfer Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    sched_rd_valid _/‾‾‾‾‾‾‾\___:_______:_______:_______:_______
    sched_rd_beats X| 4 |XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
    sched_rd_addr  X|ADDR|XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    m_axi_arvalid  _______/‾\___:_______:_______:_______:_______
    m_axi_arlen    X:XXXXX| 3 |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    m_axi_rvalid   ___________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\___:_______
    m_axi_rdata    X:XXXXXXX|=D0=|=D1=|=D2=|=D3=|XXX:XXXXXXX
    m_axi_rlast    _________________________/‾\___:_______:_______
                    :       :       :       :       :       :
    src_drain_valid ___________________:_______/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
    src_drain_data X:XXXXXXX:XXXXXXX:XXXXXXX|=D0=|=D1=|=D2=|=D3=|
                    :       :       :       :       :       :
    sched_rd_done  _________________________________:_______/‾\___
```

**TODO:** Replace with simulation-generated waveform showing complete source transfer

---

## Integration Example

```systemverilog
source_data_path #(
    .NUM_CHANNELS(8),
    .ADDR_WIDTH(64),
    .DATA_WIDTH(512),
    .SRAM_DEPTH(512)
) u_source_path (
    .clk                    (clk),
    .rst_n                  (rst_n),

    // Scheduler interface
    .sched_rd_valid         (sched_rd_valid),
    .sched_rd_addr          (sched_rd_addr),
    .sched_rd_beats         (sched_rd_beats),
    .sched_rd_id            (sched_rd_id),
    .sched_rd_done_strobe   (sched_rd_done_strobe),
    .sched_rd_beats_done    (sched_rd_beats_done),
    .sched_rd_error         (sched_rd_error),

    // AXI read master
    .m_axi_arvalid          (src_axi_arvalid),
    .m_axi_arready          (src_axi_arready),
    .m_axi_araddr           (src_axi_araddr),
    .m_axi_arlen            (src_axi_arlen),
    .m_axi_rvalid           (src_axi_rvalid),
    .m_axi_rready           (src_axi_rready),
    .m_axi_rdata            (src_axi_rdata),
    .m_axi_rlast            (src_axi_rlast),

    // Drain interface
    .src_drain_valid        (src_drain_valid),
    .src_drain_ready        (src_drain_ready),
    .src_drain_data         (src_drain_data),
    .src_drain_last         (src_drain_last),
    .src_drain_id           (src_drain_id),
    .src_drain_data_avail   (src_data_avail)
);
```

---

**Last Updated:** 2025-01-10
