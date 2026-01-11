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

# AXI Write Engine Specification

**Module:** `axi_write_engine.sv`
**Location:** `projects/components/rapids/rtl/fub_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The AXI Write Engine reads data from SRAM and performs burst writes to system memory. It operates as a streaming pipeline and includes write response handling for completion tracking.

### Key Features

- **Streaming Pipeline:** No FSM - pure streaming architecture
- **Multi-Channel Support:** Channel ID in AXI ID field
- **Write Response Tracking:** B channel completion handling
- **Configurable Burst Length:** Up to 256 beats per burst
- **Latency Compensation:** Integrated beats_latency_bridge

### Block Diagram

### Figure 2.4.1: AXI Write Engine Block Diagram

```
                        +---------------------------+
    sched_wr_valid   -->|                           |--> m_axi_awid
    sched_wr_addr    -->|                           |--> m_axi_awaddr
    sched_wr_beats   -->|    AXI WRITE ENGINE       |--> m_axi_awlen
    sched_wr_id      -->|                           |--> m_axi_awvalid
                        |    (Streaming Pipeline)   |<-- m_axi_awready
    cfg_xfer_beats   -->|                           |
                        |                           |--> m_axi_wdata
    sched_wr_done    <--|                           |--> m_axi_wstrb
    sched_wr_beats_d <--|                           |--> m_axi_wlast
    sched_wr_error   <--|                           |--> m_axi_wvalid
                        |                           |<-- m_axi_wready
    sram_rd_en       <--|                           |
    sram_rd_addr     <--|                           |<-- m_axi_bid
    sram_rd_data     -->|                           |<-- m_axi_bresp
    sram_rd_id       <--|                           |<-- m_axi_bvalid
                        |                           |--> m_axi_bready
                        +---------------------------+
```

**Source:** [02_axi_write_engine_block.mmd](../assets/mermaid/02_axi_write_engine_block.mmd)

---

## Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;                  // Number of channels
parameter int ADDR_WIDTH = 64;                   // Address bus width
parameter int DATA_WIDTH = 512;                  // Data bus width
parameter int AXI_ID_WIDTH = 8;                  // AXI ID width
parameter int MAX_OUTSTANDING = 8;               // Max outstanding AW transactions
parameter int W_FIFO_DEPTH = 64;                 // Write data FIFO depth
parameter int B_FIFO_DEPTH = 16;                 // Write response FIFO depth
parameter int PIPELINE = 0;                      // Pipeline stages

// Derived
parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS);
```

: Table 2.4.1: AXI Write Engine Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low reset |

: Table 2.4.2: Clock and Reset

### Scheduler Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_wr_valid` | input | 1 | Write request valid |
| `sched_wr_addr` | input | AW | Destination address |
| `sched_wr_beats` | input | 32 | Total beats to write |
| `sched_wr_id` | input | CW | Channel ID |
| `sched_wr_done_strobe` | output | 1 | Burst complete strobe |
| `sched_wr_beats_done` | output | 32 | Beats completed |
| `sched_wr_error` | output | 1 | Error flag |

: Table 2.4.3: Scheduler Interface

### AXI4 Write Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_awid` | output | IW | Write address ID |
| `m_axi_awaddr` | output | AW | Write address |
| `m_axi_awlen` | output | 8 | Burst length (beats - 1) |
| `m_axi_awsize` | output | 3 | Burst size |
| `m_axi_awburst` | output | 2 | Burst type (INCR) |
| `m_axi_awvalid` | output | 1 | Address valid |
| `m_axi_awready` | input | 1 | Address ready |
| `m_axi_wdata` | output | DW | Write data |
| `m_axi_wstrb` | output | DW/8 | Write strobes |
| `m_axi_wlast` | output | 1 | Last beat |
| `m_axi_wvalid` | output | 1 | Data valid |
| `m_axi_wready` | input | 1 | Data ready |
| `m_axi_bid` | input | IW | Response ID |
| `m_axi_bresp` | input | 2 | Write response |
| `m_axi_bvalid` | input | 1 | Response valid |
| `m_axi_bready` | output | 1 | Response ready |

: Table 2.4.4: AXI4 Write Master Interface

### SRAM Read Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sram_rd_en` | output | 1 | SRAM read enable |
| `sram_rd_addr` | output | AW | SRAM read address |
| `sram_rd_data` | input | DW | SRAM read data |
| `sram_rd_id` | output | CW | Channel ID for read |

: Table 2.4.5: SRAM Read Interface

---

## Operation

### Write Transaction Phases

AXI writes have three phases that can overlap:

```
Phase 1: AW (Address)    Phase 2: W (Data)    Phase 3: B (Response)
    |                        |                      |
    +-- Issue address        +-- Stream data        +-- Receive response
        before data             from SRAM               track completion
```

### Timing Diagram

### Figure 2.4.2: AXI Write Burst Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    sched_wr_valid _/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\_____
    sched_wr_beats |=============== 4 ================|XXXXX|XXXXX
                    :       :       :       :       :       :
    m_axi_awvalid  _/‾\_____:_______:_______:_______:_______:_______
    m_axi_awlen    X| 3 |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    sram_rd_en     _/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\_______:_______:_______
                    :       :       :       :       :       :
    m_axi_wvalid   _________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\_______:_______
    m_axi_wdata    X:XXXXXXX|==D0===|==D1===|==D2===|==D3===|XXXXXXX
    m_axi_wlast    _________:_______:_______:_______/‾\_____:_______
                    :       :       :       :       :       :
    m_axi_bvalid   _________:_______:_______:_______:_______/‾\_____
    m_axi_bresp    X:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX| OK|XXX
                    :       :       :       :       :       :
    sched_wr_done  _________:_______:_______:_______:_______:_/‾\___
```

**TODO:** Replace with simulation-generated waveform

---

## Error Handling

| Error | Detection | Response |
|-------|-----------|----------|
| AXI SLVERR | `m_axi_bresp == 2'b10` | Set `sched_wr_error` |
| AXI DECERR | `m_axi_bresp == 2'b11` | Set `sched_wr_error` |

: Table 2.4.6: Error Handling

---

**Last Updated:** 2025-01-10
