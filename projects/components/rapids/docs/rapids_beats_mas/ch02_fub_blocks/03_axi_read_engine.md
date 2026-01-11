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

# AXI Read Engine Specification

**Module:** `axi_read_engine.sv`
**Location:** `projects/components/rapids/rtl/fub_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The AXI Read Engine performs burst reads from system memory and writes data to the SRAM buffer. It operates as a streaming pipeline with no FSM, maximizing throughput through continuous data flow.

### Key Features

- **Streaming Pipeline:** No FSM - pure streaming architecture
- **Multi-Channel Support:** Channel ID passed through AXI ID field
- **Configurable Burst Length:** Up to 256 beats per burst
- **Latency Compensation:** Integrated beats_latency_bridge
- **Error Handling:** AXI RRESP error detection and reporting

### Block Diagram

### Figure 2.3.1: AXI Read Engine Block Diagram

```
                        +---------------------------+
    sched_rd_valid   -->|                           |--> m_axi_arid
    sched_rd_addr    -->|                           |--> m_axi_araddr
    sched_rd_beats   -->|    AXI READ ENGINE        |--> m_axi_arlen
    sched_rd_id      -->|                           |--> m_axi_arvalid
                        |    (Streaming Pipeline)   |<-- m_axi_arready
    cfg_xfer_beats   -->|                           |
                        |                           |<-- m_axi_rid
    sched_rd_done    <--|                           |<-- m_axi_rdata
    sched_rd_beats_d <--|                           |<-- m_axi_rresp
    sched_rd_error   <--|                           |<-- m_axi_rlast
                        |                           |<-- m_axi_rvalid
    sram_wr_en       <--|                           |--> m_axi_rready
    sram_wr_addr     <--|                           |
    sram_wr_data     <--|                           |
    sram_wr_id       <--|                           |
                        +---------------------------+
```

**Source:** [02_axi_read_engine_block.mmd](../assets/mermaid/02_axi_read_engine_block.mmd)

---

## Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;                  // Number of channels
parameter int ADDR_WIDTH = 64;                   // Address bus width
parameter int DATA_WIDTH = 512;                  // Data bus width
parameter int AXI_ID_WIDTH = 8;                  // AXI ID width
parameter int MAX_OUTSTANDING = 8;               // Max outstanding AR transactions
parameter int PIPELINE = 0;                      // Pipeline stages

// Derived
parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS);
```

: Table 2.3.1: AXI Read Engine Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low reset |

: Table 2.3.2: Clock and Reset

### Scheduler Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_rd_valid` | input | 1 | Read request valid |
| `sched_rd_addr` | input | AW | Source address |
| `sched_rd_beats` | input | 32 | Total beats to read |
| `sched_rd_id` | input | CW | Channel ID |
| `sched_rd_done_strobe` | output | 1 | Burst complete strobe |
| `sched_rd_beats_done` | output | 32 | Beats completed |
| `sched_rd_error` | output | 1 | Error flag |

: Table 2.3.3: Scheduler Interface

### AXI4 Read Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_arid` | output | IW | Read address ID |
| `m_axi_araddr` | output | AW | Read address |
| `m_axi_arlen` | output | 8 | Burst length (beats - 1) |
| `m_axi_arsize` | output | 3 | Burst size |
| `m_axi_arburst` | output | 2 | Burst type (INCR) |
| `m_axi_arvalid` | output | 1 | Address valid |
| `m_axi_arready` | input | 1 | Address ready |
| `m_axi_rid` | input | IW | Read data ID |
| `m_axi_rdata` | input | DW | Read data |
| `m_axi_rresp` | input | 2 | Read response |
| `m_axi_rlast` | input | 1 | Last beat |
| `m_axi_rvalid` | input | 1 | Data valid |
| `m_axi_rready` | output | 1 | Data ready |

: Table 2.3.4: AXI4 Read Master Interface

### SRAM Write Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sram_wr_en` | output | 1 | SRAM write enable |
| `sram_wr_addr` | output | AW | SRAM write address |
| `sram_wr_data` | output | DW | SRAM write data |
| `sram_wr_id` | output | CW | Channel ID for data |

: Table 2.3.5: SRAM Write Interface

---

## Operation

### Streaming Pipeline Architecture

The AXI read engine uses a **streaming pipeline** with no FSM:

```
Scheduler Request --> AR Channel --> R Channel --> SRAM Write
      |                   |             |              |
      +--- beat count     +-- addr      +-- data       +-- wr_en
           tracking           issue         receive        generate
```

### Timing Diagram

### Figure 2.3.2: AXI Read Burst Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    sched_rd_valid _/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\_____
    sched_rd_beats |=============== 8 ================|XXXXX|XXXXX
                    :       :       :       :       :       :
    m_axi_arvalid  _/‾\_____:_______:_______:_______:_______:_______
    m_axi_arlen    X| 7 |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
    m_axi_arready  ‾‾‾‾‾\___/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
                    :       :       :       :       :       :
    m_axi_rvalid   _________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\_____
    m_axi_rdata    X:XXXXXXX|==D0===|==D1===|...|==D7===|XXXXXXX
    m_axi_rlast    _________:_______:_______:_______/‾\_____:_______
                    :       :       :       :       :       :
    sram_wr_en     _________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\_____
    sram_wr_data   X:XXXXXXX|==D0===|==D1===|...|==D7===|XXXXXXX
                    :       :       :       :       :       :
    sched_rd_done  _________:_______:_______:_______:_______/‾\___
```

**TODO:** Replace with simulation-generated waveform

---

## Burst Segmentation

Large transfers are segmented into AXI-compliant bursts:

```
Total beats = 256
cfg_xfer_beats = 64

Bursts issued:
  AR[0]: addr=0x1000, len=63 (64 beats)
  AR[1]: addr=0x2000, len=63 (64 beats)
  AR[2]: addr=0x3000, len=63 (64 beats)
  AR[3]: addr=0x4000, len=63 (64 beats)
```

---

## Error Handling

| Error | Detection | Response |
|-------|-----------|----------|
| AXI SLVERR | `m_axi_rresp == 2'b10` | Set `sched_rd_error`, continue |
| AXI DECERR | `m_axi_rresp == 2'b11` | Set `sched_rd_error`, continue |

: Table 2.3.6: Error Handling

---

**Last Updated:** 2025-01-10
