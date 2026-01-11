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

# Sink Data Path Specification

**Module:** `sink_data_path.sv`
**Location:** `projects/components/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The Sink Data Path integrates the SRAM controller and AXI write engine for network-to-memory transfers. Data enters through the fill interface, is buffered in SRAM, and is written to system memory via AXI4.

### Key Features

- **8-Channel SRAM Controller:** Per-channel buffering with flow control
- **AXI Write Engine:** Streaming burst writes to system memory
- **Beat-Level Tracking:** Precise flow control at beat granularity
- **Scheduler Integration:** Receives transfer requests from scheduler

### Block Diagram

### Figure 3.3.1: Sink Data Path Block Diagram

```
                        sink_data_path
    +-------------------------------------------------------+
    |                                                       |
    |    Fill Interface (External)                          |
    |         |                                             |
    |         v                                             |
    |  +---------------------------------------------+      |
    |  |         snk_sram_controller                 |      |
    |  |  +-------+  +-------+       +-------+       |      |
    |  |  | unit  |  | unit  |  ...  | unit  |       |      |
    |  |  |  [0]  |  |  [1]  |       |  [7]  |       |      |
    |  |  +-------+  +-------+       +-------+       |      |
    |  |      |          |              |            |      |
    |  |      v          v              v            |      |
    |  |  +-------------------------------------+    |      |
    |  |  |        Channel Arbitration          |    |      |
    |  |  +------------------+------------------+    |      |
    |  +---------------------|----------------------+       |
    |                        |                              |
    |                        v                              |
    |  +---------------------------------------------+      |
    |  |            axi_write_engine                 |      |
    |  |  - Burst generation                         |      |
    |  |  - W channel streaming                      |      |
    |  |  - B channel response tracking              |      |
    |  +---------------------+-----------------------+      |
    |                        |                              |
    +------------------------|------------------------------+
                             v
                     AXI Write Master
                   (to System Memory)
```

**Source:** [03_sink_data_path_block.mmd](../assets/mermaid/03_sink_data_path_block.mmd)

---

## Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;
parameter int ADDR_WIDTH = 64;
parameter int DATA_WIDTH = 512;
parameter int AXI_ID_WIDTH = 8;
parameter int SRAM_DEPTH = 512;
parameter int AW_MAX_OUTSTANDING = 8;
parameter int W_PHASE_FIFO_DEPTH = 64;
parameter int B_PHASE_FIFO_DEPTH = 16;
```

: Table 3.3.1: Sink Data Path Parameters

---

## Data Flow

### Figure 3.3.2: Sink Path Data Flow Sequence

```
1. Fill Request
   - snk_fill_alloc_req = 1
   - snk_fill_alloc_size = N (beats to allocate)
   - snk_fill_alloc_id = channel
        |
        v
2. Space Check (beats_alloc_ctrl)
   - Check snk_fill_space_free[channel] >= N
   - Allocate N beats of space
        |
        v
3. Fill Data Transfer
   - snk_fill_valid = 1
   - snk_fill_data = data beats
   - snk_fill_id = channel
        |
        v
4. SRAM Write
   - Data written to channel's SRAM partition
   - beats_drain_ctrl notified of data availability
        |
        v
5. AXI Write Request
   - Scheduler requests write: sched_wr_valid
   - Address and beat count provided
        |
        v
6. SRAM Read + AXI Write
   - axi_write_engine reads from SRAM
   - Issues AXI bursts to memory
        |
        v
7. Completion
   - B channel response received
   - sched_wr_done_strobe = 1
```

**Source:** [03_sink_data_flow.mmd](../assets/mermaid/03_sink_data_flow.mmd)

---

## Timing Diagram

### Figure 3.3.3: Sink Path Transfer Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    fill_alloc_req _/‾\_____:_______:_______:_______:_______:_______
    fill_alloc_size| 4 |XXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    fill_valid     _________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\_______:_______:_______
    fill_data      X:XXXXXXX|==D0==|==D1==|==D2==|==D3==|XXXXXXXXX
                    :       :       :       :       :       :
    sched_wr_valid _________:_______:_______:_______/‾‾‾‾‾‾‾\_______
    sched_wr_beats X:XXXXXXX:XXXXXXX:XXXXXXX| 4 |XXXXXXXXXXX:XXXXXXX
                    :       :       :       :       :       :
    m_axi_awvalid  _________:_______:_______:_______/‾\_____:_______
    m_axi_wvalid   _________:_______:_______:_______:_/‾‾‾‾‾\_______
    m_axi_bvalid   _________:_______:_______:_______:_______:_/‾\___
                    :       :       :       :       :       :
    sched_wr_done  _________:_______:_______:_______:_______:___/‾\_
```

**TODO:** Replace with simulation-generated waveform showing complete sink transfer

---

## Interface Summary

### Fill Interface (Input)

| Signal | Direction | Description |
|--------|-----------|-------------|
| `snk_fill_alloc_req` | input | Allocation request |
| `snk_fill_alloc_size` | input | Beats to allocate |
| `snk_fill_alloc_id` | input | Channel ID |
| `snk_fill_space_free` | output | Available space per channel |
| `snk_fill_valid` | input | Data valid |
| `snk_fill_ready` | output | Ready for data |
| `snk_fill_data` | input | Fill data |
| `snk_fill_last` | input | Last beat |
| `snk_fill_id` | input | Channel ID |

: Table 3.3.2: Fill Interface

### Scheduler Interface

| Signal | Direction | Description |
|--------|-----------|-------------|
| `sched_wr_valid` | input | Write request |
| `sched_wr_addr` | input | Destination address |
| `sched_wr_beats` | input | Beats to write |
| `sched_wr_id` | input | Channel ID |
| `sched_wr_done_strobe` | output | Write complete |
| `sched_wr_beats_done` | output | Beats completed |
| `sched_wr_error` | output | Error flag |

: Table 3.3.3: Scheduler Interface

---

**Last Updated:** 2025-01-10
