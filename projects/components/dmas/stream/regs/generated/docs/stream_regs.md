<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## stream_regs address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x126C

<p>Configuration and status registers for 8-channel STREAM DMA engine with full monitor control</p>

|Offset|     Identifier     |                 Name                 |
|------|--------------------|--------------------------------------|
|0x0000|    CH0_CTRL_LOW    |             Ch0 kick LOW             |
|0x0004|    CH0_CTRL_HIGH   |             Ch0 kick HIGH            |
|0x0008|    CH1_CTRL_LOW    |             Ch1 kick LOW             |
|0x000C|    CH1_CTRL_HIGH   |             Ch1 kick HIGH            |
|0x0010|    CH2_CTRL_LOW    |             Ch2 kick LOW             |
|0x0014|    CH2_CTRL_HIGH   |             Ch2 kick HIGH            |
|0x0018|    CH3_CTRL_LOW    |             Ch3 kick LOW             |
|0x001C|    CH3_CTRL_HIGH   |             Ch3 kick HIGH            |
|0x0020|    CH4_CTRL_LOW    |             Ch4 kick LOW             |
|0x0024|    CH4_CTRL_HIGH   |             Ch4 kick HIGH            |
|0x0028|    CH5_CTRL_LOW    |             Ch5 kick LOW             |
|0x002C|    CH5_CTRL_HIGH   |             Ch5 kick HIGH            |
|0x0030|    CH6_CTRL_LOW    |             Ch6 kick LOW             |
|0x0034|    CH6_CTRL_HIGH   |             Ch6 kick HIGH            |
|0x0038|    CH7_CTRL_LOW    |             Ch7 kick LOW             |
|0x003C|    CH7_CTRL_HIGH   |             Ch7 kick HIGH            |
|0x0100|     GLOBAL_CTRL    |        Global Control Register       |
|0x0104|    GLOBAL_STATUS   |        Global Status Register        |
|0x0108|       VERSION      |           Version Register           |
|0x0120|   CHANNEL_ENABLE   |        Channel Enable Register       |
|0x0124|    CHANNEL_RESET   |        Channel Reset Register        |
|0x0140|    CHANNEL_IDLE    |          Channel Idle Status         |
|0x0144|  DESC_ENGINE_IDLE  |     Descriptor Engine Idle Status    |
|0x0148|   SCHEDULER_IDLE   |         Scheduler Idle Status        |
|0x0150|     CH_STATE[0]    |      Per-Channel State Registers     |
|0x0154|     CH_STATE[1]    |      Per-Channel State Registers     |
|0x0158|     CH_STATE[2]    |      Per-Channel State Registers     |
|0x015C|     CH_STATE[3]    |      Per-Channel State Registers     |
|0x0160|     CH_STATE[4]    |      Per-Channel State Registers     |
|0x0164|     CH_STATE[5]    |      Per-Channel State Registers     |
|0x0168|     CH_STATE[6]    |      Per-Channel State Registers     |
|0x016C|     CH_STATE[7]    |      Per-Channel State Registers     |
|0x0170|     SCHED_ERROR    |        Scheduler Error Status        |
|0x0174|   AXI_RD_COMPLETE  |   AXI Read Engine Completion Status  |
|0x0178|   AXI_WR_COMPLETE  |  AXI Write Engine Completion Status  |
|0x0200|SCHED_TIMEOUT_CYCLES|       Scheduler Timeout Cycles       |
|0x0204|    SCHED_CONFIG    |        Scheduler Configuration       |
|0x0208| SCHED_TIMEOUT_LIMIT|  Scheduler Timeout Escalation Limit  |
|0x0220|   DESCENG_CONFIG   |    Descriptor Engine Configuration   |
|0x0224| DESCENG_ADDR0_BASE |    Descriptor Address Range 0 Base   |
|0x0228| DESCENG_ADDR0_LIMIT|   Descriptor Address Range 0 Limit   |
|0x022C| DESCENG_ADDR1_BASE |    Descriptor Address Range 1 Base   |
|0x0230| DESCENG_ADDR1_LIMIT|   Descriptor Address Range 1 Limit   |
|0x02A0|   AXI_XFER_CONFIG  |      AXI Transfer Configuration      |
|0x02B0|     PERF_CONFIG    |  Performance Profiler Configuration  |
|0x02C0|      OBS_CTRL      |        Observation Mux Control       |
|0x02C4|      OBS_FLAGS     |           Observation Flags          |
|0x02C8|      OBS_DATA0     |          Observation Data 0          |
|0x02CC|      OBS_DATA1     |          Observation Data 1          |
|0x035C|     PERF_CH_SEL    |Per-Channel Perf Bucket Readout Select|
|0x0378|      HIST_SEL      |   Latency Histogram Readout Select   |
|0x037C|      HIST_DATA     |      Latency Histogram Bin Count     |
|0x0380|     HIST_TOTAL     |    Latency Histogram Metric Total    |
|0x1000|         MON        |       STREAM Monitor Registers       |

### CH0_CTRL_LOW register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>Ch0 descriptor addr [31:0]  (write kicks)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|   w  | 0x0 |  — |

### CH0_CTRL_HIGH register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

<p>Ch0 descriptor addr [63:32] (write kicks)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|   w  | 0x0 |  — |

### CH1_CTRL_LOW register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4

<p>Ch1 descriptor addr [31:0]  (write kicks)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|   w  | 0x0 |  — |

### CH1_CTRL_HIGH register

- Absolute Address: 0xC
- Base Offset: 0xC
- Size: 0x4

<p>Ch1 descriptor addr [63:32] (write kicks)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|   w  | 0x0 |  — |

### CH2_CTRL_LOW register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>Ch2 descriptor addr [31:0]  (write kicks)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|   w  | 0x0 |  — |

### CH2_CTRL_HIGH register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

<p>Ch2 descriptor addr [63:32] (write kicks)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|   w  | 0x0 |  — |

### CH3_CTRL_LOW register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

<p>Ch3 descriptor addr [31:0]  (write kicks)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|   w  | 0x0 |  — |

### CH3_CTRL_HIGH register

- Absolute Address: 0x1C
- Base Offset: 0x1C
- Size: 0x4

<p>Ch3 descriptor addr [63:32] (write kicks)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|   w  | 0x0 |  — |

### CH4_CTRL_LOW register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

<p>Ch4 descriptor addr [31:0]  (write kicks)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|   w  | 0x0 |  — |

### CH4_CTRL_HIGH register

- Absolute Address: 0x24
- Base Offset: 0x24
- Size: 0x4

<p>Ch4 descriptor addr [63:32] (write kicks)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|   w  | 0x0 |  — |

### CH5_CTRL_LOW register

- Absolute Address: 0x28
- Base Offset: 0x28
- Size: 0x4

<p>Ch5 descriptor addr [31:0]  (write kicks)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|   w  | 0x0 |  — |

### CH5_CTRL_HIGH register

- Absolute Address: 0x2C
- Base Offset: 0x2C
- Size: 0x4

<p>Ch5 descriptor addr [63:32] (write kicks)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|   w  | 0x0 |  — |

### CH6_CTRL_LOW register

- Absolute Address: 0x30
- Base Offset: 0x30
- Size: 0x4

<p>Ch6 descriptor addr [31:0]  (write kicks)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|   w  | 0x0 |  — |

### CH6_CTRL_HIGH register

- Absolute Address: 0x34
- Base Offset: 0x34
- Size: 0x4

<p>Ch6 descriptor addr [63:32] (write kicks)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|   w  | 0x0 |  — |

### CH7_CTRL_LOW register

- Absolute Address: 0x38
- Base Offset: 0x38
- Size: 0x4

<p>Ch7 descriptor addr [31:0]  (write kicks)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|   w  | 0x0 |  — |

### CH7_CTRL_HIGH register

- Absolute Address: 0x3C
- Base Offset: 0x3C
- Size: 0x4

<p>Ch7 descriptor addr [63:32] (write kicks)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|   w  | 0x0 |  — |

### GLOBAL_CTRL register

- Absolute Address: 0x100
- Base Offset: 0x100
- Size: 0x4

<p>Master enable and global configuration</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 | GLOBAL_EN|  rw  | 0x0 |  — |
|  1 |GLOBAL_RST|  rw  | 0x0 |  — |
|31:2|   RSVD   |   r  | 0x0 |  — |

#### GLOBAL_EN field

<p>Global enable - master switch for entire STREAM engine</p>

#### GLOBAL_RST field

<p>Global reset - resets all channels and state machines</p>

#### RSVD field

<p>Reserved</p>

### GLOBAL_STATUS register

- Absolute Address: 0x104
- Base Offset: 0x104
- Size: 0x4

<p>Overall system status and error flags</p>

|Bits| Identifier|Access|Reset|Name|
|----|-----------|------|-----|----|
|  0 |SYSTEM_IDLE|   r  |  —  |  — |
|31:1|    RSVD   |   r  | 0x0 |  — |

#### SYSTEM_IDLE field

<p>System idle - all channels idle</p>

#### RSVD field

<p>Reserved</p>

### VERSION register

- Absolute Address: 0x108
- Base Offset: 0x108
- Size: 0x4

<p>STREAM version and configuration information</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 7:0 |    MINOR   |   r  | 0x5A|  — |
| 15:8|    MAJOR   |   r  | 0x0 |  — |
|23:16|NUM_CHANNELS|   r  | 0x8 |  — |
|31:24|    RSVD    |   r  | 0x0 |  — |

#### MINOR field

<p>Minor version</p>

#### MAJOR field

<p>Major version</p>

#### NUM_CHANNELS field

<p>Number of channels</p>

#### RSVD field

<p>Reserved</p>

### CHANNEL_ENABLE register

- Absolute Address: 0x120
- Base Offset: 0x120
- Size: 0x4

<p>Per-channel enable bits (one bit per channel)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|   CH_EN  |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### CH_EN field

<p>Channel enable bits [7:0] - 1=enabled, 0=disabled</p>

#### RSVD field

<p>Reserved</p>

### CHANNEL_RESET register

- Absolute Address: 0x124
- Base Offset: 0x124
- Size: 0x4

<p>Per-channel reset bits (one bit per channel, self-clearing)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  CH_RST  |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### CH_RST field

<p>Channel reset bits [7:0] - write 1 to reset channel</p>

#### RSVD field

<p>Reserved</p>

### CHANNEL_IDLE register

- Absolute Address: 0x140
- Base Offset: 0x140
- Size: 0x4

<p>Per-channel idle status (one bit per channel)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  CH_IDLE |   r  |  —  |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### CH_IDLE field

<p>Channel idle bits [7:0] - 1=idle, 0=active</p>

#### RSVD field

<p>Reserved</p>

### DESC_ENGINE_IDLE register

- Absolute Address: 0x144
- Base Offset: 0x144
- Size: 0x4

<p>Per-channel descriptor engine idle status</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0| DESC_IDLE|   r  |  —  |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### DESC_IDLE field

<p>Descriptor engine idle bits [7:0] - 1=idle, 0=active</p>

#### RSVD field

<p>Reserved</p>

### SCHEDULER_IDLE register

- Absolute Address: 0x148
- Base Offset: 0x148
- Size: 0x4

<p>Per-channel scheduler idle status</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|SCHED_IDLE|   r  |  —  |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCHED_IDLE field

<p>Scheduler idle bits [7:0] - 1=idle, 0=active</p>

#### RSVD field

<p>Reserved</p>

## CH_STATE register file

- Absolute Address: 0x150
- Base Offset: 0x150
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x150
- Base Offset: 0x0
- Size: 0x4

<p>Current FSM state of scheduler (one-hot 7-bit encoding)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 6:0|   STATE  |   r  |  —  |  — |
|31:7|   RSVD   |   r  | 0x0 |  — |

#### STATE field

<p>Scheduler state [6:0] - one-hot encoding</p>

#### RSVD field

<p>Reserved</p>

## CH_STATE register file

- Absolute Address: 0x154
- Base Offset: 0x150
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x154
- Base Offset: 0x0
- Size: 0x4

<p>Current FSM state of scheduler (one-hot 7-bit encoding)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 6:0|   STATE  |   r  |  —  |  — |
|31:7|   RSVD   |   r  | 0x0 |  — |

#### STATE field

<p>Scheduler state [6:0] - one-hot encoding</p>

#### RSVD field

<p>Reserved</p>

## CH_STATE register file

- Absolute Address: 0x158
- Base Offset: 0x150
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x158
- Base Offset: 0x0
- Size: 0x4

<p>Current FSM state of scheduler (one-hot 7-bit encoding)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 6:0|   STATE  |   r  |  —  |  — |
|31:7|   RSVD   |   r  | 0x0 |  — |

#### STATE field

<p>Scheduler state [6:0] - one-hot encoding</p>

#### RSVD field

<p>Reserved</p>

## CH_STATE register file

- Absolute Address: 0x15C
- Base Offset: 0x150
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x15C
- Base Offset: 0x0
- Size: 0x4

<p>Current FSM state of scheduler (one-hot 7-bit encoding)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 6:0|   STATE  |   r  |  —  |  — |
|31:7|   RSVD   |   r  | 0x0 |  — |

#### STATE field

<p>Scheduler state [6:0] - one-hot encoding</p>

#### RSVD field

<p>Reserved</p>

## CH_STATE register file

- Absolute Address: 0x160
- Base Offset: 0x150
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x160
- Base Offset: 0x0
- Size: 0x4

<p>Current FSM state of scheduler (one-hot 7-bit encoding)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 6:0|   STATE  |   r  |  —  |  — |
|31:7|   RSVD   |   r  | 0x0 |  — |

#### STATE field

<p>Scheduler state [6:0] - one-hot encoding</p>

#### RSVD field

<p>Reserved</p>

## CH_STATE register file

- Absolute Address: 0x164
- Base Offset: 0x150
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x164
- Base Offset: 0x0
- Size: 0x4

<p>Current FSM state of scheduler (one-hot 7-bit encoding)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 6:0|   STATE  |   r  |  —  |  — |
|31:7|   RSVD   |   r  | 0x0 |  — |

#### STATE field

<p>Scheduler state [6:0] - one-hot encoding</p>

#### RSVD field

<p>Reserved</p>

## CH_STATE register file

- Absolute Address: 0x168
- Base Offset: 0x150
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x168
- Base Offset: 0x0
- Size: 0x4

<p>Current FSM state of scheduler (one-hot 7-bit encoding)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 6:0|   STATE  |   r  |  —  |  — |
|31:7|   RSVD   |   r  | 0x0 |  — |

#### STATE field

<p>Scheduler state [6:0] - one-hot encoding</p>

#### RSVD field

<p>Reserved</p>

## CH_STATE register file

- Absolute Address: 0x16C
- Base Offset: 0x150
- Size: 0x4
- Array Dimensions: [8]
- Array Stride: 0x4
- Total Size: 0x20

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x16C
- Base Offset: 0x0
- Size: 0x4

<p>Current FSM state of scheduler (one-hot 7-bit encoding)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 6:0|   STATE  |   r  |  —  |  — |
|31:7|   RSVD   |   r  | 0x0 |  — |

#### STATE field

<p>Scheduler state [6:0] - one-hot encoding</p>

#### RSVD field

<p>Reserved</p>

### SCHED_ERROR register

- Absolute Address: 0x170
- Base Offset: 0x170
- Size: 0x4

<p>Per-channel scheduler error flags</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0| SCHED_ERR|   r  |  —  |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCHED_ERR field

<p>Scheduler error bits [7:0] - 1=error detected, 0=no error</p>

#### RSVD field

<p>Reserved</p>

### AXI_RD_COMPLETE register

- Absolute Address: 0x174
- Base Offset: 0x174
- Size: 0x4

<p>Per-channel read engine all_complete flags</p>

|Bits| Identifier|Access|Reset|Name|
|----|-----------|------|-----|----|
| 7:0|RD_COMPLETE|   r  |  —  |  — |
|31:8|    RSVD   |   r  | 0x0 |  — |

#### RD_COMPLETE field

<p>Read completion bits [7:0] - 1=all reads complete, 0=reads pending</p>

#### RSVD field

<p>Reserved</p>

### AXI_WR_COMPLETE register

- Absolute Address: 0x178
- Base Offset: 0x178
- Size: 0x4

<p>Per-channel write engine all_complete flags</p>

|Bits| Identifier|Access|Reset|Name|
|----|-----------|------|-----|----|
| 7:0|WR_COMPLETE|   r  |  —  |  — |
|31:8|    RSVD   |   r  | 0x0 |  — |

#### WR_COMPLETE field

<p>Write completion bits [7:0] - 1=all writes complete, 0=writes pending</p>

#### RSVD field

<p>Reserved</p>

### SCHED_TIMEOUT_CYCLES register

- Absolute Address: 0x200
- Base Offset: 0x200
- Size: 0x4

<p>Timeout threshold in clock cycles (global for all channels)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x3E8|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0] - number of cycles before timeout</p>

### SCHED_CONFIG register

- Absolute Address: 0x204
- Base Offset: 0x204
- Size: 0x4

<p>Scheduler feature enables (global for all channels)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|  0 |   SCHED_EN   |  rw  | 0x1 |  — |
|  1 |  TIMEOUT_EN  |  rw  | 0x1 |  — |
|  2 |    ERR_EN    |  rw  | 0x1 |  — |
|  3 |   COMPL_EN   |  rw  | 0x1 |  — |
|  4 |    PERF_EN   |  rw  | 0x0 |  — |
|  5 |RD_PREFETCH_EN|  rw  | 0x1 |  — |
|31:6|     RSVD     |   r  | 0x0 |  — |

#### SCHED_EN field

<p>Scheduler enable - master scheduler enable</p>

#### TIMEOUT_EN field

<p>Timeout enable - enable timeout detection</p>

#### ERR_EN field

<p>Error enable - enable error reporting</p>

#### COMPL_EN field

<p>Completion enable - enable completion reporting</p>

#### PERF_EN field

<p>Performance enable - enable performance monitoring</p>

#### RD_PREFETCH_EN field

<p>Read-ahead descriptor prefetch enable. When set, on a chained
legacy descriptor the scheduler read side loads the next
descriptor from the descriptor-FIFO head and keeps filling SRAM
while the write side drains the current one -- collapsing the
per-descriptor boundary bubble to zero (perfect cross-descriptor
streaming). Default enabled; clear for lockstep A/B on the same
bitstream. Ignored for EXT (row/col) descriptors.</p>

#### RSVD field

<p>Reserved</p>

### SCHED_TIMEOUT_LIMIT register

- Absolute Address: 0x208
- Base Offset: 0x208
- Size: 0x4

<p>Number of consecutive write-progress timeout windows a channel may
tolerate before the (recoverable) timeout escalates to a fatal,
sticky CH_ERROR. 0 = never escalate (pure soft timeout: report and
keep waiting). Total time to escalate = LIMIT x TIMEOUT_CYCLES.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|   LIMIT  |  rw  | 0x4 |  — |

#### LIMIT field

<p>Consecutive-timeout strike limit before fatal escalation (0 = never)</p>

### DESCENG_CONFIG register

- Absolute Address: 0x220
- Base Offset: 0x220
- Size: 0x4

<p>Descriptor engine feature enables (global for all channels)</p>

|Bits| Identifier|Access|Reset|Name|
|----|-----------|------|-----|----|
|  0 | DESCENG_EN|  rw  | 0x1 |  — |
|  1 |PREFETCH_EN|  rw  | 0x1 |  — |
| 5:2|FIFO_THRESH|  rw  | 0x8 |  — |
|31:6|    RSVD   |   r  | 0x0 |  — |

#### DESCENG_EN field

<p>Descriptor engine enable - master enable</p>

#### PREFETCH_EN field

<p>Prefetch enable - enable descriptor prefetch. Default ENABLED:
with prefetch off the descriptor engine is on-demand (fetch the
next descriptor only after the current one drains), which inserts
a per-descriptor pipeline drain/refill bubble (~40 cycles) on
chains. Prefetch buffers FIFO_THRESH descriptors ahead so the
datapath streams continuously across descriptor boundaries.</p>

#### FIFO_THRESH field

<p>FIFO threshold [5:2] - prefetch threshold (4 bits)</p>

#### RSVD field

<p>Reserved</p>

### DESCENG_ADDR0_BASE register

- Absolute Address: 0x224
- Base Offset: 0x224
- Size: 0x4

<p>Base address for descriptor address range 0 (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|ADDR0_BASE|  rw  | 0x0 |  — |

#### ADDR0_BASE field

<p>Address range 0 base [31:0]</p>

### DESCENG_ADDR0_LIMIT register

- Absolute Address: 0x228
- Base Offset: 0x228
- Size: 0x4

<p>Limit address for descriptor address range 0 (lower 32 bits)</p>

|Bits| Identifier|Access|   Reset  |Name|
|----|-----------|------|----------|----|
|31:0|ADDR0_LIMIT|  rw  |0xFFFFFFFF|  — |

#### ADDR0_LIMIT field

<p>Address range 0 limit [31:0]</p>

### DESCENG_ADDR1_BASE register

- Absolute Address: 0x22C
- Base Offset: 0x22C
- Size: 0x4

<p>Base address for descriptor address range 1 (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|ADDR1_BASE|  rw  | 0x0 |  — |

#### ADDR1_BASE field

<p>Address range 1 base [31:0]</p>

### DESCENG_ADDR1_LIMIT register

- Absolute Address: 0x230
- Base Offset: 0x230
- Size: 0x4

<p>Limit address for descriptor address range 1 (lower 32 bits)</p>

|Bits| Identifier|Access|   Reset  |Name|
|----|-----------|------|----------|----|
|31:0|ADDR1_LIMIT|  rw  |0xFFFFFFFF|  — |

#### ADDR1_LIMIT field

<p>Address range 1 limit [31:0]</p>

### AXI_XFER_CONFIG register

- Absolute Address: 0x2A0
- Base Offset: 0x2A0
- Size: 0x4

<p>AXI read and write transfer burst sizes</p>

| Bits|  Identifier |Access|Reset|Name|
|-----|-------------|------|-----|----|
| 7:0 |RD_XFER_BEATS|  rw  | 0xF |  — |
| 15:8|WR_XFER_BEATS|  rw  | 0xF |  — |
|31:16|     RSVD    |   r  | 0x0 |  — |

#### RD_XFER_BEATS field

<p>AXI read transfer beats [7:0] - ARLEN value (0-255 represents 1-256 beats)</p>

#### WR_XFER_BEATS field

<p>AXI write transfer beats [15:8] - AWLEN value (0-255 represents 1-256 beats)</p>

#### RSVD field

<p>Reserved</p>

### PERF_CONFIG register

- Absolute Address: 0x2B0
- Base Offset: 0x2B0
- Size: 0x4

<p>Performance profiler enable and mode controls</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |  PERF_EN |  rw  | 0x0 |  — |
|  1 | PERF_MODE|  rw  | 0x0 |  — |
|  2 |PERF_CLEAR|  rw  | 0x0 |  — |
|31:3|   RSVD   |   r  | 0x0 |  — |

#### PERF_EN field

<p>Performance profiler enable</p>

#### PERF_MODE field

<p>Performance profiler mode - 0=count, 1=histogram</p>

#### PERF_CLEAR field

<p>Performance profiler clear - write 1 to clear counters</p>

#### RSVD field

<p>Reserved</p>

### OBS_CTRL register

- Absolute Address: 0x2C0
- Base Offset: 0x2C0
- Size: 0x4

<p>Selects which channel and which category drive OBS_FLAGS / OBS_DATA0 / OBS_DATA1</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 2:0|  CH_SEL  |  rw  | 0x0 |  — |
| 4:3|  CAT_SEL |  rw  | 0x0 |  — |
|31:5|   RSVD   |   r  | 0x0 |  — |

#### CH_SEL field

<p>Channel select (0..NUM_CHANNELS-1)</p>

#### CAT_SEL field

<p>Category select: 0=status (data0=sched_rd_beats, data1=sched_wr_beats), 1=rd_addr (data0=lo, data1=hi), 2=wr_addr (data0=lo, data1=hi), 3=sram (data0=rd_space_free, data1=wr_data_avail)</p>

#### RSVD field

<p>Reserved</p>

### OBS_FLAGS register

- Absolute Address: 0x2C4
- Base Offset: 0x2C4
- Size: 0x4

<p>Combinational status vector for the channel selected by OBS_CTRL.CH_SEL. See stream_core.sv for the bit layout (scheduler_state, sched_rd/wr_valid, sched_wr_ready, error stickies, idle bits, cfg_channel_enable, axi_*_all_complete).</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   FLAGS  |   r  |  —  |  — |

#### FLAGS field

<p>Observation flags</p>

### OBS_DATA0 register

- Absolute Address: 0x2C8
- Base Offset: 0x2C8
- Size: 0x4

<p>Category-muxed data word 0 for the selected channel. Semantics depend on OBS_CTRL.CAT_SEL.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   DATA   |   r  |  —  |  — |

#### DATA field

<p>Observation data 0</p>

### OBS_DATA1 register

- Absolute Address: 0x2CC
- Base Offset: 0x2CC
- Size: 0x4

<p>Category-muxed data word 1 for the selected channel. Semantics depend on OBS_CTRL.CAT_SEL.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   DATA   |   r  |  —  |  — |

#### DATA field

<p>Observation data 1</p>

### PERF_CH_SEL register

- Absolute Address: 0x35C
- Base Offset: 0x35C
- Size: 0x4

<p>Selects which channel's buckets appear in RD/WRMON_PERF_CH_*</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 2:0|  CH_SEL  |  rw  | 0x0 |  — |
|31:3|   RSVD   |   r  | 0x0 |  — |

#### CH_SEL field

<p>Channel select (0..NUM_CHANNELS-1)</p>

#### RSVD field

<p>Reserved</p>

### HIST_SEL register

- Absolute Address: 0x378
- Base Offset: 0x378
- Size: 0x4

<p>Selects bus/metric/bin presented in HIST_DATA / HIST_TOTAL</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |    BUS   |  rw  | 0x0 |  — |
|  1 |  METRIC  |  rw  | 0x0 |  — |
| 5:2|    BIN   |  rw  | 0x0 |  — |
|31:6|   RSVD   |   r  | 0x0 |  — |

#### BUS field

<p>Bus: 0=data-read R bus, 1=data-write W bus</p>

#### METRIC field

<p>Metric: 0=AR-&gt;firstR (rd) / AW-&gt;B (wr), 1=AR-&gt;RLAST (rd only)</p>

#### BIN field

<p>Latency bin index (0..15, log2)</p>

#### RSVD field

<p>Reserved</p>

### HIST_DATA register

- Absolute Address: 0x37C
- Base Offset: 0x37C
- Size: 0x4

<p>Transaction count in the HIST_SEL-selected bus/metric/bin</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Selected histogram bin count [31:0]</p>

### HIST_TOTAL register

- Absolute Address: 0x380
- Base Offset: 0x380
- Size: 0x4

<p>Total transactions for the HIST_SEL-selected bus/metric (= sum
over all bins). Equals the burst/transaction count, an
acceptance cross-check against the perf-window burst counters.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Selected metric total transaction count [31:0]</p>

## MON register file

- Absolute Address: 0x1000
- Base Offset: 0x1000
- Size: 0x26C

<p>AXI monitor + perf registers (relocatable block, instantiated at 0x1000)</p>

|Offset|        Identifier       |                       Name                       |
|------|-------------------------|--------------------------------------------------|
| 0x000|     MON_FIFO_STATUS     |                Monitor FIFO Status               |
| 0x004|      MON_FIFO_COUNT     |                Monitor FIFO Count                |
| 0x0C0|      DAXMON_ENABLE      |           Descriptor AXI Monitor Enable          |
| 0x0C4|      DAXMON_TIMEOUT     |          Descriptor AXI Monitor Timeout          |
| 0x0C8|  DAXMON_LATENCY_THRESH  |     Descriptor AXI Monitor Latency Threshold     |
| 0x0CC|     DAXMON_PKT_MASK     |        Descriptor AXI Monitor Packet Mask        |
| 0x0D0|      DAXMON_ERR_CFG     |   Descriptor AXI Monitor Error Select and Mask   |
| 0x0D4|       DAXMON_MASK1      |          Descriptor AXI Monitor Masks 1          |
| 0x0D8|       DAXMON_MASK2      |          Descriptor AXI Monitor Masks 2          |
| 0x0DC|       DAXMON_MASK3      |          Descriptor AXI Monitor Masks 3          |
| 0x0E0|       RDMON_ENABLE      |          Read Engine AXI Monitor Enable          |
| 0x0E4|      RDMON_TIMEOUT      |          Read Engine AXI Monitor Timeout         |
| 0x0E8|   RDMON_LATENCY_THRESH  |     Read Engine AXI Monitor Latency Threshold    |
| 0x0EC|      RDMON_PKT_MASK     |        Read Engine AXI Monitor Packet Mask       |
| 0x0F0|      RDMON_ERR_CFG      |   Read Engine AXI Monitor Error Select and Mask  |
| 0x0F4|       RDMON_MASK1       |          Read Engine AXI Monitor Masks 1         |
| 0x0F8|       RDMON_MASK2       |          Read Engine AXI Monitor Masks 2         |
| 0x0FC|       RDMON_MASK3       |          Read Engine AXI Monitor Masks 3         |
| 0x100|       WRMON_ENABLE      |          Write Engine AXI Monitor Enable         |
| 0x104|      WRMON_TIMEOUT      |         Write Engine AXI Monitor Timeout         |
| 0x108|   WRMON_LATENCY_THRESH  |    Write Engine AXI Monitor Latency Threshold    |
| 0x10C|      WRMON_PKT_MASK     |       Write Engine AXI Monitor Packet Mask       |
| 0x110|      WRMON_ERR_CFG      |  Write Engine AXI Monitor Error Select and Mask  |
| 0x114|       WRMON_MASK1       |         Write Engine AXI Monitor Masks 1         |
| 0x118|       WRMON_MASK2       |         Write Engine AXI Monitor Masks 2         |
| 0x11C|       WRMON_MASK3       |         Write Engine AXI Monitor Masks 3         |
| 0x150|     DAXMON_PERF_CTRL    |    Descriptor AXI Monitor Perf Window Control    |
| 0x154|    DAXMON_PERF_STATUS   |     Descriptor AXI Monitor Perf Window Status    |
| 0x158|DAXMON_PERF_WINDOW_CYCLES|     Descriptor AXI Monitor Perf Window Cycles    |
| 0x15C| DAXMON_PERF_PROD_CYCLES |   Descriptor AXI Monitor Perf Productive Cycles  |
| 0x160|  DAXMON_PERF_BP_CYCLES  |  Descriptor AXI Monitor Perf Backpressure Cycles |
| 0x164| DAXMON_PERF_STARV_CYCLES|   Descriptor AXI Monitor Perf Starvation Cycles  |
| 0x168| DAXMON_PERF_IDLE_CYCLES |      Descriptor AXI Monitor Perf Idle Cycles     |
| 0x16C|  DAXMON_PERF_BEAT_COUNT |      Descriptor AXI Monitor Perf Beat Count      |
| 0x170|DAXMON_PERF_BYTE_COUNT_LO|    Descriptor AXI Monitor Perf Byte Count Low    |
| 0x174|DAXMON_PERF_BYTE_COUNT_HI|    Descriptor AXI Monitor Perf Byte Count High   |
| 0x178| DAXMON_PERF_BURST_COUNT |      Descriptor AXI Monitor Perf Burst Count     |
| 0x180|     RDMON_PERF_CTRL     |     Read Datapath Monitor Perf Window Control    |
| 0x184|    RDMON_PERF_STATUS    |     Read Datapath Monitor Perf Window Status     |
| 0x188| RDMON_PERF_WINDOW_CYCLES|     Read Datapath Monitor Perf Window Cycles     |
| 0x18C|  RDMON_PERF_PROD_CYCLES |   Read Datapath Monitor Perf Productive Cycles   |
| 0x190|   RDMON_PERF_BP_CYCLES  |  Read Datapath Monitor Perf Backpressure Cycles  |
| 0x194| RDMON_PERF_STARV_CYCLES |   Read Datapath Monitor Perf Starvation Cycles   |
| 0x198|  RDMON_PERF_IDLE_CYCLES |      Read Datapath Monitor Perf Idle Cycles      |
| 0x19C|  RDMON_PERF_BEAT_COUNT  |       Read Datapath Monitor Perf Beat Count      |
| 0x1A0| RDMON_PERF_BYTE_COUNT_LO|     Read Datapath Monitor Perf Byte Count Low    |
| 0x1A4| RDMON_PERF_BYTE_COUNT_HI|    Read Datapath Monitor Perf Byte Count High    |
| 0x1A8|  RDMON_PERF_BURST_COUNT |      Read Datapath Monitor Perf Burst Count      |
| 0x1B0|     WRMON_PERF_CTRL     |    Write Datapath Monitor Perf Window Control    |
| 0x1B4|    WRMON_PERF_STATUS    |     Write Datapath Monitor Perf Window Status    |
| 0x1B8| WRMON_PERF_WINDOW_CYCLES|     Write Datapath Monitor Perf Window Cycles    |
| 0x1BC|  WRMON_PERF_PROD_CYCLES |   Write Datapath Monitor Perf Productive Cycles  |
| 0x1C0|   WRMON_PERF_BP_CYCLES  |  Write Datapath Monitor Perf Backpressure Cycles |
| 0x1C4| WRMON_PERF_STARV_CYCLES |   Write Datapath Monitor Perf Starvation Cycles  |
| 0x1C8|  WRMON_PERF_IDLE_CYCLES |      Write Datapath Monitor Perf Idle Cycles     |
| 0x1CC|  WRMON_PERF_BEAT_COUNT  |      Write Datapath Monitor Perf Beat Count      |
| 0x1D0| WRMON_PERF_BYTE_COUNT_LO|    Write Datapath Monitor Perf Byte Count Low    |
| 0x1D4| WRMON_PERF_BYTE_COUNT_HI|    Write Datapath Monitor Perf Byte Count High   |
| 0x1D8|  WRMON_PERF_BURST_COUNT |      Write Datapath Monitor Perf Burst Count     |
| 0x1E0|  RDMON_PERF_CH_PROD_BP  | Read Datapath Per-Channel Productive/Backpressure|
| 0x1E4| RDMON_PERF_CH_STARV_IDLE|     Read Datapath Per-Channel Starvation/Idle    |
| 0x1E8|  WRMON_PERF_CH_PROD_BP  |Write Datapath Per-Channel Productive/Backpressure|
| 0x1EC| WRMON_PERF_CH_STARV_IDLE|    Write Datapath Per-Channel Starvation/Idle    |
| 0x1F0|  RDMON_PERF_CH_OVERFLOW |    Read Datapath Per-Channel Overflow Stickies   |
| 0x1F4|  WRMON_PERF_CH_OVERFLOW |   Write Datapath Per-Channel Overflow Stickies   |
| 0x200|  RDMON_ADDR_RANGE0_LOW  |                RD addr range0 low                |
| 0x204|  RDMON_ADDR_RANGE0_HIGH |                RD addr range0 high               |
| 0x208|  RDMON_ADDR_RANGE1_LOW  |                RD addr range1 low                |
| 0x20C|  RDMON_ADDR_RANGE1_HIGH |                RD addr range1 high               |
| 0x210|  RDMON_ADDR_RANGE2_LOW  |                RD addr range2 low                |
| 0x214|  RDMON_ADDR_RANGE2_HIGH |                RD addr range2 high               |
| 0x218|  RDMON_ADDR_RANGE3_LOW  |                RD addr range3 low                |
| 0x21C|  RDMON_ADDR_RANGE3_HIGH |                RD addr range3 high               |
| 0x220|  RDMON_ADDR_RANGE_CTRL  |               RD addr range control              |
| 0x230|  WRMON_ADDR_RANGE0_LOW  |                WR addr range0 low                |
| 0x234|  WRMON_ADDR_RANGE0_HIGH |                WR addr range0 high               |
| 0x238|  WRMON_ADDR_RANGE1_LOW  |                WR addr range1 low                |
| 0x23C|  WRMON_ADDR_RANGE1_HIGH |                WR addr range1 high               |
| 0x240|  WRMON_ADDR_RANGE2_LOW  |                WR addr range2 low                |
| 0x244|  WRMON_ADDR_RANGE2_HIGH |                WR addr range2 high               |
| 0x248|  WRMON_ADDR_RANGE3_LOW  |                WR addr range3 low                |
| 0x24C|  WRMON_ADDR_RANGE3_HIGH |                WR addr range3 high               |
| 0x250|  WRMON_ADDR_RANGE_CTRL  |               WR addr range control              |
| 0x260|   MON_GROUP_BASE_ADDR   |              Monbus group base addr              |
| 0x264|   MON_GROUP_LIMIT_ADDR  |              Monbus group limit addr             |
| 0x268|MON_GROUP_FLUSH_WATERMARK|             Monbus group flush wmark             |

### MON_FIFO_STATUS register

- Absolute Address: 0x1000
- Base Offset: 0x0
- Size: 0x4

<p>Monitor bus FIFO status indicators</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|  0 | MON_FIFO_FULL|   r  |  —  |  — |
|  1 |MON_FIFO_EMPTY|   r  |  —  |  — |
|  2 | MON_FIFO_OVFL|   r  |  —  |  — |
|  3 | MON_FIFO_UNFL|   r  |  —  |  — |
|31:4|     RSVD     |   r  | 0x0 |  — |

#### MON_FIFO_FULL field

<p>Monitor FIFO full - 1=FIFO full, 0=space available</p>

#### MON_FIFO_EMPTY field

<p>Monitor FIFO empty - 1=FIFO empty, 0=data available</p>

#### MON_FIFO_OVFL field

<p>Monitor FIFO overflow - 1=overflow detected, 0=normal</p>

#### MON_FIFO_UNFL field

<p>Monitor FIFO underflow - 1=underflow detected, 0=normal</p>

#### RSVD field

<p>Reserved</p>

### MON_FIFO_COUNT register

- Absolute Address: 0x1004
- Base Offset: 0x4
- Size: 0x4

<p>Monitor bus FIFO entry count</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|FIFO_COUNT|   r  |  —  |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### FIFO_COUNT field

<p>FIFO count [15:0] - number of entries in FIFO</p>

#### RSVD field

<p>Reserved</p>

### DAXMON_ENABLE register

- Absolute Address: 0x10C0
- Base Offset: 0xC0
- Size: 0x4

<p>Descriptor AXI master monitor enable controls</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |  MON_EN  |  rw  | 0x0 |  — |
|  1 |  ERR_EN  |  rw  | 0x0 |  — |
|  2 | COMPL_EN |  rw  | 0x0 |  — |
|  3 |TIMEOUT_EN|  rw  | 0x0 |  — |
|  4 |  PERF_EN |  rw  | 0x0 |  — |
|  5 |   RSVD5  |   r  | 0x0 |  — |
|  6 | THRESH_EN|  rw  | 0x0 |  — |
|31:7|   RSVD   |   r  | 0x0 |  — |

#### MON_EN field

<p>Monitor enable - master enable for descriptor monitor</p>

#### ERR_EN field

<p>Error enable - enable error detection</p>

#### COMPL_EN field

<p>Completion enable - enable completion packets</p>

#### TIMEOUT_EN field

<p>Timeout enable - enable timeout detection</p>

#### PERF_EN field

<p>Performance enable - enable performance packets</p>

#### RSVD5 field

<p>Reserved. Bit 5 is COMPRESS_EN on WRMON_ENABLE only; held reserved here so all three monitor ENABLE registers share one bit layout.</p>

#### THRESH_EN field

<p>Threshold enable - enable latency-threshold packets. Before this field existed the threshold cone was gated by PERF_EN, so a host that left PERF_EN clear saw no threshold packets however low it set LATENCY_THRESH.</p>

#### RSVD field

<p>Reserved</p>

### DAXMON_TIMEOUT register

- Absolute Address: 0x10C4
- Base Offset: 0xC4
- Size: 0x4

<p>Descriptor AXI monitor timeout threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x2710|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0]</p>

### DAXMON_LATENCY_THRESH register

- Absolute Address: 0x10C8
- Base Offset: 0xC8
- Size: 0x4

<p>Descriptor AXI monitor latency threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|LATENCY_THRESH|  rw  |0x1388|  — |

#### LATENCY_THRESH field

<p>Latency threshold cycles [31:0]</p>

### DAXMON_PKT_MASK register

- Absolute Address: 0x10CC
- Base Offset: 0xCC
- Size: 0x4

<p>Descriptor AXI monitor packet type filtering (16-bit mask)</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0| PKT_MASK |  rw  |0xFFFF|  — |
|31:16|   RSVD   |   r  |  0x0 |  — |

#### PKT_MASK field

<p>Packet type mask [15:0] - 1=enable, 0=disable</p>

#### RSVD field

<p>Reserved</p>

### DAXMON_ERR_CFG register

- Absolute Address: 0x10D0
- Base Offset: 0xD0
- Size: 0x4

<p>Descriptor AXI monitor error selection and filtering</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0|ERR_SELECT|  rw  |  0x0 |  — |
|31:16| ERR_MASK |  rw  |0xFFFF|  — |

#### ERR_SELECT field

<p>Error select - per-packet-type route: 1=err FIFO/IRQ, 0=bulk trace</p>

#### ERR_MASK field

<p>Error mask - per-event-code drop mask, indexed by event_code[3:0]</p>

### DAXMON_MASK1 register

- Absolute Address: 0x10D4
- Base Offset: 0xD4
- Size: 0x4

<p>Descriptor AXI monitor timeout and completion masks</p>

| Bits| Identifier |Access| Reset|Name|
|-----|------------|------|------|----|
| 15:0|TIMEOUT_MASK|  rw  |0xFFFF|  — |
|31:16| COMPL_MASK |  rw  |  0x0 |  — |

#### TIMEOUT_MASK field

<p>Timeout mask</p>

#### COMPL_MASK field

<p>Completion mask</p>

### DAXMON_MASK2 register

- Absolute Address: 0x10D8
- Base Offset: 0xD8
- Size: 0x4

<p>Descriptor AXI monitor threshold and performance masks</p>

| Bits| Identifier|Access| Reset|Name|
|-----|-----------|------|------|----|
| 15:0|THRESH_MASK|  rw  |0xFFFF|  — |
|31:16| PERF_MASK |  rw  |  0x0 |  — |

#### THRESH_MASK field

<p>Threshold mask</p>

#### PERF_MASK field

<p>Performance mask</p>

### DAXMON_MASK3 register

- Absolute Address: 0x10DC
- Base Offset: 0xDC
- Size: 0x4

<p>Descriptor AXI monitor address and debug masks</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0| ADDR_MASK|  rw  |0xFFFF|  — |
|31:16|DEBUG_MASK|  rw  |  0x0 |  — |

#### ADDR_MASK field

<p>Address mask</p>

#### DEBUG_MASK field

<p>Debug mask</p>

### RDMON_ENABLE register

- Absolute Address: 0x10E0
- Base Offset: 0xE0
- Size: 0x4

<p>Read engine AXI master monitor enable controls</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |  MON_EN  |  rw  | 0x0 |  — |
|  1 |  ERR_EN  |  rw  | 0x0 |  — |
|  2 | COMPL_EN |  rw  | 0x0 |  — |
|  3 |TIMEOUT_EN|  rw  | 0x0 |  — |
|  4 |  PERF_EN |  rw  | 0x0 |  — |
|  5 |   RSVD5  |   r  | 0x0 |  — |
|  6 | THRESH_EN|  rw  | 0x0 |  — |
|31:7|   RSVD   |   r  | 0x0 |  — |

#### MON_EN field

<p>Monitor enable - master enable for read monitor</p>

#### ERR_EN field

<p>Error enable - enable error detection</p>

#### COMPL_EN field

<p>Completion enable - enable completion packets</p>

#### TIMEOUT_EN field

<p>Timeout enable - enable timeout detection</p>

#### PERF_EN field

<p>Performance enable - enable performance packets</p>

#### RSVD5 field

<p>Reserved. Bit 5 is COMPRESS_EN on WRMON_ENABLE only; held reserved here so all three monitor ENABLE registers share one bit layout.</p>

#### THRESH_EN field

<p>Threshold enable - enable latency-threshold packets. Before this field existed the threshold cone was gated by PERF_EN, so a host that left PERF_EN clear saw no threshold packets however low it set LATENCY_THRESH.</p>

#### RSVD field

<p>Reserved</p>

### RDMON_TIMEOUT register

- Absolute Address: 0x10E4
- Base Offset: 0xE4
- Size: 0x4

<p>Read engine AXI monitor timeout threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x2710|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0]</p>

### RDMON_LATENCY_THRESH register

- Absolute Address: 0x10E8
- Base Offset: 0xE8
- Size: 0x4

<p>Read engine AXI monitor latency threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|LATENCY_THRESH|  rw  |0x1388|  — |

#### LATENCY_THRESH field

<p>Latency threshold cycles [31:0]</p>

### RDMON_PKT_MASK register

- Absolute Address: 0x10EC
- Base Offset: 0xEC
- Size: 0x4

<p>Read engine AXI monitor packet type filtering (16-bit mask)</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0| PKT_MASK |  rw  |0xFFFF|  — |
|31:16|   RSVD   |   r  |  0x0 |  — |

#### PKT_MASK field

<p>Packet type mask [15:0] - 1=enable, 0=disable</p>

#### RSVD field

<p>Reserved</p>

### RDMON_ERR_CFG register

- Absolute Address: 0x10F0
- Base Offset: 0xF0
- Size: 0x4

<p>Read engine AXI monitor error selection and filtering</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0|ERR_SELECT|  rw  |  0x0 |  — |
|31:16| ERR_MASK |  rw  |0xFFFF|  — |

#### ERR_SELECT field

<p>Error select - per-packet-type route: 1=err FIFO/IRQ, 0=bulk trace</p>

#### ERR_MASK field

<p>Error mask - per-event-code drop mask, indexed by event_code[3:0]</p>

### RDMON_MASK1 register

- Absolute Address: 0x10F4
- Base Offset: 0xF4
- Size: 0x4

<p>Read engine AXI monitor timeout and completion masks</p>

| Bits| Identifier |Access| Reset|Name|
|-----|------------|------|------|----|
| 15:0|TIMEOUT_MASK|  rw  |0xFFFF|  — |
|31:16| COMPL_MASK |  rw  |  0x0 |  — |

#### TIMEOUT_MASK field

<p>Timeout mask</p>

#### COMPL_MASK field

<p>Completion mask</p>

### RDMON_MASK2 register

- Absolute Address: 0x10F8
- Base Offset: 0xF8
- Size: 0x4

<p>Read engine AXI monitor threshold and performance masks</p>

| Bits| Identifier|Access| Reset|Name|
|-----|-----------|------|------|----|
| 15:0|THRESH_MASK|  rw  |0xFFFF|  — |
|31:16| PERF_MASK |  rw  |  0x0 |  — |

#### THRESH_MASK field

<p>Threshold mask</p>

#### PERF_MASK field

<p>Performance mask</p>

### RDMON_MASK3 register

- Absolute Address: 0x10FC
- Base Offset: 0xFC
- Size: 0x4

<p>Read engine AXI monitor address and debug masks</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0| ADDR_MASK|  rw  |0xFFFF|  — |
|31:16|DEBUG_MASK|  rw  |  0x0 |  — |

#### ADDR_MASK field

<p>Address mask</p>

#### DEBUG_MASK field

<p>Debug mask</p>

### WRMON_ENABLE register

- Absolute Address: 0x1100
- Base Offset: 0x100
- Size: 0x4

<p>Write engine AXI master monitor enable controls</p>

|Bits| Identifier|Access|Reset|Name|
|----|-----------|------|-----|----|
|  0 |   MON_EN  |  rw  | 0x0 |  — |
|  1 |   ERR_EN  |  rw  | 0x0 |  — |
|  2 |  COMPL_EN |  rw  | 0x0 |  — |
|  3 | TIMEOUT_EN|  rw  | 0x0 |  — |
|  4 |  PERF_EN  |  rw  | 0x0 |  — |
|  5 |COMPRESS_EN|  rw  | 0x1 |  — |
|  6 | THRESH_EN |  rw  | 0x0 |  — |
|31:7|    RSVD   |   r  | 0x0 |  — |

#### MON_EN field

<p>Monitor enable - master enable for write monitor</p>

#### ERR_EN field

<p>Error enable - enable error detection</p>

#### COMPL_EN field

<p>Completion enable - enable completion packets</p>

#### TIMEOUT_EN field

<p>Timeout enable - enable timeout detection</p>

#### PERF_EN field

<p>Performance enable - enable performance packets</p>

#### COMPRESS_EN field

<p>Compression enable - 1=compress the monbus write stream, 0=raw 3-beat records. Only effective when the monbus group is built with USE_COMPRESSION=1. Program once before monitoring starts (must be stable while the write path is active).</p>

#### THRESH_EN field

<p>Threshold enable - enable latency-threshold packets. Before this field existed the threshold cone was gated by PERF_EN, so a host that left PERF_EN clear saw no threshold packets however low it set LATENCY_THRESH.</p>

#### RSVD field

<p>Reserved</p>

### WRMON_TIMEOUT register

- Absolute Address: 0x1104
- Base Offset: 0x104
- Size: 0x4

<p>Write engine AXI monitor timeout threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x2710|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0]</p>

### WRMON_LATENCY_THRESH register

- Absolute Address: 0x1108
- Base Offset: 0x108
- Size: 0x4

<p>Write engine AXI monitor latency threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|LATENCY_THRESH|  rw  |0x1388|  — |

#### LATENCY_THRESH field

<p>Latency threshold cycles [31:0]</p>

### WRMON_PKT_MASK register

- Absolute Address: 0x110C
- Base Offset: 0x10C
- Size: 0x4

<p>Write engine AXI monitor packet type filtering (16-bit mask)</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0| PKT_MASK |  rw  |0xFFFF|  — |
|31:16|   RSVD   |   r  |  0x0 |  — |

#### PKT_MASK field

<p>Packet type mask [15:0] - 1=enable, 0=disable</p>

#### RSVD field

<p>Reserved</p>

### WRMON_ERR_CFG register

- Absolute Address: 0x1110
- Base Offset: 0x110
- Size: 0x4

<p>Write engine AXI monitor error selection and filtering</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0|ERR_SELECT|  rw  |  0x0 |  — |
|31:16| ERR_MASK |  rw  |0xFFFF|  — |

#### ERR_SELECT field

<p>Error select - per-packet-type route: 1=err FIFO/IRQ, 0=bulk trace</p>

#### ERR_MASK field

<p>Error mask - per-event-code drop mask, indexed by event_code[3:0]</p>

### WRMON_MASK1 register

- Absolute Address: 0x1114
- Base Offset: 0x114
- Size: 0x4

<p>Write engine AXI monitor timeout and completion masks</p>

| Bits| Identifier |Access| Reset|Name|
|-----|------------|------|------|----|
| 15:0|TIMEOUT_MASK|  rw  |0xFFFF|  — |
|31:16| COMPL_MASK |  rw  |  0x0 |  — |

#### TIMEOUT_MASK field

<p>Timeout mask</p>

#### COMPL_MASK field

<p>Completion mask</p>

### WRMON_MASK2 register

- Absolute Address: 0x1118
- Base Offset: 0x118
- Size: 0x4

<p>Write engine AXI monitor threshold and performance masks</p>

| Bits| Identifier|Access| Reset|Name|
|-----|-----------|------|------|----|
| 15:0|THRESH_MASK|  rw  |0xFFFF|  — |
|31:16| PERF_MASK |  rw  |  0x0 |  — |

#### THRESH_MASK field

<p>Threshold mask</p>

#### PERF_MASK field

<p>Performance mask</p>

### WRMON_MASK3 register

- Absolute Address: 0x111C
- Base Offset: 0x11C
- Size: 0x4

<p>Write engine AXI monitor address and debug masks</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0| ADDR_MASK|  rw  |0xFFFF|  — |
|31:16|DEBUG_MASK|  rw  |  0x0 |  — |

#### ADDR_MASK field

<p>Address mask</p>

#### DEBUG_MASK field

<p>Debug mask</p>

### DAXMON_PERF_CTRL register

- Absolute Address: 0x1150
- Base Offset: 0x150
- Size: 0x4

<p>Perf-window run control for the descriptor AXI monitor</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |    RUN   |  rw  | 0x0 |  — |
|31:1|   RSVD   |   r  | 0x0 |  — |

#### RUN field

<p>Perf window run - 1=open window and accumulate cycle buckets, 0=close window and freeze counters. Rising edge clears all counters.</p>

#### RSVD field

<p>Reserved</p>

### DAXMON_PERF_STATUS register

- Absolute Address: 0x1154
- Base Offset: 0x154
- Size: 0x4

<p>Perf-window live status</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |WIN_ACTIVE|   r  |  —  |  — |
|31:1|   RSVD   |   r  | 0x0 |  — |

#### WIN_ACTIVE field

<p>Window active - 1=window open and accumulating</p>

#### RSVD field

<p>Reserved</p>

### DAXMON_PERF_WINDOW_CYCLES register

- Absolute Address: 0x1158
- Base Offset: 0x158
- Size: 0x4

<p>LIVE free-running window-cycle counter. Valid only while
DAXMON_PERF_STATUS.WIN_ACTIVE=1; the monitor ZEROES this when the
window closes (RUN-&gt;0). For a closed window, use the sum of the
four bucket registers (PROD+BP+STARV+IDLE), which HOLD their
values after close.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Window cycles [31:0] (live-only; reads 0 after close)</p>

### DAXMON_PERF_PROD_CYCLES register

- Absolute Address: 0x115C
- Base Offset: 0x15C
- Size: 0x4

<p>Cycles with R data valid &amp;&amp; ready (data delivered)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Productive cycles [31:0]</p>

### DAXMON_PERF_BP_CYCLES register

- Absolute Address: 0x1160
- Base Offset: 0x160
- Size: 0x4

<p>Cycles with R data valid &amp;&amp; !ready (back-pressure)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Backpressure cycles [31:0]</p>

### DAXMON_PERF_STARV_CYCLES register

- Absolute Address: 0x1164
- Base Offset: 0x164
- Size: 0x4

<p>Cycles with !R data valid &amp;&amp; ready (starvation)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Starvation cycles [31:0]</p>

### DAXMON_PERF_IDLE_CYCLES register

- Absolute Address: 0x1168
- Base Offset: 0x168
- Size: 0x4

<p>Cycles with !R data valid &amp;&amp; !ready (idle)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Idle cycles [31:0]</p>

### DAXMON_PERF_BEAT_COUNT register

- Absolute Address: 0x116C
- Base Offset: 0x16C
- Size: 0x4

<p>R beats transferred in window (= productive cycles)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Beat count [31:0]</p>

### DAXMON_PERF_BYTE_COUNT_LO register

- Absolute Address: 0x1170
- Base Offset: 0x170
- Size: 0x4

<p>Bytes transferred in window (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [31:0]</p>

### DAXMON_PERF_BYTE_COUNT_HI register

- Absolute Address: 0x1174
- Base Offset: 0x174
- Size: 0x4

<p>Bytes transferred in window (upper 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [63:32]</p>

### DAXMON_PERF_BURST_COUNT register

- Absolute Address: 0x1178
- Base Offset: 0x178
- Size: 0x4

<p>AR handshakes (bursts issued) in window</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Burst count [31:0]</p>

### RDMON_PERF_CTRL register

- Absolute Address: 0x1180
- Base Offset: 0x180
- Size: 0x4

<p>Perf-window run control for the data-read datapath monitor</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |    RUN   |  rw  | 0x0 |  — |
|31:1|   RSVD   |   r  | 0x0 |  — |

#### RUN field

<p>Perf window run - 1=open window and accumulate cycle buckets, 0=close window and freeze counters. Rising edge clears all counters.</p>

#### RSVD field

<p>Reserved</p>

### RDMON_PERF_STATUS register

- Absolute Address: 0x1184
- Base Offset: 0x184
- Size: 0x4

<p>Perf-window live status</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |WIN_ACTIVE|   r  |  —  |  — |
|31:1|   RSVD   |   r  | 0x0 |  — |

#### WIN_ACTIVE field

<p>Window active - 1=window open and accumulating</p>

#### RSVD field

<p>Reserved</p>

### RDMON_PERF_WINDOW_CYCLES register

- Absolute Address: 0x1188
- Base Offset: 0x188
- Size: 0x4

<p>LIVE free-running window-cycle counter. Valid only while
RDMON_PERF_STATUS.WIN_ACTIVE=1; the monitor ZEROES this when the
window closes (RUN-&gt;0). For a closed window, use the sum of the
four bucket registers (PROD+BP+STARV+IDLE), which HOLD their
values after close.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Window cycles [31:0] (live-only; reads 0 after close)</p>

### RDMON_PERF_PROD_CYCLES register

- Absolute Address: 0x118C
- Base Offset: 0x18C
- Size: 0x4

<p>Cycles with R data valid &amp;&amp; ready (data delivered)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Productive cycles [31:0]</p>

### RDMON_PERF_BP_CYCLES register

- Absolute Address: 0x1190
- Base Offset: 0x190
- Size: 0x4

<p>Cycles with R data valid &amp;&amp; !ready (back-pressure)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Backpressure cycles [31:0]</p>

### RDMON_PERF_STARV_CYCLES register

- Absolute Address: 0x1194
- Base Offset: 0x194
- Size: 0x4

<p>Cycles with !R data valid &amp;&amp; ready (starvation)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Starvation cycles [31:0]</p>

### RDMON_PERF_IDLE_CYCLES register

- Absolute Address: 0x1198
- Base Offset: 0x198
- Size: 0x4

<p>Cycles with !R data valid &amp;&amp; !ready (idle)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Idle cycles [31:0]</p>

### RDMON_PERF_BEAT_COUNT register

- Absolute Address: 0x119C
- Base Offset: 0x19C
- Size: 0x4

<p>R beats transferred in window (= productive cycles)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Beat count [31:0]</p>

### RDMON_PERF_BYTE_COUNT_LO register

- Absolute Address: 0x11A0
- Base Offset: 0x1A0
- Size: 0x4

<p>Bytes transferred in window (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [31:0]</p>

### RDMON_PERF_BYTE_COUNT_HI register

- Absolute Address: 0x11A4
- Base Offset: 0x1A4
- Size: 0x4

<p>Bytes transferred in window (upper 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [63:32]</p>

### RDMON_PERF_BURST_COUNT register

- Absolute Address: 0x11A8
- Base Offset: 0x1A8
- Size: 0x4

<p>AR handshakes (bursts issued) in window</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Burst count [31:0]</p>

### WRMON_PERF_CTRL register

- Absolute Address: 0x11B0
- Base Offset: 0x1B0
- Size: 0x4

<p>Perf-window run control for the data-write datapath monitor</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |    RUN   |  rw  | 0x0 |  — |
|31:1|   RSVD   |   r  | 0x0 |  — |

#### RUN field

<p>Perf window run - 1=open window and accumulate cycle buckets, 0=close window and freeze counters. Rising edge clears all counters.</p>

#### RSVD field

<p>Reserved</p>

### WRMON_PERF_STATUS register

- Absolute Address: 0x11B4
- Base Offset: 0x1B4
- Size: 0x4

<p>Perf-window live status</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |WIN_ACTIVE|   r  |  —  |  — |
|31:1|   RSVD   |   r  | 0x0 |  — |

#### WIN_ACTIVE field

<p>Window active - 1=window open and accumulating</p>

#### RSVD field

<p>Reserved</p>

### WRMON_PERF_WINDOW_CYCLES register

- Absolute Address: 0x11B8
- Base Offset: 0x1B8
- Size: 0x4

<p>LIVE free-running window-cycle counter. Valid only while
WRMON_PERF_STATUS.WIN_ACTIVE=1; the monitor ZEROES this when the
window closes (RUN-&gt;0). For a closed window, use the sum of the
four bucket registers (PROD+BP+STARV+IDLE), which HOLD their
values after close.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Window cycles [31:0] (live-only; reads 0 after close)</p>

### WRMON_PERF_PROD_CYCLES register

- Absolute Address: 0x11BC
- Base Offset: 0x1BC
- Size: 0x4

<p>Cycles with W data valid &amp;&amp; ready (beat delivered)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Productive cycles [31:0]</p>

### WRMON_PERF_BP_CYCLES register

- Absolute Address: 0x11C0
- Base Offset: 0x1C0
- Size: 0x4

<p>Cycles with W data valid &amp;&amp; !ready (back-pressure)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Backpressure cycles [31:0]</p>

### WRMON_PERF_STARV_CYCLES register

- Absolute Address: 0x11C4
- Base Offset: 0x1C4
- Size: 0x4

<p>Cycles with !W data valid &amp;&amp; ready (starvation)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Starvation cycles [31:0]</p>

### WRMON_PERF_IDLE_CYCLES register

- Absolute Address: 0x11C8
- Base Offset: 0x1C8
- Size: 0x4

<p>Cycles with !W data valid &amp;&amp; !ready (idle)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Idle cycles [31:0]</p>

### WRMON_PERF_BEAT_COUNT register

- Absolute Address: 0x11CC
- Base Offset: 0x1CC
- Size: 0x4

<p>W beats transferred in window (= productive cycles)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Beat count [31:0]</p>

### WRMON_PERF_BYTE_COUNT_LO register

- Absolute Address: 0x11D0
- Base Offset: 0x1D0
- Size: 0x4

<p>Bytes transferred in window (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [31:0]</p>

### WRMON_PERF_BYTE_COUNT_HI register

- Absolute Address: 0x11D4
- Base Offset: 0x1D4
- Size: 0x4

<p>Bytes transferred in window (upper 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [63:32]</p>

### WRMON_PERF_BURST_COUNT register

- Absolute Address: 0x11D8
- Base Offset: 0x1D8
- Size: 0x4

<p>AW handshakes (bursts issued) in window</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Burst count [31:0]</p>

### RDMON_PERF_CH_PROD_BP register

- Absolute Address: 0x11E0
- Base Offset: 0x1E0
- Size: 0x4

<p>Selected channel: {backpressure[31:16], productive[15:0]} (16-bit each)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>{bp[15:0], prod[15:0]} for PERF_CH_SEL channel</p>

### RDMON_PERF_CH_STARV_IDLE register

- Absolute Address: 0x11E4
- Base Offset: 0x1E4
- Size: 0x4

<p>Selected channel: {idle[31:16], starvation[15:0]} (16-bit each)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>{idle[15:0], starv[15:0]} for PERF_CH_SEL channel</p>

### WRMON_PERF_CH_PROD_BP register

- Absolute Address: 0x11E8
- Base Offset: 0x1E8
- Size: 0x4

<p>Selected channel: {backpressure[31:16], productive[15:0]} (16-bit each)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>{bp[15:0], prod[15:0]} for PERF_CH_SEL channel</p>

### WRMON_PERF_CH_STARV_IDLE register

- Absolute Address: 0x11EC
- Base Offset: 0x1EC
- Size: 0x4

<p>Selected channel: {idle[31:16], starvation[15:0]} (16-bit each)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>{idle[15:0], starv[15:0]} for PERF_CH_SEL channel</p>

### RDMON_PERF_CH_OVERFLOW register

- Absolute Address: 0x11F0
- Base Offset: 0x1F0
- Size: 0x4

<p>All channels, {prod,bp,starv,idle} sticky overflow per channel
(4 bits/channel, channel 0 in the low nibble). A set bit means
that 16-bit per-channel bucket wrapped during the window.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Per-channel overflow mask (NUM_CHANNELS*4 bits)</p>

### WRMON_PERF_CH_OVERFLOW register

- Absolute Address: 0x11F4
- Base Offset: 0x1F4
- Size: 0x4

<p>All channels, {prod,bp,starv,idle} sticky overflow per channel.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Per-channel overflow mask (NUM_CHANNELS*4 bits)</p>

### RDMON_ADDR_RANGE0_LOW register

- Absolute Address: 0x1200
- Base Offset: 0x200
- Size: 0x4

<p>Read monitor range0 inclusive low bound</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### RDMON_ADDR_RANGE0_HIGH register

- Absolute Address: 0x1204
- Base Offset: 0x204
- Size: 0x4

<p>Read monitor range0 inclusive high bound</p>

|Bits|Identifier|Access|   Reset  |Name|
|----|----------|------|----------|----|
|31:0|   VALUE  |  rw  |0xFFFFFFFF|  — |

### RDMON_ADDR_RANGE1_LOW register

- Absolute Address: 0x1208
- Base Offset: 0x208
- Size: 0x4

<p>Read monitor range1 inclusive low bound</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### RDMON_ADDR_RANGE1_HIGH register

- Absolute Address: 0x120C
- Base Offset: 0x20C
- Size: 0x4

<p>Read monitor range1 inclusive high bound</p>

|Bits|Identifier|Access|   Reset  |Name|
|----|----------|------|----------|----|
|31:0|   VALUE  |  rw  |0xFFFFFFFF|  — |

### RDMON_ADDR_RANGE2_LOW register

- Absolute Address: 0x1210
- Base Offset: 0x210
- Size: 0x4

<p>Read monitor range2 inclusive low bound</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### RDMON_ADDR_RANGE2_HIGH register

- Absolute Address: 0x1214
- Base Offset: 0x214
- Size: 0x4

<p>Read monitor range2 inclusive high bound</p>

|Bits|Identifier|Access|   Reset  |Name|
|----|----------|------|----------|----|
|31:0|   VALUE  |  rw  |0xFFFFFFFF|  — |

### RDMON_ADDR_RANGE3_LOW register

- Absolute Address: 0x1218
- Base Offset: 0x218
- Size: 0x4

<p>Read monitor range3 inclusive low bound</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### RDMON_ADDR_RANGE3_HIGH register

- Absolute Address: 0x121C
- Base Offset: 0x21C
- Size: 0x4

<p>Read monitor range3 inclusive high bound</p>

|Bits|Identifier|Access|   Reset  |Name|
|----|----------|------|----------|----|
|31:0|   VALUE  |  rw  |0xFFFFFFFF|  — |

### RDMON_ADDR_RANGE_CTRL register

- Absolute Address: 0x1220
- Base Offset: 0x220
- Size: 0x4

<p>Read monitor address-range checker enables</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 3:0| RANGE_EN |  rw  | 0x0 |  — |
|  4 | CHECK_EN |  rw  | 0x0 |  — |
|  5 | MATCH_EN |  rw  | 0x0 |  — |
|  6 |  MISS_EN |  rw  | 0x0 |  — |

#### RANGE_EN field

<p>Per-range enable mask (bit i enables range i)</p>

#### CHECK_EN field

<p>Master addr-check enable</p>

#### MATCH_EN field

<p>DEBUG/match path enable (drives cfg_debug_enable)</p>

#### MISS_EN field

<p>ERROR/miss path enable (drives cfg_error_enable)</p>

### WRMON_ADDR_RANGE0_LOW register

- Absolute Address: 0x1230
- Base Offset: 0x230
- Size: 0x4

<p>Write monitor range0 inclusive low bound</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### WRMON_ADDR_RANGE0_HIGH register

- Absolute Address: 0x1234
- Base Offset: 0x234
- Size: 0x4

<p>Write monitor range0 inclusive high bound</p>

|Bits|Identifier|Access|   Reset  |Name|
|----|----------|------|----------|----|
|31:0|   VALUE  |  rw  |0xFFFFFFFF|  — |

### WRMON_ADDR_RANGE1_LOW register

- Absolute Address: 0x1238
- Base Offset: 0x238
- Size: 0x4

<p>Write monitor range1 inclusive low bound</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### WRMON_ADDR_RANGE1_HIGH register

- Absolute Address: 0x123C
- Base Offset: 0x23C
- Size: 0x4

<p>Write monitor range1 inclusive high bound</p>

|Bits|Identifier|Access|   Reset  |Name|
|----|----------|------|----------|----|
|31:0|   VALUE  |  rw  |0xFFFFFFFF|  — |

### WRMON_ADDR_RANGE2_LOW register

- Absolute Address: 0x1240
- Base Offset: 0x240
- Size: 0x4

<p>Write monitor range2 inclusive low bound</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### WRMON_ADDR_RANGE2_HIGH register

- Absolute Address: 0x1244
- Base Offset: 0x244
- Size: 0x4

<p>Write monitor range2 inclusive high bound</p>

|Bits|Identifier|Access|   Reset  |Name|
|----|----------|------|----------|----|
|31:0|   VALUE  |  rw  |0xFFFFFFFF|  — |

### WRMON_ADDR_RANGE3_LOW register

- Absolute Address: 0x1248
- Base Offset: 0x248
- Size: 0x4

<p>Write monitor range3 inclusive low bound</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### WRMON_ADDR_RANGE3_HIGH register

- Absolute Address: 0x124C
- Base Offset: 0x24C
- Size: 0x4

<p>Write monitor range3 inclusive high bound</p>

|Bits|Identifier|Access|   Reset  |Name|
|----|----------|------|----------|----|
|31:0|   VALUE  |  rw  |0xFFFFFFFF|  — |

### WRMON_ADDR_RANGE_CTRL register

- Absolute Address: 0x1250
- Base Offset: 0x250
- Size: 0x4

<p>Write monitor address-range checker enables</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 3:0| RANGE_EN |  rw  | 0x0 |  — |
|  4 | CHECK_EN |  rw  | 0x0 |  — |
|  5 | MATCH_EN |  rw  | 0x0 |  — |
|  6 |  MISS_EN |  rw  | 0x0 |  — |

#### RANGE_EN field

<p>Per-range enable mask (bit i enables range i)</p>

#### CHECK_EN field

<p>Master addr-check enable</p>

#### MATCH_EN field

<p>DEBUG/match path enable (drives cfg_debug_enable)</p>

#### MISS_EN field

<p>ERROR/miss path enable (drives cfg_error_enable)</p>

### MON_GROUP_BASE_ADDR register

- Absolute Address: 0x1260
- Base Offset: 0x260
- Size: 0x4

<p>Master-write window inclusive low bound (monbus bulk-trace)</p>

|Bits|Identifier|Access| Reset |Name|
|----|----------|------|-------|----|
|31:0|   VALUE  |  rw  |0x40000|  — |

### MON_GROUP_LIMIT_ADDR register

- Absolute Address: 0x1264
- Base Offset: 0x264
- Size: 0x4

<p>Master-write window inclusive high bound (monbus bulk-trace)</p>

|Bits|Identifier|Access| Reset |Name|
|----|----------|------|-------|----|
|31:0|   VALUE  |  rw  |0x7FFFF|  — |

### MON_GROUP_FLUSH_WATERMARK register

- Absolute Address: 0x1268
- Base Offset: 0x268
- Size: 0x4

<p>Flush burst once this many beats buffered; 0 = flush every complete record</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|15:0|   VALUE  |  rw  | 0x0 |  — |
