<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## stream_regs address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x2B4

<p>Configuration and status registers for 8-channel STREAM DMA engine with full monitor control</p>

|Offset|      Identifier     |                     Name                     |
|------|---------------------|----------------------------------------------|
| 0x100|     GLOBAL_CTRL     |            Global Control Register           |
| 0x104|    GLOBAL_STATUS    |            Global Status Register            |
| 0x108|       VERSION       |               Version Register               |
| 0x120|    CHANNEL_ENABLE   |            Channel Enable Register           |
| 0x124|    CHANNEL_RESET    |            Channel Reset Register            |
| 0x140|     CHANNEL_IDLE    |              Channel Idle Status             |
| 0x144|   DESC_ENGINE_IDLE  |         Descriptor Engine Idle Status        |
| 0x148|    SCHEDULER_IDLE   |             Scheduler Idle Status            |
| 0x150|     CH_STATE[0]     |          Per-Channel State Registers         |
| 0x154|     CH_STATE[1]     |          Per-Channel State Registers         |
| 0x158|     CH_STATE[2]     |          Per-Channel State Registers         |
| 0x15C|     CH_STATE[3]     |          Per-Channel State Registers         |
| 0x160|     CH_STATE[4]     |          Per-Channel State Registers         |
| 0x164|     CH_STATE[5]     |          Per-Channel State Registers         |
| 0x168|     CH_STATE[6]     |          Per-Channel State Registers         |
| 0x16C|     CH_STATE[7]     |          Per-Channel State Registers         |
| 0x170|     SCHED_ERROR     |            Scheduler Error Status            |
| 0x174|   AXI_RD_COMPLETE   |       AXI Read Engine Completion Status      |
| 0x178|   AXI_WR_COMPLETE   |      AXI Write Engine Completion Status      |
| 0x180|   MON_FIFO_STATUS   |              Monitor FIFO Status             |
| 0x184|    MON_FIFO_COUNT   |              Monitor FIFO Count              |
| 0x200| SCHED_TIMEOUT_CYCLES|           Scheduler Timeout Cycles           |
| 0x204|     SCHED_CONFIG    |            Scheduler Configuration           |
| 0x220|    DESCENG_CONFIG   |        Descriptor Engine Configuration       |
| 0x224|  DESCENG_ADDR0_BASE |        Descriptor Address Range 0 Base       |
| 0x228| DESCENG_ADDR0_LIMIT |       Descriptor Address Range 0 Limit       |
| 0x22C|  DESCENG_ADDR1_BASE |        Descriptor Address Range 1 Base       |
| 0x230| DESCENG_ADDR1_LIMIT |       Descriptor Address Range 1 Limit       |
| 0x240|    DAXMON_ENABLE    |         Descriptor AXI Monitor Enable        |
| 0x244|    DAXMON_TIMEOUT   |        Descriptor AXI Monitor Timeout        |
| 0x248|DAXMON_LATENCY_THRESH|   Descriptor AXI Monitor Latency Threshold   |
| 0x24C|   DAXMON_PKT_MASK   |      Descriptor AXI Monitor Packet Mask      |
| 0x250|    DAXMON_ERR_CFG   | Descriptor AXI Monitor Error Select and Mask |
| 0x254|     DAXMON_MASK1    |        Descriptor AXI Monitor Masks 1        |
| 0x258|     DAXMON_MASK2    |        Descriptor AXI Monitor Masks 2        |
| 0x25C|     DAXMON_MASK3    |        Descriptor AXI Monitor Masks 3        |
| 0x260|     RDMON_ENABLE    |        Read Engine AXI Monitor Enable        |
| 0x264|    RDMON_TIMEOUT    |        Read Engine AXI Monitor Timeout       |
| 0x268| RDMON_LATENCY_THRESH|   Read Engine AXI Monitor Latency Threshold  |
| 0x26C|    RDMON_PKT_MASK   |      Read Engine AXI Monitor Packet Mask     |
| 0x270|    RDMON_ERR_CFG    | Read Engine AXI Monitor Error Select and Mask|
| 0x274|     RDMON_MASK1     |        Read Engine AXI Monitor Masks 1       |
| 0x278|     RDMON_MASK2     |        Read Engine AXI Monitor Masks 2       |
| 0x27C|     RDMON_MASK3     |        Read Engine AXI Monitor Masks 3       |
| 0x280|     WRMON_ENABLE    |        Write Engine AXI Monitor Enable       |
| 0x284|    WRMON_TIMEOUT    |       Write Engine AXI Monitor Timeout       |
| 0x288| WRMON_LATENCY_THRESH|  Write Engine AXI Monitor Latency Threshold  |
| 0x28C|    WRMON_PKT_MASK   |     Write Engine AXI Monitor Packet Mask     |
| 0x290|    WRMON_ERR_CFG    |Write Engine AXI Monitor Error Select and Mask|
| 0x294|     WRMON_MASK1     |       Write Engine AXI Monitor Masks 1       |
| 0x298|     WRMON_MASK2     |       Write Engine AXI Monitor Masks 2       |
| 0x29C|     WRMON_MASK3     |       Write Engine AXI Monitor Masks 3       |
| 0x2A0|   AXI_XFER_CONFIG   |          AXI Transfer Configuration          |
| 0x2B0|     PERF_CONFIG     |      Performance Profiler Configuration      |

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

### MON_FIFO_STATUS register

- Absolute Address: 0x180
- Base Offset: 0x180
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

- Absolute Address: 0x184
- Base Offset: 0x184
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

### SCHED_TIMEOUT_CYCLES register

- Absolute Address: 0x200
- Base Offset: 0x200
- Size: 0x4

<p>Timeout threshold in clock cycles (global for all channels)</p>

| Bits|  Identifier  |Access|Reset|Name|
|-----|--------------|------|-----|----|
| 15:0|TIMEOUT_CYCLES|  rw  |0x3E8|  — |
|31:16|     RSVD     |   r  | 0x0 |  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [15:0] - number of cycles before timeout</p>

#### RSVD field

<p>Reserved</p>

### SCHED_CONFIG register

- Absolute Address: 0x204
- Base Offset: 0x204
- Size: 0x4

<p>Scheduler feature enables (global for all channels)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 | SCHED_EN |  rw  | 0x1 |  — |
|  1 |TIMEOUT_EN|  rw  | 0x1 |  — |
|  2 |  ERR_EN  |  rw  | 0x1 |  — |
|  3 | COMPL_EN |  rw  | 0x1 |  — |
|  4 |  PERF_EN |  rw  | 0x0 |  — |
|31:5|   RSVD   |   r  | 0x0 |  — |

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

#### RSVD field

<p>Reserved</p>

### DESCENG_CONFIG register

- Absolute Address: 0x220
- Base Offset: 0x220
- Size: 0x4

<p>Descriptor engine feature enables (global for all channels)</p>

|Bits| Identifier|Access|Reset|Name|
|----|-----------|------|-----|----|
|  0 | DESCENG_EN|  rw  | 0x1 |  — |
|  1 |PREFETCH_EN|  rw  | 0x0 |  — |
| 5:2|FIFO_THRESH|  rw  | 0x8 |  — |
|31:6|    RSVD   |   r  | 0x0 |  — |

#### DESCENG_EN field

<p>Descriptor engine enable - master enable</p>

#### PREFETCH_EN field

<p>Prefetch enable - enable descriptor prefetch</p>

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

### DAXMON_ENABLE register

- Absolute Address: 0x240
- Base Offset: 0x240
- Size: 0x4

<p>Descriptor AXI master monitor enable controls</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |  MON_EN  |  rw  | 0x1 |  — |
|  1 |  ERR_EN  |  rw  | 0x1 |  — |
|  2 | COMPL_EN |  rw  | 0x0 |  — |
|  3 |TIMEOUT_EN|  rw  | 0x1 |  — |
|  4 |  PERF_EN |  rw  | 0x0 |  — |
|31:5|   RSVD   |   r  | 0x0 |  — |

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

#### RSVD field

<p>Reserved</p>

### DAXMON_TIMEOUT register

- Absolute Address: 0x244
- Base Offset: 0x244
- Size: 0x4

<p>Descriptor AXI monitor timeout threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x2710|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0]</p>

### DAXMON_LATENCY_THRESH register

- Absolute Address: 0x248
- Base Offset: 0x248
- Size: 0x4

<p>Descriptor AXI monitor latency threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|LATENCY_THRESH|  rw  |0x1388|  — |

#### LATENCY_THRESH field

<p>Latency threshold cycles [31:0]</p>

### DAXMON_PKT_MASK register

- Absolute Address: 0x24C
- Base Offset: 0x24C
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

- Absolute Address: 0x250
- Base Offset: 0x250
- Size: 0x4

<p>Descriptor AXI monitor error selection and filtering</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 3:0 |ERR_SELECT|  rw  | 0x0 |  — |
| 7:4 |   RSVD1  |   r  | 0x0 |  — |
| 15:8| ERR_MASK |  rw  | 0xFF|  — |
|31:16|   RSVD2  |   r  | 0x0 |  — |

#### ERR_SELECT field

<p>Error select [3:0] - error type selection</p>

#### RSVD1 field

<p>Reserved</p>

#### ERR_MASK field

<p>Error mask [15:8] - error type filtering</p>

#### RSVD2 field

<p>Reserved</p>

### DAXMON_MASK1 register

- Absolute Address: 0x254
- Base Offset: 0x254
- Size: 0x4

<p>Descriptor AXI monitor timeout and completion masks</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 7:0 |TIMEOUT_MASK|  rw  | 0xFF|  — |
| 15:8| COMPL_MASK |  rw  | 0x0 |  — |
|31:16|    RSVD    |   r  | 0x0 |  — |

#### TIMEOUT_MASK field

<p>Timeout mask [7:0]</p>

#### COMPL_MASK field

<p>Completion mask [15:8]</p>

#### RSVD field

<p>Reserved</p>

### DAXMON_MASK2 register

- Absolute Address: 0x258
- Base Offset: 0x258
- Size: 0x4

<p>Descriptor AXI monitor threshold and performance masks</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 7:0 |THRESH_MASK|  rw  | 0xFF|  — |
| 15:8| PERF_MASK |  rw  | 0x0 |  — |
|31:16|    RSVD   |   r  | 0x0 |  — |

#### THRESH_MASK field

<p>Threshold mask [7:0]</p>

#### PERF_MASK field

<p>Performance mask [15:8]</p>

#### RSVD field

<p>Reserved</p>

### DAXMON_MASK3 register

- Absolute Address: 0x25C
- Base Offset: 0x25C
- Size: 0x4

<p>Descriptor AXI monitor address and debug masks</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | ADDR_MASK|  rw  | 0xFF|  — |
| 15:8|DEBUG_MASK|  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### ADDR_MASK field

<p>Address mask [7:0]</p>

#### DEBUG_MASK field

<p>Debug mask [15:8]</p>

#### RSVD field

<p>Reserved</p>

### RDMON_ENABLE register

- Absolute Address: 0x260
- Base Offset: 0x260
- Size: 0x4

<p>Read engine AXI master monitor enable controls</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |  MON_EN  |  rw  | 0x1 |  — |
|  1 |  ERR_EN  |  rw  | 0x1 |  — |
|  2 | COMPL_EN |  rw  | 0x0 |  — |
|  3 |TIMEOUT_EN|  rw  | 0x1 |  — |
|  4 |  PERF_EN |  rw  | 0x0 |  — |
|31:5|   RSVD   |   r  | 0x0 |  — |

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

#### RSVD field

<p>Reserved</p>

### RDMON_TIMEOUT register

- Absolute Address: 0x264
- Base Offset: 0x264
- Size: 0x4

<p>Read engine AXI monitor timeout threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x2710|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0]</p>

### RDMON_LATENCY_THRESH register

- Absolute Address: 0x268
- Base Offset: 0x268
- Size: 0x4

<p>Read engine AXI monitor latency threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|LATENCY_THRESH|  rw  |0x1388|  — |

#### LATENCY_THRESH field

<p>Latency threshold cycles [31:0]</p>

### RDMON_PKT_MASK register

- Absolute Address: 0x26C
- Base Offset: 0x26C
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

- Absolute Address: 0x270
- Base Offset: 0x270
- Size: 0x4

<p>Read engine AXI monitor error selection and filtering</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 3:0 |ERR_SELECT|  rw  | 0x0 |  — |
| 7:4 |   RSVD1  |   r  | 0x0 |  — |
| 15:8| ERR_MASK |  rw  | 0xFF|  — |
|31:16|   RSVD2  |   r  | 0x0 |  — |

#### ERR_SELECT field

<p>Error select [3:0] - error type selection</p>

#### RSVD1 field

<p>Reserved</p>

#### ERR_MASK field

<p>Error mask [15:8] - error type filtering</p>

#### RSVD2 field

<p>Reserved</p>

### RDMON_MASK1 register

- Absolute Address: 0x274
- Base Offset: 0x274
- Size: 0x4

<p>Read engine AXI monitor timeout and completion masks</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 7:0 |TIMEOUT_MASK|  rw  | 0xFF|  — |
| 15:8| COMPL_MASK |  rw  | 0x0 |  — |
|31:16|    RSVD    |   r  | 0x0 |  — |

#### TIMEOUT_MASK field

<p>Timeout mask [7:0]</p>

#### COMPL_MASK field

<p>Completion mask [15:8]</p>

#### RSVD field

<p>Reserved</p>

### RDMON_MASK2 register

- Absolute Address: 0x278
- Base Offset: 0x278
- Size: 0x4

<p>Read engine AXI monitor threshold and performance masks</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 7:0 |THRESH_MASK|  rw  | 0xFF|  — |
| 15:8| PERF_MASK |  rw  | 0x0 |  — |
|31:16|    RSVD   |   r  | 0x0 |  — |

#### THRESH_MASK field

<p>Threshold mask [7:0]</p>

#### PERF_MASK field

<p>Performance mask [15:8]</p>

#### RSVD field

<p>Reserved</p>

### RDMON_MASK3 register

- Absolute Address: 0x27C
- Base Offset: 0x27C
- Size: 0x4

<p>Read engine AXI monitor address and debug masks</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | ADDR_MASK|  rw  | 0xFF|  — |
| 15:8|DEBUG_MASK|  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### ADDR_MASK field

<p>Address mask [7:0]</p>

#### DEBUG_MASK field

<p>Debug mask [15:8]</p>

#### RSVD field

<p>Reserved</p>

### WRMON_ENABLE register

- Absolute Address: 0x280
- Base Offset: 0x280
- Size: 0x4

<p>Write engine AXI master monitor enable controls</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |  MON_EN  |  rw  | 0x1 |  — |
|  1 |  ERR_EN  |  rw  | 0x1 |  — |
|  2 | COMPL_EN |  rw  | 0x0 |  — |
|  3 |TIMEOUT_EN|  rw  | 0x1 |  — |
|  4 |  PERF_EN |  rw  | 0x0 |  — |
|31:5|   RSVD   |   r  | 0x0 |  — |

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

#### RSVD field

<p>Reserved</p>

### WRMON_TIMEOUT register

- Absolute Address: 0x284
- Base Offset: 0x284
- Size: 0x4

<p>Write engine AXI monitor timeout threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x2710|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0]</p>

### WRMON_LATENCY_THRESH register

- Absolute Address: 0x288
- Base Offset: 0x288
- Size: 0x4

<p>Write engine AXI monitor latency threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|LATENCY_THRESH|  rw  |0x1388|  — |

#### LATENCY_THRESH field

<p>Latency threshold cycles [31:0]</p>

### WRMON_PKT_MASK register

- Absolute Address: 0x28C
- Base Offset: 0x28C
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

- Absolute Address: 0x290
- Base Offset: 0x290
- Size: 0x4

<p>Write engine AXI monitor error selection and filtering</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 3:0 |ERR_SELECT|  rw  | 0x0 |  — |
| 7:4 |   RSVD1  |   r  | 0x0 |  — |
| 15:8| ERR_MASK |  rw  | 0xFF|  — |
|31:16|   RSVD2  |   r  | 0x0 |  — |

#### ERR_SELECT field

<p>Error select [3:0] - error type selection</p>

#### RSVD1 field

<p>Reserved</p>

#### ERR_MASK field

<p>Error mask [15:8] - error type filtering</p>

#### RSVD2 field

<p>Reserved</p>

### WRMON_MASK1 register

- Absolute Address: 0x294
- Base Offset: 0x294
- Size: 0x4

<p>Write engine AXI monitor timeout and completion masks</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 7:0 |TIMEOUT_MASK|  rw  | 0xFF|  — |
| 15:8| COMPL_MASK |  rw  | 0x0 |  — |
|31:16|    RSVD    |   r  | 0x0 |  — |

#### TIMEOUT_MASK field

<p>Timeout mask [7:0]</p>

#### COMPL_MASK field

<p>Completion mask [15:8]</p>

#### RSVD field

<p>Reserved</p>

### WRMON_MASK2 register

- Absolute Address: 0x298
- Base Offset: 0x298
- Size: 0x4

<p>Write engine AXI monitor threshold and performance masks</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 7:0 |THRESH_MASK|  rw  | 0xFF|  — |
| 15:8| PERF_MASK |  rw  | 0x0 |  — |
|31:16|    RSVD   |   r  | 0x0 |  — |

#### THRESH_MASK field

<p>Threshold mask [7:0]</p>

#### PERF_MASK field

<p>Performance mask [15:8]</p>

#### RSVD field

<p>Reserved</p>

### WRMON_MASK3 register

- Absolute Address: 0x29C
- Base Offset: 0x29C
- Size: 0x4

<p>Write engine AXI monitor address and debug masks</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | ADDR_MASK|  rw  | 0xFF|  — |
| 15:8|DEBUG_MASK|  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### ADDR_MASK field

<p>Address mask [7:0]</p>

#### DEBUG_MASK field

<p>Debug mask [15:8]</p>

#### RSVD field

<p>Reserved</p>

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
