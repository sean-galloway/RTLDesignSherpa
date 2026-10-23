<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## rapids_regs_16ch address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x1A00

<p>Two independent halves: SRC @ 0x0000, SNK @ 0x1000 (each 4KB; monitors @ +0x800)</p>

|Offset|Identifier|                  Name                 |
|------|----------|---------------------------------------|
|0x0000|    SRC   |RAPIDS (beats) per-engine register file|
|0x1000|    SNK   |RAPIDS (beats) per-engine register file|

## SRC register file

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0xA00

<p>Config/status + monitors for one RAPIDS engine (source or sink)</p>

|Offset|     Identifier     |                 Name                 |
|------|--------------------|--------------------------------------|
| 0x000|  CH0_DESC_ADDR_LOW |           Ch0 desc addr LOW          |
| 0x004| CH0_DESC_ADDR_HIGH |          Ch0 desc addr HIGH          |
| 0x008|  CH1_DESC_ADDR_LOW |           Ch1 desc addr LOW          |
| 0x00C| CH1_DESC_ADDR_HIGH |          Ch1 desc addr HIGH          |
| 0x010|  CH2_DESC_ADDR_LOW |           Ch2 desc addr LOW          |
| 0x014| CH2_DESC_ADDR_HIGH |          Ch2 desc addr HIGH          |
| 0x018|  CH3_DESC_ADDR_LOW |           Ch3 desc addr LOW          |
| 0x01C| CH3_DESC_ADDR_HIGH |          Ch3 desc addr HIGH          |
| 0x020|  CH4_DESC_ADDR_LOW |           Ch4 desc addr LOW          |
| 0x024| CH4_DESC_ADDR_HIGH |          Ch4 desc addr HIGH          |
| 0x028|  CH5_DESC_ADDR_LOW |           Ch5 desc addr LOW          |
| 0x02C| CH5_DESC_ADDR_HIGH |          Ch5 desc addr HIGH          |
| 0x030|  CH6_DESC_ADDR_LOW |           Ch6 desc addr LOW          |
| 0x034| CH6_DESC_ADDR_HIGH |          Ch6 desc addr HIGH          |
| 0x038|  CH7_DESC_ADDR_LOW |           Ch7 desc addr LOW          |
| 0x03C| CH7_DESC_ADDR_HIGH |          Ch7 desc addr HIGH          |
| 0x040|  CH8_DESC_ADDR_LOW |           Ch8 desc addr LOW          |
| 0x044| CH8_DESC_ADDR_HIGH |          Ch8 desc addr HIGH          |
| 0x048|  CH9_DESC_ADDR_LOW |           Ch9 desc addr LOW          |
| 0x04C| CH9_DESC_ADDR_HIGH |          Ch9 desc addr HIGH          |
| 0x050| CH10_DESC_ADDR_LOW |          Ch10 desc addr LOW          |
| 0x054| CH10_DESC_ADDR_HIGH|          Ch10 desc addr HIGH         |
| 0x058| CH11_DESC_ADDR_LOW |          Ch11 desc addr LOW          |
| 0x05C| CH11_DESC_ADDR_HIGH|          Ch11 desc addr HIGH         |
| 0x060| CH12_DESC_ADDR_LOW |          Ch12 desc addr LOW          |
| 0x064| CH12_DESC_ADDR_HIGH|          Ch12 desc addr HIGH         |
| 0x068| CH13_DESC_ADDR_LOW |          Ch13 desc addr LOW          |
| 0x06C| CH13_DESC_ADDR_HIGH|          Ch13 desc addr HIGH         |
| 0x070| CH14_DESC_ADDR_LOW |          Ch14 desc addr LOW          |
| 0x074| CH14_DESC_ADDR_HIGH|          Ch14 desc addr HIGH         |
| 0x078| CH15_DESC_ADDR_LOW |          Ch15 desc addr LOW          |
| 0x07C| CH15_DESC_ADDR_HIGH|          Ch15 desc addr HIGH         |
| 0x080|     KICK_ENABLE    |              Kick enable             |
| 0x100|     GLOBAL_CTRL    |        Global Control Register       |
| 0x104|    GLOBAL_STATUS   |        Global Status Register        |
| 0x108|       VERSION      |           Version Register           |
| 0x120|   CHANNEL_ENABLE   |        Channel Enable Register       |
| 0x124|    CHANNEL_RESET   |        Channel Reset Register        |
| 0x140|    CHANNEL_IDLE    |          Channel Idle Status         |
| 0x144|  DESC_ENGINE_IDLE  |     Descriptor Engine Idle Status    |
| 0x148|   SCHEDULER_IDLE   |         Scheduler Idle Status        |
| 0x170|     SCHED_ERROR    |        Scheduler Error Status        |
| 0x174|   AXI_RD_COMPLETE  |   AXI Read Engine Completion Status  |
| 0x178|   AXI_WR_COMPLETE  |  AXI Write Engine Completion Status  |
| 0x180|     CH_STATE[0]    |      Per-Channel State Registers     |
| 0x184|     CH_STATE[1]    |      Per-Channel State Registers     |
| 0x188|     CH_STATE[2]    |      Per-Channel State Registers     |
| 0x18C|     CH_STATE[3]    |      Per-Channel State Registers     |
| 0x190|     CH_STATE[4]    |      Per-Channel State Registers     |
| 0x194|     CH_STATE[5]    |      Per-Channel State Registers     |
| 0x198|     CH_STATE[6]    |      Per-Channel State Registers     |
| 0x19C|     CH_STATE[7]    |      Per-Channel State Registers     |
| 0x1A0|     CH_STATE[8]    |      Per-Channel State Registers     |
| 0x1A4|     CH_STATE[9]    |      Per-Channel State Registers     |
| 0x1A8|    CH_STATE[10]    |      Per-Channel State Registers     |
| 0x1AC|    CH_STATE[11]    |      Per-Channel State Registers     |
| 0x1B0|    CH_STATE[12]    |      Per-Channel State Registers     |
| 0x1B4|    CH_STATE[13]    |      Per-Channel State Registers     |
| 0x1B8|    CH_STATE[14]    |      Per-Channel State Registers     |
| 0x1BC|    CH_STATE[15]    |      Per-Channel State Registers     |
| 0x200|SCHED_TIMEOUT_CYCLES|       Scheduler Timeout Cycles       |
| 0x204|    SCHED_CONFIG    |        Scheduler Configuration       |
| 0x208| SCHED_TIMEOUT_LIMIT|  Scheduler Timeout Escalation Limit  |
| 0x220|   DESCENG_CONFIG   |    Descriptor Engine Configuration   |
| 0x224| DESCENG_ADDR0_BASE |    Descriptor Address Range 0 Base   |
| 0x228| DESCENG_ADDR0_LIMIT|   Descriptor Address Range 0 Limit   |
| 0x22C| DESCENG_ADDR1_BASE |    Descriptor Address Range 1 Base   |
| 0x230| DESCENG_ADDR1_LIMIT|   Descriptor Address Range 1 Limit   |
| 0x240|     CTRL_CONFIG    |     Control Engine Configuration     |
| 0x2A0|   AXI_XFER_CONFIG  |      AXI Transfer Configuration      |
| 0x2B0|     PERF_CONFIG    |  Performance Profiler Configuration  |
| 0x2C0|      OBS_CTRL      |        Observation Mux Control       |
| 0x2C4|      OBS_FLAGS     |           Observation Flags          |
| 0x2C8|      OBS_DATA0     |          Observation Data 0          |
| 0x2CC|      OBS_DATA1     |          Observation Data 1          |
| 0x2D0|     TILE_STATUS    |          Tile Header Status          |
| 0x2D4|  TILE_DESC_DROPPED |         Cell Descriptor Drops        |
| 0x2D8|     TILE_COUNTS    |          Tile Packet Counts          |
| 0x2DC|   TILE_ADV_WINDOW  |       Tile Advertisement Window      |
| 0x2E0| TILE_LEGAL_DEST_LO |     Tile Legal Destinations, Low     |
| 0x2E4| TILE_CREDIT_STATUS |          Tile Credit Status          |
| 0x2E8| TILE_LEGAL_DEST_HI |     Tile Legal Destinations, High    |
| 0x2EC|     TILE_RESYNC    |          Tile Credit Resync          |
| 0x2F0|  TILE_STALL_CYCLES |      Tile Stalled-Data Threshold     |
| 0x2F4|    TILE_STALLED    |         Tile Stalled Channels        |
| 0x300|    CH_SCRATCH[0]   |          Per-Channel Scratch         |
| 0x304|    CH_SCRATCH[1]   |          Per-Channel Scratch         |
| 0x308|    CH_SCRATCH[2]   |          Per-Channel Scratch         |
| 0x30C|    CH_SCRATCH[3]   |          Per-Channel Scratch         |
| 0x310|    CH_SCRATCH[4]   |          Per-Channel Scratch         |
| 0x314|    CH_SCRATCH[5]   |          Per-Channel Scratch         |
| 0x318|    CH_SCRATCH[6]   |          Per-Channel Scratch         |
| 0x31C|    CH_SCRATCH[7]   |          Per-Channel Scratch         |
| 0x320|    CH_SCRATCH[8]   |          Per-Channel Scratch         |
| 0x324|    CH_SCRATCH[9]   |          Per-Channel Scratch         |
| 0x328|   CH_SCRATCH[10]   |          Per-Channel Scratch         |
| 0x32C|   CH_SCRATCH[11]   |          Per-Channel Scratch         |
| 0x330|   CH_SCRATCH[12]   |          Per-Channel Scratch         |
| 0x334|   CH_SCRATCH[13]   |          Per-Channel Scratch         |
| 0x338|   CH_SCRATCH[14]   |          Per-Channel Scratch         |
| 0x33C|   CH_SCRATCH[15]   |          Per-Channel Scratch         |
| 0x35C|     PERF_CH_SEL    |Per-Channel Perf Bucket Readout Select|
| 0x378|      HIST_SEL      |   Latency Histogram Readout Select   |
| 0x37C|      HIST_DATA     |      Latency Histogram Bin Count     |
| 0x380|     HIST_TOTAL     |    Latency Histogram Metric Total    |
| 0x7FC|     TILE_STRAPS    |              Tile Straps             |
| 0x800|         MON        |       RAPIDS Monitor Registers       |

### CH0_DESC_ADDR_LOW register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>Ch0 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH0_DESC_ADDR_HIGH register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

<p>Ch0 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH1_DESC_ADDR_LOW register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4

<p>Ch1 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH1_DESC_ADDR_HIGH register

- Absolute Address: 0xC
- Base Offset: 0xC
- Size: 0x4

<p>Ch1 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH2_DESC_ADDR_LOW register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>Ch2 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH2_DESC_ADDR_HIGH register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

<p>Ch2 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH3_DESC_ADDR_LOW register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

<p>Ch3 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH3_DESC_ADDR_HIGH register

- Absolute Address: 0x1C
- Base Offset: 0x1C
- Size: 0x4

<p>Ch3 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH4_DESC_ADDR_LOW register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

<p>Ch4 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH4_DESC_ADDR_HIGH register

- Absolute Address: 0x24
- Base Offset: 0x24
- Size: 0x4

<p>Ch4 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH5_DESC_ADDR_LOW register

- Absolute Address: 0x28
- Base Offset: 0x28
- Size: 0x4

<p>Ch5 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH5_DESC_ADDR_HIGH register

- Absolute Address: 0x2C
- Base Offset: 0x2C
- Size: 0x4

<p>Ch5 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH6_DESC_ADDR_LOW register

- Absolute Address: 0x30
- Base Offset: 0x30
- Size: 0x4

<p>Ch6 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH6_DESC_ADDR_HIGH register

- Absolute Address: 0x34
- Base Offset: 0x34
- Size: 0x4

<p>Ch6 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH7_DESC_ADDR_LOW register

- Absolute Address: 0x38
- Base Offset: 0x38
- Size: 0x4

<p>Ch7 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH7_DESC_ADDR_HIGH register

- Absolute Address: 0x3C
- Base Offset: 0x3C
- Size: 0x4

<p>Ch7 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH8_DESC_ADDR_LOW register

- Absolute Address: 0x40
- Base Offset: 0x40
- Size: 0x4

<p>Ch8 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH8_DESC_ADDR_HIGH register

- Absolute Address: 0x44
- Base Offset: 0x44
- Size: 0x4

<p>Ch8 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH9_DESC_ADDR_LOW register

- Absolute Address: 0x48
- Base Offset: 0x48
- Size: 0x4

<p>Ch9 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH9_DESC_ADDR_HIGH register

- Absolute Address: 0x4C
- Base Offset: 0x4C
- Size: 0x4

<p>Ch9 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH10_DESC_ADDR_LOW register

- Absolute Address: 0x50
- Base Offset: 0x50
- Size: 0x4

<p>Ch10 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH10_DESC_ADDR_HIGH register

- Absolute Address: 0x54
- Base Offset: 0x54
- Size: 0x4

<p>Ch10 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH11_DESC_ADDR_LOW register

- Absolute Address: 0x58
- Base Offset: 0x58
- Size: 0x4

<p>Ch11 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH11_DESC_ADDR_HIGH register

- Absolute Address: 0x5C
- Base Offset: 0x5C
- Size: 0x4

<p>Ch11 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH12_DESC_ADDR_LOW register

- Absolute Address: 0x60
- Base Offset: 0x60
- Size: 0x4

<p>Ch12 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH12_DESC_ADDR_HIGH register

- Absolute Address: 0x64
- Base Offset: 0x64
- Size: 0x4

<p>Ch12 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH13_DESC_ADDR_LOW register

- Absolute Address: 0x68
- Base Offset: 0x68
- Size: 0x4

<p>Ch13 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH13_DESC_ADDR_HIGH register

- Absolute Address: 0x6C
- Base Offset: 0x6C
- Size: 0x4

<p>Ch13 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH14_DESC_ADDR_LOW register

- Absolute Address: 0x70
- Base Offset: 0x70
- Size: 0x4

<p>Ch14 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH14_DESC_ADDR_HIGH register

- Absolute Address: 0x74
- Base Offset: 0x74
- Size: 0x4

<p>Ch14 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH15_DESC_ADDR_LOW register

- Absolute Address: 0x78
- Base Offset: 0x78
- Size: 0x4

<p>Ch15 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH15_DESC_ADDR_HIGH register

- Absolute Address: 0x7C
- Base Offset: 0x7C
- Size: 0x4

<p>Ch15 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### KICK_ENABLE register

- Absolute Address: 0x80
- Base Offset: 0x80
- Size: 0x4

<p>Write 1 to bit[ch] to launch that channel from its staged CHx_DESC_ADDR pair</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
|  0  |   KICK0  |   w  | 0x0 |  — |
|  1  |   KICK1  |   w  | 0x0 |  — |
|  2  |   KICK2  |   w  | 0x0 |  — |
|  3  |   KICK3  |   w  | 0x0 |  — |
|  4  |   KICK4  |   w  | 0x0 |  — |
|  5  |   KICK5  |   w  | 0x0 |  — |
|  6  |   KICK6  |   w  | 0x0 |  — |
|  7  |   KICK7  |   w  | 0x0 |  — |
|  8  |   KICK8  |   w  | 0x0 |  — |
|  9  |   KICK9  |   w  | 0x0 |  — |
|  10 |  KICK10  |   w  | 0x0 |  — |
|  11 |  KICK11  |   w  | 0x0 |  — |
|  12 |  KICK12  |   w  | 0x0 |  — |
|  13 |  KICK13  |   w  | 0x0 |  — |
|  14 |  KICK14  |   w  | 0x0 |  — |
|  15 |  KICK15  |   w  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### RSVD field

<p>Reserved</p>

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
|23:16|NUM_CHANNELS|   r  | 0x10|  — |
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

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|   CH_EN  |  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### CH_EN field

<p>Channel enable bits [15:0] - 1=enabled, 0=disabled</p>

#### RSVD field

<p>Reserved</p>

### CHANNEL_RESET register

- Absolute Address: 0x124
- Base Offset: 0x124
- Size: 0x4

<p>Per-channel reset bits (one bit per channel, self-clearing)</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|  CH_RST  |  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### CH_RST field

<p>Channel reset bits [15:0] - write 1 to reset channel</p>

#### RSVD field

<p>Reserved</p>

### CHANNEL_IDLE register

- Absolute Address: 0x140
- Base Offset: 0x140
- Size: 0x4

<p>Per-channel idle status (one bit per channel)</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|  CH_IDLE |   r  |  —  |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### CH_IDLE field

<p>Channel idle bits [15:0] - 1=idle, 0=active</p>

#### RSVD field

<p>Reserved</p>

### DESC_ENGINE_IDLE register

- Absolute Address: 0x144
- Base Offset: 0x144
- Size: 0x4

<p>Per-channel descriptor engine idle status</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| DESC_IDLE|   r  |  —  |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### DESC_IDLE field

<p>Descriptor engine idle bits [15:0] - 1=idle, 0=active</p>

#### RSVD field

<p>Reserved</p>

### SCHEDULER_IDLE register

- Absolute Address: 0x148
- Base Offset: 0x148
- Size: 0x4

<p>Per-channel scheduler idle status</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|SCHED_IDLE|   r  |  —  |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### SCHED_IDLE field

<p>Scheduler idle bits [15:0] - 1=idle, 0=active</p>

#### RSVD field

<p>Reserved</p>

### SCHED_ERROR register

- Absolute Address: 0x170
- Base Offset: 0x170
- Size: 0x4

<p>Per-channel scheduler error flags</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| SCHED_ERR|   r  |  —  |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### SCHED_ERR field

<p>Scheduler error bits [15:0] - 1=error detected, 0=no error</p>

#### RSVD field

<p>Reserved</p>

### AXI_RD_COMPLETE register

- Absolute Address: 0x174
- Base Offset: 0x174
- Size: 0x4

<p>Per-channel read engine all_complete flags</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 15:0|RD_COMPLETE|   r  |  —  |  — |
|31:16|    RSVD   |   r  | 0x0 |  — |

#### RD_COMPLETE field

<p>Read completion bits [15:0] - 1=all reads complete, 0=reads pending</p>

#### RSVD field

<p>Reserved</p>

### AXI_WR_COMPLETE register

- Absolute Address: 0x178
- Base Offset: 0x178
- Size: 0x4

<p>Per-channel write engine all_complete flags</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 15:0|WR_COMPLETE|   r  |  —  |  — |
|31:16|    RSVD   |   r  | 0x0 |  — |

#### WR_COMPLETE field

<p>Write completion bits [15:0] - 1=all writes complete, 0=writes pending</p>

#### RSVD field

<p>Reserved</p>

## CH_STATE register file

- Absolute Address: 0x180
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x180
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

- Absolute Address: 0x184
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x184
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

- Absolute Address: 0x188
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x188
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

- Absolute Address: 0x18C
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x18C
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

- Absolute Address: 0x190
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x190
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

- Absolute Address: 0x194
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x194
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

- Absolute Address: 0x198
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x198
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

- Absolute Address: 0x19C
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x19C
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

- Absolute Address: 0x1A0
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1A0
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

- Absolute Address: 0x1A4
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1A4
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

- Absolute Address: 0x1A8
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1A8
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

- Absolute Address: 0x1AC
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1AC
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

- Absolute Address: 0x1B0
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1B0
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

- Absolute Address: 0x1B4
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1B4
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

- Absolute Address: 0x1B8
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1B8
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

- Absolute Address: 0x1BC
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1BC
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

<p>Completion enable. 1 = the scheduler and the descriptor engine report CORE Completion packets (descriptor loaded, descriptor/chain complete) on the monitor bus; 0 = those packets are dropped at the scheduler group, and the emitters are acknowledged so nothing stalls. Error packets are not gated by this bit (or by ERR_EN).</p>

#### PERF_EN field

<p>Performance enable - enable performance monitoring</p>

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

### CTRL_CONFIG register

- Absolute Address: 0x240
- Base Offset: 0x240
- Size: 0x4

<p>Control read/write engine configuration (global for all channels,
Phase 2 producer/consumer). CTRLRD_MAX_TRY bounds ctrl-read poll
retries so a never-matching gate cannot hang a channel; it feeds
cfg_ctrlrd_max_try into every channel's ctrlrd_engine.</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
| 8:0|CTRLRD_MAX_TRY|  rw  | 0x10|  — |
|31:9|     RSVD     |   r  | 0x0 |  — |

#### CTRLRD_MAX_TRY field

<p>Control-read poll retry budget [8:0] (0-511)</p>

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
|23:16|  ALLOC_SIZE |  rw  | 0x10|  — |
|31:24|  DRAIN_SIZE |  rw  | 0x10|  — |

#### RD_XFER_BEATS field

<p>AXI read transfer beats [7:0] - ARLEN value (0-255 represents 1-256 beats). The engine clamps it to the per-channel SRAM depth minus one, and to 254 beyond that (rapids BUG-009): a burst is never larger than the buffer that stages it</p>

#### WR_XFER_BEATS field

<p>AXI write transfer beats [15:8] - AWLEN value (0-255 represents 1-256 beats). The engine clamps it to the per-channel SRAM depth minus one, and to 254 beyond that (rapids BUG-009): a burst is never larger than the buffer that stages it</p>

#### ALLOC_SIZE field

<p>Sink AXIS SRAM allocation size [23:16] - segments reserved per AXIS fill burst</p>

#### DRAIN_SIZE field

<p>Source AXIS drain size [31:24] - beats drained to AXIS per packet request</p>

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

### TILE_STATUS register

- Absolute Address: 0x2D0
- Base Offset: 0x2D0
- Size: 0x4

<p>Sink-port tile header status (SNK half). Sticky; write 1 to clear.</p>

|Bits| Identifier |  Access |Reset|Name|
|----|------------|---------|-----|----|
|  0 | UNSUPPORTED|rw, woclr| 0x0 |  — |
|  1 |TAG_MISMATCH|rw, woclr| 0x0 |  — |
|31:2|    RSVD    |    r    | 0x0 |  — |

#### UNSUPPORTED field

<p>A packet the sink port consumed without acting on it: a read request to RAPIDS, a reserved ptype, a desc packet with no payload, a tag past NUM_CHANNELS or DATA_WIDTH &lt; 256, or extra desc payload. Sticky; write 1 to clear</p>

#### TAG_MISMATCH field

<p>A data packet whose header tag differed from its stream ID (delivered by stream ID). Sticky; write 1 to clear</p>

#### RSVD field

<p>Reserved</p>

### TILE_DESC_DROPPED register

- Absolute Address: 0x2D4
- Base Offset: 0x2D4
- Size: 0x4

<p>Per source channel: a cell-issued descriptor was dropped (SRC half). Sticky; write 1 to clear.</p>

| Bits|Identifier|  Access |Reset|Name|
|-----|----------|---------|-----|----|
|  0  |   DROP0  |rw, woclr| 0x0 |  — |
|  1  |   DROP1  |rw, woclr| 0x0 |  — |
|  2  |   DROP2  |rw, woclr| 0x0 |  — |
|  3  |   DROP3  |rw, woclr| 0x0 |  — |
|  4  |   DROP4  |rw, woclr| 0x0 |  — |
|  5  |   DROP5  |rw, woclr| 0x0 |  — |
|  6  |   DROP6  |rw, woclr| 0x0 |  — |
|  7  |   DROP7  |rw, woclr| 0x0 |  — |
|  8  |   DROP8  |rw, woclr| 0x0 |  — |
|  9  |   DROP9  |rw, woclr| 0x0 |  — |
|  10 |  DROP10  |rw, woclr| 0x0 |  — |
|  11 |  DROP11  |rw, woclr| 0x0 |  — |
|  12 |  DROP12  |rw, woclr| 0x0 |  — |
|  13 |  DROP13  |rw, woclr| 0x0 |  — |
|  14 |  DROP14  |rw, woclr| 0x0 |  — |
|  15 |  DROP15  |rw, woclr| 0x0 |  — |
|31:16|   RSVD   |    r    | 0x0 |  — |

#### DROP0 field

<p>Channel 0: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP1 field

<p>Channel 1: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP2 field

<p>Channel 2: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP3 field

<p>Channel 3: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP4 field

<p>Channel 4: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP5 field

<p>Channel 5: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP6 field

<p>Channel 6: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP7 field

<p>Channel 7: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP8 field

<p>Channel 8: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP9 field

<p>Channel 9: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP10 field

<p>Channel 10: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP11 field

<p>Channel 11: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP12 field

<p>Channel 12: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP13 field

<p>Channel 13: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP14 field

<p>Channel 14: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP15 field

<p>Channel 15: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### RSVD field

<p>Reserved</p>

### TILE_COUNTS register

- Absolute Address: 0x2D8
- Base Offset: 0x2D8
- Size: 0x4

<p>Sink-port packets passed on or consumed (SNK half); 16-bit counters that wrap</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 15:0| DESC_COUNT |   r  |  —  |  — |
|31:16|CREDIT_COUNT|   r  |  —  |  — |

#### DESC_COUNT field

<p>desc packets passed to the source half</p>

#### CREDIT_COUNT field

<p>credit packets received (with TILE_CREDITS = 1 they fill the SRC half's destination counters)</p>

### TILE_ADV_WINDOW register

- Absolute Address: 0x2DC
- Base Offset: 0x2DC
- Size: 0x4

<p>Cycles from reset during which destinations advertise their credits (SRC half). When the window closes, a destination whose counter is still 0 is illegal (TILE_LEGAL_DEST_LO/HI).</p>

|Bits|Identifier|Access| Reset|Name|
|----|----------|------|------|----|
|31:0|  CYCLES  |  rw  |0x1000|  — |

#### CYCLES field

<p>Window length in cycles from reset. Counted from reset, so a write takes effect only if made before the window closes; 0 closes it at once and makes every destination illegal</p>

### TILE_LEGAL_DEST_LO register

- Absolute Address: 0x2E0
- Base Offset: 0x2E0
- Size: 0x4

<p>Saved legal-destination mask, indices 0-31: the nodes' internal IDs (SRC half). 1 = the destination advertised a non-zero credit count in the window. Valid once TILE_CREDIT_STATUS.ADV_DONE is 1; held until reset. A descriptor to an illegal destination is refused as invalid.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   LEGAL  |   r  |  —  |  — |

#### LEGAL field

<p>Bit i: destination index i is legal</p>

### TILE_CREDIT_STATUS register

- Absolute Address: 0x2E4
- Base Offset: 0x2E4
- Size: 0x4

<p>End-to-end tile credit status (SRC half)</p>

| Bits|  Identifier  |Access|Reset|Name|
|-----|--------------|------|-----|----|
|  0  |   ADV_DONE   |   r  |  —  |  — |
|  1  |  RESYNC_BUSY |   r  |  —  |  — |
|  2  | LAND_OVERRUN |   r  |  —  |  — |
|  3  |INTAKE_OVERRUN|   r  |  —  |  — |
| 15:4|     RSVD     |   r  | 0x0 |  — |
|31:16|   RET_COUNT  |   r  |  —  |  — |

#### ADV_DONE field

<p>The advertisement window has closed and TILE_LEGAL_DEST_LO/HI are valid. Tile descriptors wait until it is 1</p>

#### RESYNC_BUSY field

<p>A resync (TILE_RESYNC) is waiting for the tile to be quiescent, or its set packets are still going out (rapids TASK-027)</p>

#### LAND_OVERRUN field

<p>Sticky until reset: a cell sent past its landing-space strap (TILE_LAND_FLITS); the sink port waited for room. A strap contract violation by the sender</p>

#### INTAKE_OVERRUN field

<p>Sticky until reset: a control core sent a desc packet past its intake strap (TILE_DESC_PER_CORE); the descriptor was dropped and its entry returned</p>

#### RSVD field

<p>Reserved</p>

#### RET_COUNT field

<p>Credit packets RAPIDS has sent to the cells and cores (returns and resync sets); 16-bit, wraps</p>

### TILE_LEGAL_DEST_HI register

- Absolute Address: 0x2E8
- Base Offset: 0x2E8
- Size: 0x4

<p>Saved legal-destination mask, indices 32-63: the external IDs, what is attached to each node (SRC half). Same rules as TILE_LEGAL_DEST_LO.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   LEGAL  |   r  |  —  |  — |

#### LEGAL field

<p>Bit i: destination index 32 + i is legal</p>

### TILE_RESYNC register

- Absolute Address: 0x2EC
- Base Offset: 0x2EC
- Size: 0x4

<p>Restores every legal cell's and control core's strap after a root failover (TILE_SPEC 11.10; SRC half). RAPIDS sends each a set credit packet: a cell its TILE_LAND_FLITS, a core its TILE_DESC_PER_CORE. Taken only while the tile is quiescent (tile_quiescent); a request made before then waits for it.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |    GO    |   w  | 0x0 |  — |
|31:1|   RSVD   |   r  | 0x0 |  — |

#### GO field

<p>Write 1 to request a resync</p>

#### RSVD field

<p>Reserved</p>

### TILE_STALL_CYCLES register

- Absolute Address: 0x2F0
- Base Offset: 0x2F0
- Size: 0x4

<p>Stalled-data checks (TILE_SPEC 11.9; SRC half, used by both): data that has not moved for this many cycles raises a MonBus error packet (PktTypeError, event RAPIDS_EVENT_STALL) -- sink SRAM data not written out, a source channel with reads outstanding and no R beat. The default is 10 us at 100 MHz. TILE_CREDITS = 1 only.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|  CYCLES  |  rw  |0x3E8|  — |

#### CYCLES field

<p>Threshold in cycles; 0 turns the checks off</p>

### TILE_STALLED register

- Absolute Address: 0x2F4
- Base Offset: 0x2F4
- Size: 0x4

<p>Per channel of this half: its data has stopped moving past TILE_STALL_CYCLES (the current episode; clears when the data moves or drains). TILE_CREDITS = 1 only.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|    CH    |   r  |  —  |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### CH field

<p>Bit n: channel n is stalled</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x300
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x300
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x304
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x304
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x308
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x308
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x30C
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x30C
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x310
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x310
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x314
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x314
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x318
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x318
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x31C
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x31C
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x320
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x320
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x324
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x324
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x328
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x328
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x32C
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x32C
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x330
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x330
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x334
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x334
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x338
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x338
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x33C
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x33C
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

### PERF_CH_SEL register

- Absolute Address: 0x35C
- Base Offset: 0x35C
- Size: 0x4

<p>Selects which channel's buckets appear in RD/WRMON_PERF_CH_*</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 3:0|  CH_SEL  |  rw  | 0x0 |  — |
|31:4|   RSVD   |   r  | 0x0 |  — |

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

### TILE_STRAPS register

- Absolute Address: 0x7FC
- Base Offset: 0x7FC
- Size: 0x4

<p>The straps this RAPIDS reserves toward it (TILE_SPEC 11.9), from
its build parameters, for the Hive to check against the cells'
and cores' straps. Both fields read 0 when TILE_CREDITS = 0 (no
straps). The same values in both halves.</p>

| Bits|  Identifier |Access|Reset|Name|
|-----|-------------|------|-----|----|
| 15:0|  LAND_FLITS |   r  |  —  |  — |
|31:16|DESC_PER_CORE|   r  |  —  |  — |

#### LAND_FLITS field

<p>TILE_LAND_FLITS: landing-space flits per cell, header included</p>

#### DESC_PER_CORE field

<p>TILE_DESC_PER_CORE: descriptor-intake entries per control core</p>

## MON register file

- Absolute Address: 0x800
- Base Offset: 0x800
- Size: 0x200

<p>AXI monitor + perf registers (relocatable block, instantiated at 0x1000)</p>

|Offset|        Identifier       |                            Name                           |
|------|-------------------------|-----------------------------------------------------------|
| 0x000|     MON_FIFO_STATUS     |                    Monitor FIFO Status                    |
| 0x004|      MON_FIFO_COUNT     |                     Monitor FIFO Count                    |
| 0x0C0|      DAXMON_ENABLE      |               Descriptor AXI Monitor Enable               |
| 0x0C4|      DAXMON_TIMEOUT     |               Descriptor AXI Monitor Timeout              |
| 0x0C8|  DAXMON_LATENCY_THRESH  |          Descriptor AXI Monitor Latency Threshold         |
| 0x0CC|     DAXMON_PKT_MASK     |             Descriptor AXI Monitor Packet Mask            |
| 0x0D0|      DAXMON_ERR_CFG     |        Descriptor AXI Monitor Error Select and Mask       |
| 0x0D4|       DAXMON_MASK1      |               Descriptor AXI Monitor Masks 1              |
| 0x0D8|       DAXMON_MASK2      |               Descriptor AXI Monitor Masks 2              |
| 0x0DC|       DAXMON_MASK3      |               Descriptor AXI Monitor Masks 3              |
| 0x0E0|       RDMON_ENABLE      |               Read Engine AXI Monitor Enable              |
| 0x0E4|      RDMON_TIMEOUT      |              Read Engine AXI Monitor Timeout              |
| 0x0E8|   RDMON_LATENCY_THRESH  |         Read Engine AXI Monitor Latency Threshold         |
| 0x0EC|      RDMON_PKT_MASK     |            Read Engine AXI Monitor Packet Mask            |
| 0x0F0|      RDMON_ERR_CFG      |       Read Engine AXI Monitor Error Select and Mask       |
| 0x0F4|       RDMON_MASK1       |              Read Engine AXI Monitor Masks 1              |
| 0x0F8|       RDMON_MASK2       |              Read Engine AXI Monitor Masks 2              |
| 0x0FC|       RDMON_MASK3       |              Read Engine AXI Monitor Masks 3              |
| 0x100|       WRMON_ENABLE      |              Write Engine AXI Monitor Enable              |
| 0x104|      WRMON_TIMEOUT      |              Write Engine AXI Monitor Timeout             |
| 0x108|   WRMON_LATENCY_THRESH  |         Write Engine AXI Monitor Latency Threshold        |
| 0x10C|      WRMON_PKT_MASK     |            Write Engine AXI Monitor Packet Mask           |
| 0x110|      WRMON_ERR_CFG      |       Write Engine AXI Monitor Error Select and Mask      |
| 0x114|       WRMON_MASK1       |              Write Engine AXI Monitor Masks 1             |
| 0x118|       WRMON_MASK2       |              Write Engine AXI Monitor Masks 2             |
| 0x11C|       WRMON_MASK3       |              Write Engine AXI Monitor Masks 3             |
| 0x150|     DAXMON_PERF_CTRL    |         Descriptor AXI Monitor Perf Window Control        |
| 0x154|    DAXMON_PERF_STATUS   |         Descriptor AXI Monitor Perf Window Status         |
| 0x158|DAXMON_PERF_WINDOW_CYCLES|         Descriptor AXI Monitor Perf Window Cycles         |
| 0x15C| DAXMON_PERF_PROD_CYCLES |       Descriptor AXI Monitor Perf Productive Cycles       |
| 0x160|  DAXMON_PERF_BP_CYCLES  |      Descriptor AXI Monitor Perf Backpressure Cycles      |
| 0x164| DAXMON_PERF_STARV_CYCLES|       Descriptor AXI Monitor Perf Starvation Cycles       |
| 0x168| DAXMON_PERF_IDLE_CYCLES |          Descriptor AXI Monitor Perf Idle Cycles          |
| 0x16C|  DAXMON_PERF_BEAT_COUNT |           Descriptor AXI Monitor Perf Beat Count          |
| 0x170|DAXMON_PERF_BYTE_COUNT_LO|         Descriptor AXI Monitor Perf Byte Count Low        |
| 0x174|DAXMON_PERF_BYTE_COUNT_HI|        Descriptor AXI Monitor Perf Byte Count High        |
| 0x178| DAXMON_PERF_BURST_COUNT |          Descriptor AXI Monitor Perf Burst Count          |
| 0x180|     RDMON_PERF_CTRL     |         Read Datapath Monitor Perf Window Control         |
| 0x184|    RDMON_PERF_STATUS    |          Read Datapath Monitor Perf Window Status         |
| 0x188| RDMON_PERF_WINDOW_CYCLES|          Read Datapath Monitor Perf Window Cycles         |
| 0x18C|  RDMON_PERF_PROD_CYCLES |        Read Datapath Monitor Perf Productive Cycles       |
| 0x190|   RDMON_PERF_BP_CYCLES  |       Read Datapath Monitor Perf Backpressure Cycles      |
| 0x194| RDMON_PERF_STARV_CYCLES |        Read Datapath Monitor Perf Starvation Cycles       |
| 0x198|  RDMON_PERF_IDLE_CYCLES |           Read Datapath Monitor Perf Idle Cycles          |
| 0x19C|  RDMON_PERF_BEAT_COUNT  |           Read Datapath Monitor Perf Beat Count           |
| 0x1A0| RDMON_PERF_BYTE_COUNT_LO|         Read Datapath Monitor Perf Byte Count Low         |
| 0x1A4| RDMON_PERF_BYTE_COUNT_HI|         Read Datapath Monitor Perf Byte Count High        |
| 0x1A8|  RDMON_PERF_BURST_COUNT |           Read Datapath Monitor Perf Burst Count          |
| 0x1B0|     WRMON_PERF_CTRL     |         Write Datapath Monitor Perf Window Control        |
| 0x1B4|    WRMON_PERF_STATUS    |         Write Datapath Monitor Perf Window Status         |
| 0x1B8| WRMON_PERF_WINDOW_CYCLES|         Write Datapath Monitor Perf Window Cycles         |
| 0x1BC|  WRMON_PERF_PROD_CYCLES |       Write Datapath Monitor Perf Productive Cycles       |
| 0x1C0|   WRMON_PERF_BP_CYCLES  |      Write Datapath Monitor Perf Backpressure Cycles      |
| 0x1C4| WRMON_PERF_STARV_CYCLES |       Write Datapath Monitor Perf Starvation Cycles       |
| 0x1C8|  WRMON_PERF_IDLE_CYCLES |          Write Datapath Monitor Perf Idle Cycles          |
| 0x1CC|  WRMON_PERF_BEAT_COUNT  |           Write Datapath Monitor Perf Beat Count          |
| 0x1D0| WRMON_PERF_BYTE_COUNT_LO|         Write Datapath Monitor Perf Byte Count Low        |
| 0x1D4| WRMON_PERF_BYTE_COUNT_HI|        Write Datapath Monitor Perf Byte Count High        |
| 0x1D8|  WRMON_PERF_BURST_COUNT |          Write Datapath Monitor Perf Burst Count          |
| 0x1E0|  RDMON_PERF_CH_PROD_BP  |     Read Datapath Per-Channel Productive/Backpressure     |
| 0x1E4| RDMON_PERF_CH_STARV_IDLE|         Read Datapath Per-Channel Starvation/Idle         |
| 0x1E8|  WRMON_PERF_CH_PROD_BP  |     Write Datapath Per-Channel Productive/Backpressure    |
| 0x1EC| WRMON_PERF_CH_STARV_IDLE|         Write Datapath Per-Channel Starvation/Idle        |
| 0x1F0|  RDMON_PERF_CH_OVERFLOW |        Read Datapath Per-Channel Overflow Stickies        |
| 0x1F4|  WRMON_PERF_CH_OVERFLOW |        Write Datapath Per-Channel Overflow Stickies       |
| 0x1F8|RDMON_PERF_CH_OVERFLOW_HI| Read Datapath Per-Channel Overflow Stickies, channels 8-15|
| 0x1FC|WRMON_PERF_CH_OVERFLOW_HI|Write Datapath Per-Channel Overflow Stickies, channels 8-15|

### MON_FIFO_STATUS register

- Absolute Address: 0x800
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

- Absolute Address: 0x804
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

- Absolute Address: 0x8C0
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

- Absolute Address: 0x8C4
- Base Offset: 0xC4
- Size: 0x4

<p>Descriptor AXI monitor timeout threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x2710|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0]</p>

### DAXMON_LATENCY_THRESH register

- Absolute Address: 0x8C8
- Base Offset: 0xC8
- Size: 0x4

<p>Descriptor AXI monitor latency threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|LATENCY_THRESH|  rw  |0x1388|  — |

#### LATENCY_THRESH field

<p>Latency threshold cycles [31:0]</p>

### DAXMON_PKT_MASK register

- Absolute Address: 0x8CC
- Base Offset: 0xCC
- Size: 0x4

<p>Descriptor AXI monitor packet type filtering (16-bit mask)</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0| PKT_MASK |  rw  |0xFFFF|  — |
|31:16|   RSVD   |   r  |  0x0 |  — |

#### PKT_MASK field

<p>Packet type mask [15:0] - bit[type] = 1 MASKS (drops) that packet type, at the monitor-lite and again at the monbus group. Reset = all masked: the host clears the bits of the classes it wants to see (rapids BUG-008 corrected this description; the polarity and the reset are as intended)</p>

#### RSVD field

<p>Reserved</p>

### DAXMON_ERR_CFG register

- Absolute Address: 0x8D0
- Base Offset: 0xD0
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

- Absolute Address: 0x8D4
- Base Offset: 0xD4
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

- Absolute Address: 0x8D8
- Base Offset: 0xD8
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

- Absolute Address: 0x8DC
- Base Offset: 0xDC
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

- Absolute Address: 0x8E0
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

- Absolute Address: 0x8E4
- Base Offset: 0xE4
- Size: 0x4

<p>Read engine AXI monitor timeout threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x2710|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0]</p>

### RDMON_LATENCY_THRESH register

- Absolute Address: 0x8E8
- Base Offset: 0xE8
- Size: 0x4

<p>Read engine AXI monitor latency threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|LATENCY_THRESH|  rw  |0x1388|  — |

#### LATENCY_THRESH field

<p>Latency threshold cycles [31:0]</p>

### RDMON_PKT_MASK register

- Absolute Address: 0x8EC
- Base Offset: 0xEC
- Size: 0x4

<p>Read engine AXI monitor packet type filtering (16-bit mask)</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0| PKT_MASK |  rw  |0xFFFF|  — |
|31:16|   RSVD   |   r  |  0x0 |  — |

#### PKT_MASK field

<p>Packet type mask [15:0] - bit[type] = 1 MASKS (drops) that packet type, at the monitor-lite and again at the monbus group. Reset = all masked: the host clears the bits of the classes it wants to see (rapids BUG-008 corrected this description; the polarity and the reset are as intended)</p>

#### RSVD field

<p>Reserved</p>

### RDMON_ERR_CFG register

- Absolute Address: 0x8F0
- Base Offset: 0xF0
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

- Absolute Address: 0x8F4
- Base Offset: 0xF4
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

- Absolute Address: 0x8F8
- Base Offset: 0xF8
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

- Absolute Address: 0x8FC
- Base Offset: 0xFC
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

- Absolute Address: 0x900
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
|31:6|    RSVD   |   r  | 0x0 |  — |

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

#### RSVD field

<p>Reserved</p>

### WRMON_TIMEOUT register

- Absolute Address: 0x904
- Base Offset: 0x104
- Size: 0x4

<p>Write engine AXI monitor timeout threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x2710|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0]</p>

### WRMON_LATENCY_THRESH register

- Absolute Address: 0x908
- Base Offset: 0x108
- Size: 0x4

<p>Write engine AXI monitor latency threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|LATENCY_THRESH|  rw  |0x1388|  — |

#### LATENCY_THRESH field

<p>Latency threshold cycles [31:0]</p>

### WRMON_PKT_MASK register

- Absolute Address: 0x90C
- Base Offset: 0x10C
- Size: 0x4

<p>Write engine AXI monitor packet type filtering (16-bit mask)</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0| PKT_MASK |  rw  |0xFFFF|  — |
|31:16|   RSVD   |   r  |  0x0 |  — |

#### PKT_MASK field

<p>Packet type mask [15:0] - bit[type] = 1 MASKS (drops) that packet type, at the monitor-lite and again at the monbus group. Reset = all masked: the host clears the bits of the classes it wants to see (rapids BUG-008 corrected this description; the polarity and the reset are as intended)</p>

#### RSVD field

<p>Reserved</p>

### WRMON_ERR_CFG register

- Absolute Address: 0x910
- Base Offset: 0x110
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

- Absolute Address: 0x914
- Base Offset: 0x114
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

- Absolute Address: 0x918
- Base Offset: 0x118
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

- Absolute Address: 0x91C
- Base Offset: 0x11C
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

### DAXMON_PERF_CTRL register

- Absolute Address: 0x950
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

- Absolute Address: 0x954
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

- Absolute Address: 0x958
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

- Absolute Address: 0x95C
- Base Offset: 0x15C
- Size: 0x4

<p>Cycles with R data valid &amp;&amp; ready (data delivered)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Productive cycles [31:0]</p>

### DAXMON_PERF_BP_CYCLES register

- Absolute Address: 0x960
- Base Offset: 0x160
- Size: 0x4

<p>Cycles with R data valid &amp;&amp; !ready (back-pressure)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Backpressure cycles [31:0]</p>

### DAXMON_PERF_STARV_CYCLES register

- Absolute Address: 0x964
- Base Offset: 0x164
- Size: 0x4

<p>Cycles with !R data valid &amp;&amp; ready (starvation)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Starvation cycles [31:0]</p>

### DAXMON_PERF_IDLE_CYCLES register

- Absolute Address: 0x968
- Base Offset: 0x168
- Size: 0x4

<p>Cycles with !R data valid &amp;&amp; !ready (idle)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Idle cycles [31:0]</p>

### DAXMON_PERF_BEAT_COUNT register

- Absolute Address: 0x96C
- Base Offset: 0x16C
- Size: 0x4

<p>R beats transferred in window (= productive cycles)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Beat count [31:0]</p>

### DAXMON_PERF_BYTE_COUNT_LO register

- Absolute Address: 0x970
- Base Offset: 0x170
- Size: 0x4

<p>Bytes transferred in window (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [31:0]</p>

### DAXMON_PERF_BYTE_COUNT_HI register

- Absolute Address: 0x974
- Base Offset: 0x174
- Size: 0x4

<p>Bytes transferred in window (upper 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [63:32]</p>

### DAXMON_PERF_BURST_COUNT register

- Absolute Address: 0x978
- Base Offset: 0x178
- Size: 0x4

<p>AR handshakes (bursts issued) in window</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Burst count [31:0]</p>

### RDMON_PERF_CTRL register

- Absolute Address: 0x980
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

- Absolute Address: 0x984
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

- Absolute Address: 0x988
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

- Absolute Address: 0x98C
- Base Offset: 0x18C
- Size: 0x4

<p>Cycles with R data valid &amp;&amp; ready (data delivered)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Productive cycles [31:0]</p>

### RDMON_PERF_BP_CYCLES register

- Absolute Address: 0x990
- Base Offset: 0x190
- Size: 0x4

<p>Cycles with R data valid &amp;&amp; !ready (back-pressure)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Backpressure cycles [31:0]</p>

### RDMON_PERF_STARV_CYCLES register

- Absolute Address: 0x994
- Base Offset: 0x194
- Size: 0x4

<p>Cycles with !R data valid &amp;&amp; ready (starvation)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Starvation cycles [31:0]</p>

### RDMON_PERF_IDLE_CYCLES register

- Absolute Address: 0x998
- Base Offset: 0x198
- Size: 0x4

<p>Cycles with !R data valid &amp;&amp; !ready (idle)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Idle cycles [31:0]</p>

### RDMON_PERF_BEAT_COUNT register

- Absolute Address: 0x99C
- Base Offset: 0x19C
- Size: 0x4

<p>R beats transferred in window (= productive cycles)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Beat count [31:0]</p>

### RDMON_PERF_BYTE_COUNT_LO register

- Absolute Address: 0x9A0
- Base Offset: 0x1A0
- Size: 0x4

<p>Bytes transferred in window (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [31:0]</p>

### RDMON_PERF_BYTE_COUNT_HI register

- Absolute Address: 0x9A4
- Base Offset: 0x1A4
- Size: 0x4

<p>Bytes transferred in window (upper 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [63:32]</p>

### RDMON_PERF_BURST_COUNT register

- Absolute Address: 0x9A8
- Base Offset: 0x1A8
- Size: 0x4

<p>AR handshakes (bursts issued) in window</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Burst count [31:0]</p>

### WRMON_PERF_CTRL register

- Absolute Address: 0x9B0
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

- Absolute Address: 0x9B4
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

- Absolute Address: 0x9B8
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

- Absolute Address: 0x9BC
- Base Offset: 0x1BC
- Size: 0x4

<p>Cycles with W data valid &amp;&amp; ready (beat delivered)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Productive cycles [31:0]</p>

### WRMON_PERF_BP_CYCLES register

- Absolute Address: 0x9C0
- Base Offset: 0x1C0
- Size: 0x4

<p>Cycles with W data valid &amp;&amp; !ready (back-pressure)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Backpressure cycles [31:0]</p>

### WRMON_PERF_STARV_CYCLES register

- Absolute Address: 0x9C4
- Base Offset: 0x1C4
- Size: 0x4

<p>Cycles with !W data valid &amp;&amp; ready (starvation)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Starvation cycles [31:0]</p>

### WRMON_PERF_IDLE_CYCLES register

- Absolute Address: 0x9C8
- Base Offset: 0x1C8
- Size: 0x4

<p>Cycles with !W data valid &amp;&amp; !ready (idle)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Idle cycles [31:0]</p>

### WRMON_PERF_BEAT_COUNT register

- Absolute Address: 0x9CC
- Base Offset: 0x1CC
- Size: 0x4

<p>W beats transferred in window (= productive cycles)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Beat count [31:0]</p>

### WRMON_PERF_BYTE_COUNT_LO register

- Absolute Address: 0x9D0
- Base Offset: 0x1D0
- Size: 0x4

<p>Bytes transferred in window (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [31:0]</p>

### WRMON_PERF_BYTE_COUNT_HI register

- Absolute Address: 0x9D4
- Base Offset: 0x1D4
- Size: 0x4

<p>Bytes transferred in window (upper 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [63:32]</p>

### WRMON_PERF_BURST_COUNT register

- Absolute Address: 0x9D8
- Base Offset: 0x1D8
- Size: 0x4

<p>AW handshakes (bursts issued) in window</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Burst count [31:0]</p>

### RDMON_PERF_CH_PROD_BP register

- Absolute Address: 0x9E0
- Base Offset: 0x1E0
- Size: 0x4

<p>Selected channel: {backpressure[31:16], productive[15:0]} (16-bit each)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>{bp[15:0], prod[15:0]} for PERF_CH_SEL channel</p>

### RDMON_PERF_CH_STARV_IDLE register

- Absolute Address: 0x9E4
- Base Offset: 0x1E4
- Size: 0x4

<p>Selected channel: {idle[31:16], starvation[15:0]} (16-bit each)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>{idle[15:0], starv[15:0]} for PERF_CH_SEL channel</p>

### WRMON_PERF_CH_PROD_BP register

- Absolute Address: 0x9E8
- Base Offset: 0x1E8
- Size: 0x4

<p>Selected channel: {backpressure[31:16], productive[15:0]} (16-bit each)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>{bp[15:0], prod[15:0]} for PERF_CH_SEL channel</p>

### WRMON_PERF_CH_STARV_IDLE register

- Absolute Address: 0x9EC
- Base Offset: 0x1EC
- Size: 0x4

<p>Selected channel: {idle[31:16], starvation[15:0]} (16-bit each)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>{idle[15:0], starv[15:0]} for PERF_CH_SEL channel</p>

### RDMON_PERF_CH_OVERFLOW register

- Absolute Address: 0x9F0
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

- Absolute Address: 0x9F4
- Base Offset: 0x1F4
- Size: 0x4

<p>All channels, {prod,bp,starv,idle} sticky overflow per channel.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Per-channel overflow mask (NUM_CHANNELS*4 bits)</p>

### RDMON_PERF_CH_OVERFLOW_HI register

- Absolute Address: 0x9F8
- Base Offset: 0x1F8
- Size: 0x4

<p>Channels 8..15 of RDMON_PERF_CH_OVERFLOW (4 bits/channel, channel 8 in the low nibble).</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Per-channel overflow mask, channels 8..15</p>

### WRMON_PERF_CH_OVERFLOW_HI register

- Absolute Address: 0x9FC
- Base Offset: 0x1FC
- Size: 0x4

<p>Channels 8..15 of WRMON_PERF_CH_OVERFLOW (4 bits/channel, channel 8 in the low nibble).</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Per-channel overflow mask, channels 8..15</p>

## SNK register file

- Absolute Address: 0x1000
- Base Offset: 0x1000
- Size: 0xA00

<p>Config/status + monitors for one RAPIDS engine (source or sink)</p>

|Offset|     Identifier     |                 Name                 |
|------|--------------------|--------------------------------------|
| 0x000|  CH0_DESC_ADDR_LOW |           Ch0 desc addr LOW          |
| 0x004| CH0_DESC_ADDR_HIGH |          Ch0 desc addr HIGH          |
| 0x008|  CH1_DESC_ADDR_LOW |           Ch1 desc addr LOW          |
| 0x00C| CH1_DESC_ADDR_HIGH |          Ch1 desc addr HIGH          |
| 0x010|  CH2_DESC_ADDR_LOW |           Ch2 desc addr LOW          |
| 0x014| CH2_DESC_ADDR_HIGH |          Ch2 desc addr HIGH          |
| 0x018|  CH3_DESC_ADDR_LOW |           Ch3 desc addr LOW          |
| 0x01C| CH3_DESC_ADDR_HIGH |          Ch3 desc addr HIGH          |
| 0x020|  CH4_DESC_ADDR_LOW |           Ch4 desc addr LOW          |
| 0x024| CH4_DESC_ADDR_HIGH |          Ch4 desc addr HIGH          |
| 0x028|  CH5_DESC_ADDR_LOW |           Ch5 desc addr LOW          |
| 0x02C| CH5_DESC_ADDR_HIGH |          Ch5 desc addr HIGH          |
| 0x030|  CH6_DESC_ADDR_LOW |           Ch6 desc addr LOW          |
| 0x034| CH6_DESC_ADDR_HIGH |          Ch6 desc addr HIGH          |
| 0x038|  CH7_DESC_ADDR_LOW |           Ch7 desc addr LOW          |
| 0x03C| CH7_DESC_ADDR_HIGH |          Ch7 desc addr HIGH          |
| 0x040|  CH8_DESC_ADDR_LOW |           Ch8 desc addr LOW          |
| 0x044| CH8_DESC_ADDR_HIGH |          Ch8 desc addr HIGH          |
| 0x048|  CH9_DESC_ADDR_LOW |           Ch9 desc addr LOW          |
| 0x04C| CH9_DESC_ADDR_HIGH |          Ch9 desc addr HIGH          |
| 0x050| CH10_DESC_ADDR_LOW |          Ch10 desc addr LOW          |
| 0x054| CH10_DESC_ADDR_HIGH|          Ch10 desc addr HIGH         |
| 0x058| CH11_DESC_ADDR_LOW |          Ch11 desc addr LOW          |
| 0x05C| CH11_DESC_ADDR_HIGH|          Ch11 desc addr HIGH         |
| 0x060| CH12_DESC_ADDR_LOW |          Ch12 desc addr LOW          |
| 0x064| CH12_DESC_ADDR_HIGH|          Ch12 desc addr HIGH         |
| 0x068| CH13_DESC_ADDR_LOW |          Ch13 desc addr LOW          |
| 0x06C| CH13_DESC_ADDR_HIGH|          Ch13 desc addr HIGH         |
| 0x070| CH14_DESC_ADDR_LOW |          Ch14 desc addr LOW          |
| 0x074| CH14_DESC_ADDR_HIGH|          Ch14 desc addr HIGH         |
| 0x078| CH15_DESC_ADDR_LOW |          Ch15 desc addr LOW          |
| 0x07C| CH15_DESC_ADDR_HIGH|          Ch15 desc addr HIGH         |
| 0x080|     KICK_ENABLE    |              Kick enable             |
| 0x100|     GLOBAL_CTRL    |        Global Control Register       |
| 0x104|    GLOBAL_STATUS   |        Global Status Register        |
| 0x108|       VERSION      |           Version Register           |
| 0x120|   CHANNEL_ENABLE   |        Channel Enable Register       |
| 0x124|    CHANNEL_RESET   |        Channel Reset Register        |
| 0x140|    CHANNEL_IDLE    |          Channel Idle Status         |
| 0x144|  DESC_ENGINE_IDLE  |     Descriptor Engine Idle Status    |
| 0x148|   SCHEDULER_IDLE   |         Scheduler Idle Status        |
| 0x170|     SCHED_ERROR    |        Scheduler Error Status        |
| 0x174|   AXI_RD_COMPLETE  |   AXI Read Engine Completion Status  |
| 0x178|   AXI_WR_COMPLETE  |  AXI Write Engine Completion Status  |
| 0x180|     CH_STATE[0]    |      Per-Channel State Registers     |
| 0x184|     CH_STATE[1]    |      Per-Channel State Registers     |
| 0x188|     CH_STATE[2]    |      Per-Channel State Registers     |
| 0x18C|     CH_STATE[3]    |      Per-Channel State Registers     |
| 0x190|     CH_STATE[4]    |      Per-Channel State Registers     |
| 0x194|     CH_STATE[5]    |      Per-Channel State Registers     |
| 0x198|     CH_STATE[6]    |      Per-Channel State Registers     |
| 0x19C|     CH_STATE[7]    |      Per-Channel State Registers     |
| 0x1A0|     CH_STATE[8]    |      Per-Channel State Registers     |
| 0x1A4|     CH_STATE[9]    |      Per-Channel State Registers     |
| 0x1A8|    CH_STATE[10]    |      Per-Channel State Registers     |
| 0x1AC|    CH_STATE[11]    |      Per-Channel State Registers     |
| 0x1B0|    CH_STATE[12]    |      Per-Channel State Registers     |
| 0x1B4|    CH_STATE[13]    |      Per-Channel State Registers     |
| 0x1B8|    CH_STATE[14]    |      Per-Channel State Registers     |
| 0x1BC|    CH_STATE[15]    |      Per-Channel State Registers     |
| 0x200|SCHED_TIMEOUT_CYCLES|       Scheduler Timeout Cycles       |
| 0x204|    SCHED_CONFIG    |        Scheduler Configuration       |
| 0x208| SCHED_TIMEOUT_LIMIT|  Scheduler Timeout Escalation Limit  |
| 0x220|   DESCENG_CONFIG   |    Descriptor Engine Configuration   |
| 0x224| DESCENG_ADDR0_BASE |    Descriptor Address Range 0 Base   |
| 0x228| DESCENG_ADDR0_LIMIT|   Descriptor Address Range 0 Limit   |
| 0x22C| DESCENG_ADDR1_BASE |    Descriptor Address Range 1 Base   |
| 0x230| DESCENG_ADDR1_LIMIT|   Descriptor Address Range 1 Limit   |
| 0x240|     CTRL_CONFIG    |     Control Engine Configuration     |
| 0x2A0|   AXI_XFER_CONFIG  |      AXI Transfer Configuration      |
| 0x2B0|     PERF_CONFIG    |  Performance Profiler Configuration  |
| 0x2C0|      OBS_CTRL      |        Observation Mux Control       |
| 0x2C4|      OBS_FLAGS     |           Observation Flags          |
| 0x2C8|      OBS_DATA0     |          Observation Data 0          |
| 0x2CC|      OBS_DATA1     |          Observation Data 1          |
| 0x2D0|     TILE_STATUS    |          Tile Header Status          |
| 0x2D4|  TILE_DESC_DROPPED |         Cell Descriptor Drops        |
| 0x2D8|     TILE_COUNTS    |          Tile Packet Counts          |
| 0x2DC|   TILE_ADV_WINDOW  |       Tile Advertisement Window      |
| 0x2E0| TILE_LEGAL_DEST_LO |     Tile Legal Destinations, Low     |
| 0x2E4| TILE_CREDIT_STATUS |          Tile Credit Status          |
| 0x2E8| TILE_LEGAL_DEST_HI |     Tile Legal Destinations, High    |
| 0x2EC|     TILE_RESYNC    |          Tile Credit Resync          |
| 0x2F0|  TILE_STALL_CYCLES |      Tile Stalled-Data Threshold     |
| 0x2F4|    TILE_STALLED    |         Tile Stalled Channels        |
| 0x300|    CH_SCRATCH[0]   |          Per-Channel Scratch         |
| 0x304|    CH_SCRATCH[1]   |          Per-Channel Scratch         |
| 0x308|    CH_SCRATCH[2]   |          Per-Channel Scratch         |
| 0x30C|    CH_SCRATCH[3]   |          Per-Channel Scratch         |
| 0x310|    CH_SCRATCH[4]   |          Per-Channel Scratch         |
| 0x314|    CH_SCRATCH[5]   |          Per-Channel Scratch         |
| 0x318|    CH_SCRATCH[6]   |          Per-Channel Scratch         |
| 0x31C|    CH_SCRATCH[7]   |          Per-Channel Scratch         |
| 0x320|    CH_SCRATCH[8]   |          Per-Channel Scratch         |
| 0x324|    CH_SCRATCH[9]   |          Per-Channel Scratch         |
| 0x328|   CH_SCRATCH[10]   |          Per-Channel Scratch         |
| 0x32C|   CH_SCRATCH[11]   |          Per-Channel Scratch         |
| 0x330|   CH_SCRATCH[12]   |          Per-Channel Scratch         |
| 0x334|   CH_SCRATCH[13]   |          Per-Channel Scratch         |
| 0x338|   CH_SCRATCH[14]   |          Per-Channel Scratch         |
| 0x33C|   CH_SCRATCH[15]   |          Per-Channel Scratch         |
| 0x35C|     PERF_CH_SEL    |Per-Channel Perf Bucket Readout Select|
| 0x378|      HIST_SEL      |   Latency Histogram Readout Select   |
| 0x37C|      HIST_DATA     |      Latency Histogram Bin Count     |
| 0x380|     HIST_TOTAL     |    Latency Histogram Metric Total    |
| 0x7FC|     TILE_STRAPS    |              Tile Straps             |
| 0x800|         MON        |       RAPIDS Monitor Registers       |

### CH0_DESC_ADDR_LOW register

- Absolute Address: 0x1000
- Base Offset: 0x0
- Size: 0x4

<p>Ch0 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH0_DESC_ADDR_HIGH register

- Absolute Address: 0x1004
- Base Offset: 0x4
- Size: 0x4

<p>Ch0 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH1_DESC_ADDR_LOW register

- Absolute Address: 0x1008
- Base Offset: 0x8
- Size: 0x4

<p>Ch1 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH1_DESC_ADDR_HIGH register

- Absolute Address: 0x100C
- Base Offset: 0xC
- Size: 0x4

<p>Ch1 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH2_DESC_ADDR_LOW register

- Absolute Address: 0x1010
- Base Offset: 0x10
- Size: 0x4

<p>Ch2 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH2_DESC_ADDR_HIGH register

- Absolute Address: 0x1014
- Base Offset: 0x14
- Size: 0x4

<p>Ch2 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH3_DESC_ADDR_LOW register

- Absolute Address: 0x1018
- Base Offset: 0x18
- Size: 0x4

<p>Ch3 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH3_DESC_ADDR_HIGH register

- Absolute Address: 0x101C
- Base Offset: 0x1C
- Size: 0x4

<p>Ch3 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH4_DESC_ADDR_LOW register

- Absolute Address: 0x1020
- Base Offset: 0x20
- Size: 0x4

<p>Ch4 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH4_DESC_ADDR_HIGH register

- Absolute Address: 0x1024
- Base Offset: 0x24
- Size: 0x4

<p>Ch4 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH5_DESC_ADDR_LOW register

- Absolute Address: 0x1028
- Base Offset: 0x28
- Size: 0x4

<p>Ch5 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH5_DESC_ADDR_HIGH register

- Absolute Address: 0x102C
- Base Offset: 0x2C
- Size: 0x4

<p>Ch5 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH6_DESC_ADDR_LOW register

- Absolute Address: 0x1030
- Base Offset: 0x30
- Size: 0x4

<p>Ch6 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH6_DESC_ADDR_HIGH register

- Absolute Address: 0x1034
- Base Offset: 0x34
- Size: 0x4

<p>Ch6 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH7_DESC_ADDR_LOW register

- Absolute Address: 0x1038
- Base Offset: 0x38
- Size: 0x4

<p>Ch7 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH7_DESC_ADDR_HIGH register

- Absolute Address: 0x103C
- Base Offset: 0x3C
- Size: 0x4

<p>Ch7 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH8_DESC_ADDR_LOW register

- Absolute Address: 0x1040
- Base Offset: 0x40
- Size: 0x4

<p>Ch8 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH8_DESC_ADDR_HIGH register

- Absolute Address: 0x1044
- Base Offset: 0x44
- Size: 0x4

<p>Ch8 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH9_DESC_ADDR_LOW register

- Absolute Address: 0x1048
- Base Offset: 0x48
- Size: 0x4

<p>Ch9 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH9_DESC_ADDR_HIGH register

- Absolute Address: 0x104C
- Base Offset: 0x4C
- Size: 0x4

<p>Ch9 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH10_DESC_ADDR_LOW register

- Absolute Address: 0x1050
- Base Offset: 0x50
- Size: 0x4

<p>Ch10 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH10_DESC_ADDR_HIGH register

- Absolute Address: 0x1054
- Base Offset: 0x54
- Size: 0x4

<p>Ch10 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH11_DESC_ADDR_LOW register

- Absolute Address: 0x1058
- Base Offset: 0x58
- Size: 0x4

<p>Ch11 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH11_DESC_ADDR_HIGH register

- Absolute Address: 0x105C
- Base Offset: 0x5C
- Size: 0x4

<p>Ch11 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH12_DESC_ADDR_LOW register

- Absolute Address: 0x1060
- Base Offset: 0x60
- Size: 0x4

<p>Ch12 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH12_DESC_ADDR_HIGH register

- Absolute Address: 0x1064
- Base Offset: 0x64
- Size: 0x4

<p>Ch12 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH13_DESC_ADDR_LOW register

- Absolute Address: 0x1068
- Base Offset: 0x68
- Size: 0x4

<p>Ch13 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH13_DESC_ADDR_HIGH register

- Absolute Address: 0x106C
- Base Offset: 0x6C
- Size: 0x4

<p>Ch13 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH14_DESC_ADDR_LOW register

- Absolute Address: 0x1070
- Base Offset: 0x70
- Size: 0x4

<p>Ch14 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH14_DESC_ADDR_HIGH register

- Absolute Address: 0x1074
- Base Offset: 0x74
- Size: 0x4

<p>Ch14 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### CH15_DESC_ADDR_LOW register

- Absolute Address: 0x1078
- Base Offset: 0x78
- Size: 0x4

<p>Ch15 descriptor address [31:0] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier |Access|Reset|Name|
|----|-------------|------|-----|----|
|31:0|DESC_ADDR_LOW|  rw  | 0x0 |  — |

### CH15_DESC_ADDR_HIGH register

- Absolute Address: 0x107C
- Base Offset: 0x7C
- Size: 0x4

<p>Ch15 descriptor address [63:32] (staged; launch via KICK_ENABLE)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|DESC_ADDR_HIGH|  rw  | 0x0 |  — |

### KICK_ENABLE register

- Absolute Address: 0x1080
- Base Offset: 0x80
- Size: 0x4

<p>Write 1 to bit[ch] to launch that channel from its staged CHx_DESC_ADDR pair</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
|  0  |   KICK0  |   w  | 0x0 |  — |
|  1  |   KICK1  |   w  | 0x0 |  — |
|  2  |   KICK2  |   w  | 0x0 |  — |
|  3  |   KICK3  |   w  | 0x0 |  — |
|  4  |   KICK4  |   w  | 0x0 |  — |
|  5  |   KICK5  |   w  | 0x0 |  — |
|  6  |   KICK6  |   w  | 0x0 |  — |
|  7  |   KICK7  |   w  | 0x0 |  — |
|  8  |   KICK8  |   w  | 0x0 |  — |
|  9  |   KICK9  |   w  | 0x0 |  — |
|  10 |  KICK10  |   w  | 0x0 |  — |
|  11 |  KICK11  |   w  | 0x0 |  — |
|  12 |  KICK12  |   w  | 0x0 |  — |
|  13 |  KICK13  |   w  | 0x0 |  — |
|  14 |  KICK14  |   w  | 0x0 |  — |
|  15 |  KICK15  |   w  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### RSVD field

<p>Reserved</p>

### GLOBAL_CTRL register

- Absolute Address: 0x1100
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

- Absolute Address: 0x1104
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

- Absolute Address: 0x1108
- Base Offset: 0x108
- Size: 0x4

<p>STREAM version and configuration information</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 7:0 |    MINOR   |   r  | 0x5A|  — |
| 15:8|    MAJOR   |   r  | 0x0 |  — |
|23:16|NUM_CHANNELS|   r  | 0x10|  — |
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

- Absolute Address: 0x1120
- Base Offset: 0x120
- Size: 0x4

<p>Per-channel enable bits (one bit per channel)</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|   CH_EN  |  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### CH_EN field

<p>Channel enable bits [15:0] - 1=enabled, 0=disabled</p>

#### RSVD field

<p>Reserved</p>

### CHANNEL_RESET register

- Absolute Address: 0x1124
- Base Offset: 0x124
- Size: 0x4

<p>Per-channel reset bits (one bit per channel, self-clearing)</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|  CH_RST  |  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### CH_RST field

<p>Channel reset bits [15:0] - write 1 to reset channel</p>

#### RSVD field

<p>Reserved</p>

### CHANNEL_IDLE register

- Absolute Address: 0x1140
- Base Offset: 0x140
- Size: 0x4

<p>Per-channel idle status (one bit per channel)</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|  CH_IDLE |   r  |  —  |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### CH_IDLE field

<p>Channel idle bits [15:0] - 1=idle, 0=active</p>

#### RSVD field

<p>Reserved</p>

### DESC_ENGINE_IDLE register

- Absolute Address: 0x1144
- Base Offset: 0x144
- Size: 0x4

<p>Per-channel descriptor engine idle status</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| DESC_IDLE|   r  |  —  |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### DESC_IDLE field

<p>Descriptor engine idle bits [15:0] - 1=idle, 0=active</p>

#### RSVD field

<p>Reserved</p>

### SCHEDULER_IDLE register

- Absolute Address: 0x1148
- Base Offset: 0x148
- Size: 0x4

<p>Per-channel scheduler idle status</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|SCHED_IDLE|   r  |  —  |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### SCHED_IDLE field

<p>Scheduler idle bits [15:0] - 1=idle, 0=active</p>

#### RSVD field

<p>Reserved</p>

### SCHED_ERROR register

- Absolute Address: 0x1170
- Base Offset: 0x170
- Size: 0x4

<p>Per-channel scheduler error flags</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| SCHED_ERR|   r  |  —  |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### SCHED_ERR field

<p>Scheduler error bits [15:0] - 1=error detected, 0=no error</p>

#### RSVD field

<p>Reserved</p>

### AXI_RD_COMPLETE register

- Absolute Address: 0x1174
- Base Offset: 0x174
- Size: 0x4

<p>Per-channel read engine all_complete flags</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 15:0|RD_COMPLETE|   r  |  —  |  — |
|31:16|    RSVD   |   r  | 0x0 |  — |

#### RD_COMPLETE field

<p>Read completion bits [15:0] - 1=all reads complete, 0=reads pending</p>

#### RSVD field

<p>Reserved</p>

### AXI_WR_COMPLETE register

- Absolute Address: 0x1178
- Base Offset: 0x178
- Size: 0x4

<p>Per-channel write engine all_complete flags</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 15:0|WR_COMPLETE|   r  |  —  |  — |
|31:16|    RSVD   |   r  | 0x0 |  — |

#### WR_COMPLETE field

<p>Write completion bits [15:0] - 1=all writes complete, 0=writes pending</p>

#### RSVD field

<p>Reserved</p>

## CH_STATE register file

- Absolute Address: 0x1180
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1180
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

- Absolute Address: 0x1184
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1184
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

- Absolute Address: 0x1188
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1188
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

- Absolute Address: 0x118C
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x118C
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

- Absolute Address: 0x1190
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1190
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

- Absolute Address: 0x1194
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1194
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

- Absolute Address: 0x1198
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x1198
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

- Absolute Address: 0x119C
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x119C
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

- Absolute Address: 0x11A0
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x11A0
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

- Absolute Address: 0x11A4
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x11A4
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

- Absolute Address: 0x11A8
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x11A8
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

- Absolute Address: 0x11AC
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x11AC
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

- Absolute Address: 0x11B0
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x11B0
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

- Absolute Address: 0x11B4
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x11B4
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

- Absolute Address: 0x11B8
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x11B8
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

- Absolute Address: 0x11BC
- Base Offset: 0x180
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Detailed state for individual channel</p>

|Offset|Identifier|     Name    |
|------|----------|-------------|
|  0x0 |   STATE  |Channel State|

### STATE register

- Absolute Address: 0x11BC
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

### SCHED_TIMEOUT_CYCLES register

- Absolute Address: 0x1200
- Base Offset: 0x200
- Size: 0x4

<p>Timeout threshold in clock cycles (global for all channels)</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x3E8|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0] - number of cycles before timeout</p>

### SCHED_CONFIG register

- Absolute Address: 0x1204
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

<p>Completion enable. 1 = the scheduler and the descriptor engine report CORE Completion packets (descriptor loaded, descriptor/chain complete) on the monitor bus; 0 = those packets are dropped at the scheduler group, and the emitters are acknowledged so nothing stalls. Error packets are not gated by this bit (or by ERR_EN).</p>

#### PERF_EN field

<p>Performance enable - enable performance monitoring</p>

#### RSVD field

<p>Reserved</p>

### SCHED_TIMEOUT_LIMIT register

- Absolute Address: 0x1208
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

- Absolute Address: 0x1220
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

- Absolute Address: 0x1224
- Base Offset: 0x224
- Size: 0x4

<p>Base address for descriptor address range 0 (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|ADDR0_BASE|  rw  | 0x0 |  — |

#### ADDR0_BASE field

<p>Address range 0 base [31:0]</p>

### DESCENG_ADDR0_LIMIT register

- Absolute Address: 0x1228
- Base Offset: 0x228
- Size: 0x4

<p>Limit address for descriptor address range 0 (lower 32 bits)</p>

|Bits| Identifier|Access|   Reset  |Name|
|----|-----------|------|----------|----|
|31:0|ADDR0_LIMIT|  rw  |0xFFFFFFFF|  — |

#### ADDR0_LIMIT field

<p>Address range 0 limit [31:0]</p>

### DESCENG_ADDR1_BASE register

- Absolute Address: 0x122C
- Base Offset: 0x22C
- Size: 0x4

<p>Base address for descriptor address range 1 (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|ADDR1_BASE|  rw  | 0x0 |  — |

#### ADDR1_BASE field

<p>Address range 1 base [31:0]</p>

### DESCENG_ADDR1_LIMIT register

- Absolute Address: 0x1230
- Base Offset: 0x230
- Size: 0x4

<p>Limit address for descriptor address range 1 (lower 32 bits)</p>

|Bits| Identifier|Access|   Reset  |Name|
|----|-----------|------|----------|----|
|31:0|ADDR1_LIMIT|  rw  |0xFFFFFFFF|  — |

#### ADDR1_LIMIT field

<p>Address range 1 limit [31:0]</p>

### CTRL_CONFIG register

- Absolute Address: 0x1240
- Base Offset: 0x240
- Size: 0x4

<p>Control read/write engine configuration (global for all channels,
Phase 2 producer/consumer). CTRLRD_MAX_TRY bounds ctrl-read poll
retries so a never-matching gate cannot hang a channel; it feeds
cfg_ctrlrd_max_try into every channel's ctrlrd_engine.</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
| 8:0|CTRLRD_MAX_TRY|  rw  | 0x10|  — |
|31:9|     RSVD     |   r  | 0x0 |  — |

#### CTRLRD_MAX_TRY field

<p>Control-read poll retry budget [8:0] (0-511)</p>

#### RSVD field

<p>Reserved</p>

### AXI_XFER_CONFIG register

- Absolute Address: 0x12A0
- Base Offset: 0x2A0
- Size: 0x4

<p>AXI read and write transfer burst sizes</p>

| Bits|  Identifier |Access|Reset|Name|
|-----|-------------|------|-----|----|
| 7:0 |RD_XFER_BEATS|  rw  | 0xF |  — |
| 15:8|WR_XFER_BEATS|  rw  | 0xF |  — |
|23:16|  ALLOC_SIZE |  rw  | 0x10|  — |
|31:24|  DRAIN_SIZE |  rw  | 0x10|  — |

#### RD_XFER_BEATS field

<p>AXI read transfer beats [7:0] - ARLEN value (0-255 represents 1-256 beats). The engine clamps it to the per-channel SRAM depth minus one, and to 254 beyond that (rapids BUG-009): a burst is never larger than the buffer that stages it</p>

#### WR_XFER_BEATS field

<p>AXI write transfer beats [15:8] - AWLEN value (0-255 represents 1-256 beats). The engine clamps it to the per-channel SRAM depth minus one, and to 254 beyond that (rapids BUG-009): a burst is never larger than the buffer that stages it</p>

#### ALLOC_SIZE field

<p>Sink AXIS SRAM allocation size [23:16] - segments reserved per AXIS fill burst</p>

#### DRAIN_SIZE field

<p>Source AXIS drain size [31:24] - beats drained to AXIS per packet request</p>

### PERF_CONFIG register

- Absolute Address: 0x12B0
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

- Absolute Address: 0x12C0
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

- Absolute Address: 0x12C4
- Base Offset: 0x2C4
- Size: 0x4

<p>Combinational status vector for the channel selected by OBS_CTRL.CH_SEL. See stream_core.sv for the bit layout (scheduler_state, sched_rd/wr_valid, sched_wr_ready, error stickies, idle bits, cfg_channel_enable, axi_*_all_complete).</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   FLAGS  |   r  |  —  |  — |

#### FLAGS field

<p>Observation flags</p>

### OBS_DATA0 register

- Absolute Address: 0x12C8
- Base Offset: 0x2C8
- Size: 0x4

<p>Category-muxed data word 0 for the selected channel. Semantics depend on OBS_CTRL.CAT_SEL.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   DATA   |   r  |  —  |  — |

#### DATA field

<p>Observation data 0</p>

### OBS_DATA1 register

- Absolute Address: 0x12CC
- Base Offset: 0x2CC
- Size: 0x4

<p>Category-muxed data word 1 for the selected channel. Semantics depend on OBS_CTRL.CAT_SEL.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   DATA   |   r  |  —  |  — |

#### DATA field

<p>Observation data 1</p>

### TILE_STATUS register

- Absolute Address: 0x12D0
- Base Offset: 0x2D0
- Size: 0x4

<p>Sink-port tile header status (SNK half). Sticky; write 1 to clear.</p>

|Bits| Identifier |  Access |Reset|Name|
|----|------------|---------|-----|----|
|  0 | UNSUPPORTED|rw, woclr| 0x0 |  — |
|  1 |TAG_MISMATCH|rw, woclr| 0x0 |  — |
|31:2|    RSVD    |    r    | 0x0 |  — |

#### UNSUPPORTED field

<p>A packet the sink port consumed without acting on it: a read request to RAPIDS, a reserved ptype, a desc packet with no payload, a tag past NUM_CHANNELS or DATA_WIDTH &lt; 256, or extra desc payload. Sticky; write 1 to clear</p>

#### TAG_MISMATCH field

<p>A data packet whose header tag differed from its stream ID (delivered by stream ID). Sticky; write 1 to clear</p>

#### RSVD field

<p>Reserved</p>

### TILE_DESC_DROPPED register

- Absolute Address: 0x12D4
- Base Offset: 0x2D4
- Size: 0x4

<p>Per source channel: a cell-issued descriptor was dropped (SRC half). Sticky; write 1 to clear.</p>

| Bits|Identifier|  Access |Reset|Name|
|-----|----------|---------|-----|----|
|  0  |   DROP0  |rw, woclr| 0x0 |  — |
|  1  |   DROP1  |rw, woclr| 0x0 |  — |
|  2  |   DROP2  |rw, woclr| 0x0 |  — |
|  3  |   DROP3  |rw, woclr| 0x0 |  — |
|  4  |   DROP4  |rw, woclr| 0x0 |  — |
|  5  |   DROP5  |rw, woclr| 0x0 |  — |
|  6  |   DROP6  |rw, woclr| 0x0 |  — |
|  7  |   DROP7  |rw, woclr| 0x0 |  — |
|  8  |   DROP8  |rw, woclr| 0x0 |  — |
|  9  |   DROP9  |rw, woclr| 0x0 |  — |
|  10 |  DROP10  |rw, woclr| 0x0 |  — |
|  11 |  DROP11  |rw, woclr| 0x0 |  — |
|  12 |  DROP12  |rw, woclr| 0x0 |  — |
|  13 |  DROP13  |rw, woclr| 0x0 |  — |
|  14 |  DROP14  |rw, woclr| 0x0 |  — |
|  15 |  DROP15  |rw, woclr| 0x0 |  — |
|31:16|   RSVD   |    r    | 0x0 |  — |

#### DROP0 field

<p>Channel 0: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP1 field

<p>Channel 1: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP2 field

<p>Channel 2: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP3 field

<p>Channel 3: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP4 field

<p>Channel 4: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP5 field

<p>Channel 5: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP6 field

<p>Channel 6: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP7 field

<p>Channel 7: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP8 field

<p>Channel 8: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP9 field

<p>Channel 9: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP10 field

<p>Channel 10: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP11 field

<p>Channel 11: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP12 field

<p>Channel 12: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP13 field

<p>Channel 13: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP14 field

<p>Channel 14: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### DROP15 field

<p>Channel 15: a cell-issued descriptor was dropped (no free slot, EXT, or during channel reset). Sticky; write 1 to clear</p>

#### RSVD field

<p>Reserved</p>

### TILE_COUNTS register

- Absolute Address: 0x12D8
- Base Offset: 0x2D8
- Size: 0x4

<p>Sink-port packets passed on or consumed (SNK half); 16-bit counters that wrap</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 15:0| DESC_COUNT |   r  |  —  |  — |
|31:16|CREDIT_COUNT|   r  |  —  |  — |

#### DESC_COUNT field

<p>desc packets passed to the source half</p>

#### CREDIT_COUNT field

<p>credit packets received (with TILE_CREDITS = 1 they fill the SRC half's destination counters)</p>

### TILE_ADV_WINDOW register

- Absolute Address: 0x12DC
- Base Offset: 0x2DC
- Size: 0x4

<p>Cycles from reset during which destinations advertise their credits (SRC half). When the window closes, a destination whose counter is still 0 is illegal (TILE_LEGAL_DEST_LO/HI).</p>

|Bits|Identifier|Access| Reset|Name|
|----|----------|------|------|----|
|31:0|  CYCLES  |  rw  |0x1000|  — |

#### CYCLES field

<p>Window length in cycles from reset. Counted from reset, so a write takes effect only if made before the window closes; 0 closes it at once and makes every destination illegal</p>

### TILE_LEGAL_DEST_LO register

- Absolute Address: 0x12E0
- Base Offset: 0x2E0
- Size: 0x4

<p>Saved legal-destination mask, indices 0-31: the nodes' internal IDs (SRC half). 1 = the destination advertised a non-zero credit count in the window. Valid once TILE_CREDIT_STATUS.ADV_DONE is 1; held until reset. A descriptor to an illegal destination is refused as invalid.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   LEGAL  |   r  |  —  |  — |

#### LEGAL field

<p>Bit i: destination index i is legal</p>

### TILE_CREDIT_STATUS register

- Absolute Address: 0x12E4
- Base Offset: 0x2E4
- Size: 0x4

<p>End-to-end tile credit status (SRC half)</p>

| Bits|  Identifier  |Access|Reset|Name|
|-----|--------------|------|-----|----|
|  0  |   ADV_DONE   |   r  |  —  |  — |
|  1  |  RESYNC_BUSY |   r  |  —  |  — |
|  2  | LAND_OVERRUN |   r  |  —  |  — |
|  3  |INTAKE_OVERRUN|   r  |  —  |  — |
| 15:4|     RSVD     |   r  | 0x0 |  — |
|31:16|   RET_COUNT  |   r  |  —  |  — |

#### ADV_DONE field

<p>The advertisement window has closed and TILE_LEGAL_DEST_LO/HI are valid. Tile descriptors wait until it is 1</p>

#### RESYNC_BUSY field

<p>A resync (TILE_RESYNC) is waiting for the tile to be quiescent, or its set packets are still going out (rapids TASK-027)</p>

#### LAND_OVERRUN field

<p>Sticky until reset: a cell sent past its landing-space strap (TILE_LAND_FLITS); the sink port waited for room. A strap contract violation by the sender</p>

#### INTAKE_OVERRUN field

<p>Sticky until reset: a control core sent a desc packet past its intake strap (TILE_DESC_PER_CORE); the descriptor was dropped and its entry returned</p>

#### RSVD field

<p>Reserved</p>

#### RET_COUNT field

<p>Credit packets RAPIDS has sent to the cells and cores (returns and resync sets); 16-bit, wraps</p>

### TILE_LEGAL_DEST_HI register

- Absolute Address: 0x12E8
- Base Offset: 0x2E8
- Size: 0x4

<p>Saved legal-destination mask, indices 32-63: the external IDs, what is attached to each node (SRC half). Same rules as TILE_LEGAL_DEST_LO.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   LEGAL  |   r  |  —  |  — |

#### LEGAL field

<p>Bit i: destination index 32 + i is legal</p>

### TILE_RESYNC register

- Absolute Address: 0x12EC
- Base Offset: 0x2EC
- Size: 0x4

<p>Restores every legal cell's and control core's strap after a root failover (TILE_SPEC 11.10; SRC half). RAPIDS sends each a set credit packet: a cell its TILE_LAND_FLITS, a core its TILE_DESC_PER_CORE. Taken only while the tile is quiescent (tile_quiescent); a request made before then waits for it.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |    GO    |   w  | 0x0 |  — |
|31:1|   RSVD   |   r  | 0x0 |  — |

#### GO field

<p>Write 1 to request a resync</p>

#### RSVD field

<p>Reserved</p>

### TILE_STALL_CYCLES register

- Absolute Address: 0x12F0
- Base Offset: 0x2F0
- Size: 0x4

<p>Stalled-data checks (TILE_SPEC 11.9; SRC half, used by both): data that has not moved for this many cycles raises a MonBus error packet (PktTypeError, event RAPIDS_EVENT_STALL) -- sink SRAM data not written out, a source channel with reads outstanding and no R beat. The default is 10 us at 100 MHz. TILE_CREDITS = 1 only.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|  CYCLES  |  rw  |0x3E8|  — |

#### CYCLES field

<p>Threshold in cycles; 0 turns the checks off</p>

### TILE_STALLED register

- Absolute Address: 0x12F4
- Base Offset: 0x2F4
- Size: 0x4

<p>Per channel of this half: its data has stopped moving past TILE_STALL_CYCLES (the current episode; clears when the data moves or drains). TILE_CREDITS = 1 only.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|    CH    |   r  |  —  |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

#### CH field

<p>Bit n: channel n is stalled</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x1300
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x1300
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x1304
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x1304
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x1308
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x1308
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x130C
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x130C
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x1310
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x1310
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x1314
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x1314
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x1318
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x1318
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x131C
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x131C
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x1320
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x1320
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x1324
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x1324
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x1328
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x1328
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x132C
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x132C
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x1330
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x1330
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x1334
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x1334
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x1338
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x1338
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

## CH_SCRATCH register file

- Absolute Address: 0x133C
- Base Offset: 0x300
- Size: 0x4
- Array Dimensions: [16]
- Array Stride: 0x4
- Total Size: 0x40

<p>Software-defined bits for one channel (host and gatling)</p>

|Offset|Identifier|      Name     |
|------|----------|---------------|
|  0x0 |  SCRATCH |Channel Scratch|

### SCRATCH register

- Absolute Address: 0x133C
- Base Offset: 0x0
- Size: 0x4

<p>Eight read/write bits for the channel; reset 0</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  SCRATCH |  rw  | 0x0 |  — |
|31:8|   RSVD   |   r  | 0x0 |  — |

#### SCRATCH field

<p>Scratch bits [7:0]</p>

#### RSVD field

<p>Reserved</p>

### PERF_CH_SEL register

- Absolute Address: 0x135C
- Base Offset: 0x35C
- Size: 0x4

<p>Selects which channel's buckets appear in RD/WRMON_PERF_CH_*</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 3:0|  CH_SEL  |  rw  | 0x0 |  — |
|31:4|   RSVD   |   r  | 0x0 |  — |

#### CH_SEL field

<p>Channel select (0..NUM_CHANNELS-1)</p>

#### RSVD field

<p>Reserved</p>

### HIST_SEL register

- Absolute Address: 0x1378
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

- Absolute Address: 0x137C
- Base Offset: 0x37C
- Size: 0x4

<p>Transaction count in the HIST_SEL-selected bus/metric/bin</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Selected histogram bin count [31:0]</p>

### HIST_TOTAL register

- Absolute Address: 0x1380
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

### TILE_STRAPS register

- Absolute Address: 0x17FC
- Base Offset: 0x7FC
- Size: 0x4

<p>The straps this RAPIDS reserves toward it (TILE_SPEC 11.9), from
its build parameters, for the Hive to check against the cells'
and cores' straps. Both fields read 0 when TILE_CREDITS = 0 (no
straps). The same values in both halves.</p>

| Bits|  Identifier |Access|Reset|Name|
|-----|-------------|------|-----|----|
| 15:0|  LAND_FLITS |   r  |  —  |  — |
|31:16|DESC_PER_CORE|   r  |  —  |  — |

#### LAND_FLITS field

<p>TILE_LAND_FLITS: landing-space flits per cell, header included</p>

#### DESC_PER_CORE field

<p>TILE_DESC_PER_CORE: descriptor-intake entries per control core</p>

## MON register file

- Absolute Address: 0x1800
- Base Offset: 0x800
- Size: 0x200

<p>AXI monitor + perf registers (relocatable block, instantiated at 0x1000)</p>

|Offset|        Identifier       |                            Name                           |
|------|-------------------------|-----------------------------------------------------------|
| 0x000|     MON_FIFO_STATUS     |                    Monitor FIFO Status                    |
| 0x004|      MON_FIFO_COUNT     |                     Monitor FIFO Count                    |
| 0x0C0|      DAXMON_ENABLE      |               Descriptor AXI Monitor Enable               |
| 0x0C4|      DAXMON_TIMEOUT     |               Descriptor AXI Monitor Timeout              |
| 0x0C8|  DAXMON_LATENCY_THRESH  |          Descriptor AXI Monitor Latency Threshold         |
| 0x0CC|     DAXMON_PKT_MASK     |             Descriptor AXI Monitor Packet Mask            |
| 0x0D0|      DAXMON_ERR_CFG     |        Descriptor AXI Monitor Error Select and Mask       |
| 0x0D4|       DAXMON_MASK1      |               Descriptor AXI Monitor Masks 1              |
| 0x0D8|       DAXMON_MASK2      |               Descriptor AXI Monitor Masks 2              |
| 0x0DC|       DAXMON_MASK3      |               Descriptor AXI Monitor Masks 3              |
| 0x0E0|       RDMON_ENABLE      |               Read Engine AXI Monitor Enable              |
| 0x0E4|      RDMON_TIMEOUT      |              Read Engine AXI Monitor Timeout              |
| 0x0E8|   RDMON_LATENCY_THRESH  |         Read Engine AXI Monitor Latency Threshold         |
| 0x0EC|      RDMON_PKT_MASK     |            Read Engine AXI Monitor Packet Mask            |
| 0x0F0|      RDMON_ERR_CFG      |       Read Engine AXI Monitor Error Select and Mask       |
| 0x0F4|       RDMON_MASK1       |              Read Engine AXI Monitor Masks 1              |
| 0x0F8|       RDMON_MASK2       |              Read Engine AXI Monitor Masks 2              |
| 0x0FC|       RDMON_MASK3       |              Read Engine AXI Monitor Masks 3              |
| 0x100|       WRMON_ENABLE      |              Write Engine AXI Monitor Enable              |
| 0x104|      WRMON_TIMEOUT      |              Write Engine AXI Monitor Timeout             |
| 0x108|   WRMON_LATENCY_THRESH  |         Write Engine AXI Monitor Latency Threshold        |
| 0x10C|      WRMON_PKT_MASK     |            Write Engine AXI Monitor Packet Mask           |
| 0x110|      WRMON_ERR_CFG      |       Write Engine AXI Monitor Error Select and Mask      |
| 0x114|       WRMON_MASK1       |              Write Engine AXI Monitor Masks 1             |
| 0x118|       WRMON_MASK2       |              Write Engine AXI Monitor Masks 2             |
| 0x11C|       WRMON_MASK3       |              Write Engine AXI Monitor Masks 3             |
| 0x150|     DAXMON_PERF_CTRL    |         Descriptor AXI Monitor Perf Window Control        |
| 0x154|    DAXMON_PERF_STATUS   |         Descriptor AXI Monitor Perf Window Status         |
| 0x158|DAXMON_PERF_WINDOW_CYCLES|         Descriptor AXI Monitor Perf Window Cycles         |
| 0x15C| DAXMON_PERF_PROD_CYCLES |       Descriptor AXI Monitor Perf Productive Cycles       |
| 0x160|  DAXMON_PERF_BP_CYCLES  |      Descriptor AXI Monitor Perf Backpressure Cycles      |
| 0x164| DAXMON_PERF_STARV_CYCLES|       Descriptor AXI Monitor Perf Starvation Cycles       |
| 0x168| DAXMON_PERF_IDLE_CYCLES |          Descriptor AXI Monitor Perf Idle Cycles          |
| 0x16C|  DAXMON_PERF_BEAT_COUNT |           Descriptor AXI Monitor Perf Beat Count          |
| 0x170|DAXMON_PERF_BYTE_COUNT_LO|         Descriptor AXI Monitor Perf Byte Count Low        |
| 0x174|DAXMON_PERF_BYTE_COUNT_HI|        Descriptor AXI Monitor Perf Byte Count High        |
| 0x178| DAXMON_PERF_BURST_COUNT |          Descriptor AXI Monitor Perf Burst Count          |
| 0x180|     RDMON_PERF_CTRL     |         Read Datapath Monitor Perf Window Control         |
| 0x184|    RDMON_PERF_STATUS    |          Read Datapath Monitor Perf Window Status         |
| 0x188| RDMON_PERF_WINDOW_CYCLES|          Read Datapath Monitor Perf Window Cycles         |
| 0x18C|  RDMON_PERF_PROD_CYCLES |        Read Datapath Monitor Perf Productive Cycles       |
| 0x190|   RDMON_PERF_BP_CYCLES  |       Read Datapath Monitor Perf Backpressure Cycles      |
| 0x194| RDMON_PERF_STARV_CYCLES |        Read Datapath Monitor Perf Starvation Cycles       |
| 0x198|  RDMON_PERF_IDLE_CYCLES |           Read Datapath Monitor Perf Idle Cycles          |
| 0x19C|  RDMON_PERF_BEAT_COUNT  |           Read Datapath Monitor Perf Beat Count           |
| 0x1A0| RDMON_PERF_BYTE_COUNT_LO|         Read Datapath Monitor Perf Byte Count Low         |
| 0x1A4| RDMON_PERF_BYTE_COUNT_HI|         Read Datapath Monitor Perf Byte Count High        |
| 0x1A8|  RDMON_PERF_BURST_COUNT |           Read Datapath Monitor Perf Burst Count          |
| 0x1B0|     WRMON_PERF_CTRL     |         Write Datapath Monitor Perf Window Control        |
| 0x1B4|    WRMON_PERF_STATUS    |         Write Datapath Monitor Perf Window Status         |
| 0x1B8| WRMON_PERF_WINDOW_CYCLES|         Write Datapath Monitor Perf Window Cycles         |
| 0x1BC|  WRMON_PERF_PROD_CYCLES |       Write Datapath Monitor Perf Productive Cycles       |
| 0x1C0|   WRMON_PERF_BP_CYCLES  |      Write Datapath Monitor Perf Backpressure Cycles      |
| 0x1C4| WRMON_PERF_STARV_CYCLES |       Write Datapath Monitor Perf Starvation Cycles       |
| 0x1C8|  WRMON_PERF_IDLE_CYCLES |          Write Datapath Monitor Perf Idle Cycles          |
| 0x1CC|  WRMON_PERF_BEAT_COUNT  |           Write Datapath Monitor Perf Beat Count          |
| 0x1D0| WRMON_PERF_BYTE_COUNT_LO|         Write Datapath Monitor Perf Byte Count Low        |
| 0x1D4| WRMON_PERF_BYTE_COUNT_HI|        Write Datapath Monitor Perf Byte Count High        |
| 0x1D8|  WRMON_PERF_BURST_COUNT |          Write Datapath Monitor Perf Burst Count          |
| 0x1E0|  RDMON_PERF_CH_PROD_BP  |     Read Datapath Per-Channel Productive/Backpressure     |
| 0x1E4| RDMON_PERF_CH_STARV_IDLE|         Read Datapath Per-Channel Starvation/Idle         |
| 0x1E8|  WRMON_PERF_CH_PROD_BP  |     Write Datapath Per-Channel Productive/Backpressure    |
| 0x1EC| WRMON_PERF_CH_STARV_IDLE|         Write Datapath Per-Channel Starvation/Idle        |
| 0x1F0|  RDMON_PERF_CH_OVERFLOW |        Read Datapath Per-Channel Overflow Stickies        |
| 0x1F4|  WRMON_PERF_CH_OVERFLOW |        Write Datapath Per-Channel Overflow Stickies       |
| 0x1F8|RDMON_PERF_CH_OVERFLOW_HI| Read Datapath Per-Channel Overflow Stickies, channels 8-15|
| 0x1FC|WRMON_PERF_CH_OVERFLOW_HI|Write Datapath Per-Channel Overflow Stickies, channels 8-15|

### MON_FIFO_STATUS register

- Absolute Address: 0x1800
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

- Absolute Address: 0x1804
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

- Absolute Address: 0x18C0
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

- Absolute Address: 0x18C4
- Base Offset: 0xC4
- Size: 0x4

<p>Descriptor AXI monitor timeout threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x2710|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0]</p>

### DAXMON_LATENCY_THRESH register

- Absolute Address: 0x18C8
- Base Offset: 0xC8
- Size: 0x4

<p>Descriptor AXI monitor latency threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|LATENCY_THRESH|  rw  |0x1388|  — |

#### LATENCY_THRESH field

<p>Latency threshold cycles [31:0]</p>

### DAXMON_PKT_MASK register

- Absolute Address: 0x18CC
- Base Offset: 0xCC
- Size: 0x4

<p>Descriptor AXI monitor packet type filtering (16-bit mask)</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0| PKT_MASK |  rw  |0xFFFF|  — |
|31:16|   RSVD   |   r  |  0x0 |  — |

#### PKT_MASK field

<p>Packet type mask [15:0] - bit[type] = 1 MASKS (drops) that packet type, at the monitor-lite and again at the monbus group. Reset = all masked: the host clears the bits of the classes it wants to see (rapids BUG-008 corrected this description; the polarity and the reset are as intended)</p>

#### RSVD field

<p>Reserved</p>

### DAXMON_ERR_CFG register

- Absolute Address: 0x18D0
- Base Offset: 0xD0
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

- Absolute Address: 0x18D4
- Base Offset: 0xD4
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

- Absolute Address: 0x18D8
- Base Offset: 0xD8
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

- Absolute Address: 0x18DC
- Base Offset: 0xDC
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

- Absolute Address: 0x18E0
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

- Absolute Address: 0x18E4
- Base Offset: 0xE4
- Size: 0x4

<p>Read engine AXI monitor timeout threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x2710|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0]</p>

### RDMON_LATENCY_THRESH register

- Absolute Address: 0x18E8
- Base Offset: 0xE8
- Size: 0x4

<p>Read engine AXI monitor latency threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|LATENCY_THRESH|  rw  |0x1388|  — |

#### LATENCY_THRESH field

<p>Latency threshold cycles [31:0]</p>

### RDMON_PKT_MASK register

- Absolute Address: 0x18EC
- Base Offset: 0xEC
- Size: 0x4

<p>Read engine AXI monitor packet type filtering (16-bit mask)</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0| PKT_MASK |  rw  |0xFFFF|  — |
|31:16|   RSVD   |   r  |  0x0 |  — |

#### PKT_MASK field

<p>Packet type mask [15:0] - bit[type] = 1 MASKS (drops) that packet type, at the monitor-lite and again at the monbus group. Reset = all masked: the host clears the bits of the classes it wants to see (rapids BUG-008 corrected this description; the polarity and the reset are as intended)</p>

#### RSVD field

<p>Reserved</p>

### RDMON_ERR_CFG register

- Absolute Address: 0x18F0
- Base Offset: 0xF0
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

- Absolute Address: 0x18F4
- Base Offset: 0xF4
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

- Absolute Address: 0x18F8
- Base Offset: 0xF8
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

- Absolute Address: 0x18FC
- Base Offset: 0xFC
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

- Absolute Address: 0x1900
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
|31:6|    RSVD   |   r  | 0x0 |  — |

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

#### RSVD field

<p>Reserved</p>

### WRMON_TIMEOUT register

- Absolute Address: 0x1904
- Base Offset: 0x104
- Size: 0x4

<p>Write engine AXI monitor timeout threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|TIMEOUT_CYCLES|  rw  |0x2710|  — |

#### TIMEOUT_CYCLES field

<p>Timeout cycles [31:0]</p>

### WRMON_LATENCY_THRESH register

- Absolute Address: 0x1908
- Base Offset: 0x108
- Size: 0x4

<p>Write engine AXI monitor latency threshold (cycles)</p>

|Bits|  Identifier  |Access| Reset|Name|
|----|--------------|------|------|----|
|31:0|LATENCY_THRESH|  rw  |0x1388|  — |

#### LATENCY_THRESH field

<p>Latency threshold cycles [31:0]</p>

### WRMON_PKT_MASK register

- Absolute Address: 0x190C
- Base Offset: 0x10C
- Size: 0x4

<p>Write engine AXI monitor packet type filtering (16-bit mask)</p>

| Bits|Identifier|Access| Reset|Name|
|-----|----------|------|------|----|
| 15:0| PKT_MASK |  rw  |0xFFFF|  — |
|31:16|   RSVD   |   r  |  0x0 |  — |

#### PKT_MASK field

<p>Packet type mask [15:0] - bit[type] = 1 MASKS (drops) that packet type, at the monitor-lite and again at the monbus group. Reset = all masked: the host clears the bits of the classes it wants to see (rapids BUG-008 corrected this description; the polarity and the reset are as intended)</p>

#### RSVD field

<p>Reserved</p>

### WRMON_ERR_CFG register

- Absolute Address: 0x1910
- Base Offset: 0x110
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

- Absolute Address: 0x1914
- Base Offset: 0x114
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

- Absolute Address: 0x1918
- Base Offset: 0x118
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

- Absolute Address: 0x191C
- Base Offset: 0x11C
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

### DAXMON_PERF_CTRL register

- Absolute Address: 0x1950
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

- Absolute Address: 0x1954
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

- Absolute Address: 0x1958
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

- Absolute Address: 0x195C
- Base Offset: 0x15C
- Size: 0x4

<p>Cycles with R data valid &amp;&amp; ready (data delivered)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Productive cycles [31:0]</p>

### DAXMON_PERF_BP_CYCLES register

- Absolute Address: 0x1960
- Base Offset: 0x160
- Size: 0x4

<p>Cycles with R data valid &amp;&amp; !ready (back-pressure)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Backpressure cycles [31:0]</p>

### DAXMON_PERF_STARV_CYCLES register

- Absolute Address: 0x1964
- Base Offset: 0x164
- Size: 0x4

<p>Cycles with !R data valid &amp;&amp; ready (starvation)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Starvation cycles [31:0]</p>

### DAXMON_PERF_IDLE_CYCLES register

- Absolute Address: 0x1968
- Base Offset: 0x168
- Size: 0x4

<p>Cycles with !R data valid &amp;&amp; !ready (idle)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Idle cycles [31:0]</p>

### DAXMON_PERF_BEAT_COUNT register

- Absolute Address: 0x196C
- Base Offset: 0x16C
- Size: 0x4

<p>R beats transferred in window (= productive cycles)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Beat count [31:0]</p>

### DAXMON_PERF_BYTE_COUNT_LO register

- Absolute Address: 0x1970
- Base Offset: 0x170
- Size: 0x4

<p>Bytes transferred in window (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [31:0]</p>

### DAXMON_PERF_BYTE_COUNT_HI register

- Absolute Address: 0x1974
- Base Offset: 0x174
- Size: 0x4

<p>Bytes transferred in window (upper 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [63:32]</p>

### DAXMON_PERF_BURST_COUNT register

- Absolute Address: 0x1978
- Base Offset: 0x178
- Size: 0x4

<p>AR handshakes (bursts issued) in window</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Burst count [31:0]</p>

### RDMON_PERF_CTRL register

- Absolute Address: 0x1980
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

- Absolute Address: 0x1984
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

- Absolute Address: 0x1988
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

- Absolute Address: 0x198C
- Base Offset: 0x18C
- Size: 0x4

<p>Cycles with R data valid &amp;&amp; ready (data delivered)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Productive cycles [31:0]</p>

### RDMON_PERF_BP_CYCLES register

- Absolute Address: 0x1990
- Base Offset: 0x190
- Size: 0x4

<p>Cycles with R data valid &amp;&amp; !ready (back-pressure)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Backpressure cycles [31:0]</p>

### RDMON_PERF_STARV_CYCLES register

- Absolute Address: 0x1994
- Base Offset: 0x194
- Size: 0x4

<p>Cycles with !R data valid &amp;&amp; ready (starvation)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Starvation cycles [31:0]</p>

### RDMON_PERF_IDLE_CYCLES register

- Absolute Address: 0x1998
- Base Offset: 0x198
- Size: 0x4

<p>Cycles with !R data valid &amp;&amp; !ready (idle)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Idle cycles [31:0]</p>

### RDMON_PERF_BEAT_COUNT register

- Absolute Address: 0x199C
- Base Offset: 0x19C
- Size: 0x4

<p>R beats transferred in window (= productive cycles)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Beat count [31:0]</p>

### RDMON_PERF_BYTE_COUNT_LO register

- Absolute Address: 0x19A0
- Base Offset: 0x1A0
- Size: 0x4

<p>Bytes transferred in window (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [31:0]</p>

### RDMON_PERF_BYTE_COUNT_HI register

- Absolute Address: 0x19A4
- Base Offset: 0x1A4
- Size: 0x4

<p>Bytes transferred in window (upper 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [63:32]</p>

### RDMON_PERF_BURST_COUNT register

- Absolute Address: 0x19A8
- Base Offset: 0x1A8
- Size: 0x4

<p>AR handshakes (bursts issued) in window</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Burst count [31:0]</p>

### WRMON_PERF_CTRL register

- Absolute Address: 0x19B0
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

- Absolute Address: 0x19B4
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

- Absolute Address: 0x19B8
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

- Absolute Address: 0x19BC
- Base Offset: 0x1BC
- Size: 0x4

<p>Cycles with W data valid &amp;&amp; ready (beat delivered)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Productive cycles [31:0]</p>

### WRMON_PERF_BP_CYCLES register

- Absolute Address: 0x19C0
- Base Offset: 0x1C0
- Size: 0x4

<p>Cycles with W data valid &amp;&amp; !ready (back-pressure)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Backpressure cycles [31:0]</p>

### WRMON_PERF_STARV_CYCLES register

- Absolute Address: 0x19C4
- Base Offset: 0x1C4
- Size: 0x4

<p>Cycles with !W data valid &amp;&amp; ready (starvation)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Starvation cycles [31:0]</p>

### WRMON_PERF_IDLE_CYCLES register

- Absolute Address: 0x19C8
- Base Offset: 0x1C8
- Size: 0x4

<p>Cycles with !W data valid &amp;&amp; !ready (idle)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Idle cycles [31:0]</p>

### WRMON_PERF_BEAT_COUNT register

- Absolute Address: 0x19CC
- Base Offset: 0x1CC
- Size: 0x4

<p>W beats transferred in window (= productive cycles)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Beat count [31:0]</p>

### WRMON_PERF_BYTE_COUNT_LO register

- Absolute Address: 0x19D0
- Base Offset: 0x1D0
- Size: 0x4

<p>Bytes transferred in window (lower 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [31:0]</p>

### WRMON_PERF_BYTE_COUNT_HI register

- Absolute Address: 0x19D4
- Base Offset: 0x1D4
- Size: 0x4

<p>Bytes transferred in window (upper 32 bits)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Byte count [63:32]</p>

### WRMON_PERF_BURST_COUNT register

- Absolute Address: 0x19D8
- Base Offset: 0x1D8
- Size: 0x4

<p>AW handshakes (bursts issued) in window</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Burst count [31:0]</p>

### RDMON_PERF_CH_PROD_BP register

- Absolute Address: 0x19E0
- Base Offset: 0x1E0
- Size: 0x4

<p>Selected channel: {backpressure[31:16], productive[15:0]} (16-bit each)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>{bp[15:0], prod[15:0]} for PERF_CH_SEL channel</p>

### RDMON_PERF_CH_STARV_IDLE register

- Absolute Address: 0x19E4
- Base Offset: 0x1E4
- Size: 0x4

<p>Selected channel: {idle[31:16], starvation[15:0]} (16-bit each)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>{idle[15:0], starv[15:0]} for PERF_CH_SEL channel</p>

### WRMON_PERF_CH_PROD_BP register

- Absolute Address: 0x19E8
- Base Offset: 0x1E8
- Size: 0x4

<p>Selected channel: {backpressure[31:16], productive[15:0]} (16-bit each)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>{bp[15:0], prod[15:0]} for PERF_CH_SEL channel</p>

### WRMON_PERF_CH_STARV_IDLE register

- Absolute Address: 0x19EC
- Base Offset: 0x1EC
- Size: 0x4

<p>Selected channel: {idle[31:16], starvation[15:0]} (16-bit each)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>{idle[15:0], starv[15:0]} for PERF_CH_SEL channel</p>

### RDMON_PERF_CH_OVERFLOW register

- Absolute Address: 0x19F0
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

- Absolute Address: 0x19F4
- Base Offset: 0x1F4
- Size: 0x4

<p>All channels, {prod,bp,starv,idle} sticky overflow per channel.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Per-channel overflow mask (NUM_CHANNELS*4 bits)</p>

### RDMON_PERF_CH_OVERFLOW_HI register

- Absolute Address: 0x19F8
- Base Offset: 0x1F8
- Size: 0x4

<p>Channels 8..15 of RDMON_PERF_CH_OVERFLOW (4 bits/channel, channel 8 in the low nibble).</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Per-channel overflow mask, channels 8..15</p>

### WRMON_PERF_CH_OVERFLOW_HI register

- Absolute Address: 0x19FC
- Base Offset: 0x1FC
- Size: 0x4

<p>Channels 8..15 of WRMON_PERF_CH_OVERFLOW (4 bits/channel, channel 8 in the low nibble).</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    VAL   |   r  |  —  |  — |

#### VAL field

<p>Per-channel overflow mask, channels 8..15</p>
