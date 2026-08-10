<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## obs_regs_top address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x6C

<p>APB-fronted configuration for the inline performance observer</p>

|Offset|Identifier|           Name           |
|------|----------|--------------------------|
|  0x0 |    OBS   |DMA observer configuration|

## OBS register file

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x6C

<p>Runtime config for the inline performance-observation block</p>

|Offset|  Identifier  |         Name        |
|------|--------------|---------------------|
| 0x00 | AXI_PKT_MASK |   AXI packet mask   |
| 0x04 |   AXI_MASK1  |      AXI mask1      |
| 0x08 |   AXI_MASK2  |      AXI mask2      |
| 0x0C |   AXI_MASK3  |      AXI mask3      |
| 0x10 |   AXI_MASK4  |      AXI mask4      |
| 0x20 | AXIS_PKT_MASK|   AXIS packet mask  |
| 0x24 |  AXIS_MASK1  |      AXIS mask1     |
| 0x28 |  AXIS_MASK2  |      AXIS mask2     |
| 0x2C |  AXIS_MASK3  |      AXIS mask3     |
| 0x40 | CORE_PKT_MASK|   CORE packet mask  |
| 0x44 |  CORE_MASK1  |      CORE mask1     |
| 0x48 |  CORE_MASK2  |      CORE mask2     |
| 0x4C |  CORE_MASK3  |      CORE mask3     |
| 0x60 |   OBS_CTRL   |   Observer control  |
| 0x64 | OBS_BASE_ADDR| Observer window base|
| 0x68 |OBS_LIMIT_ADDR|Observer window limit|

### AXI_PKT_MASK register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>bit[type]=1 drops that packet type; ERR_SELECT routes err-FIFO vs bulk</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| PKT_MASK |  rw  | 0x0 |  — |
|31:16|ERR_SELECT|  rw  | 0x0 |  — |

### AXI_MASK1 register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

<p>Per-event-code drop masks, indexed by event_code[3:0]</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 15:0| ERROR_MASK |  rw  | 0x0 |  — |
|31:16|TIMEOUT_MASK|  rw  | 0x0 |  — |

### AXI_MASK2 register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 15:0| COMPL_MASK|  rw  | 0x0 |  — |
|31:16|THRESH_MASK|  rw  | 0x0 |  — |

### AXI_MASK3 register

- Absolute Address: 0xC
- Base Offset: 0xC
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| PERF_MASK|  rw  | 0x0 |  — |
|31:16| ADDR_MASK|  rw  | 0x0 |  — |

### AXI_MASK4 register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|DEBUG_MASK|  rw  | 0x0 |  — |
|31:16|   RSVD   |   r  | 0x0 |  — |

### AXIS_PKT_MASK register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

<p>bit[type]=1 drops that packet type</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| PKT_MASK |  rw  | 0x0 |  — |
|31:16|ERR_SELECT|  rw  | 0x0 |  — |

### AXIS_MASK1 register

- Absolute Address: 0x24
- Base Offset: 0x24
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 15:0| ERROR_MASK |  rw  | 0x0 |  — |
|31:16|TIMEOUT_MASK|  rw  | 0x0 |  — |

### AXIS_MASK2 register

- Absolute Address: 0x28
- Base Offset: 0x28
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 15:0| COMPL_MASK |  rw  | 0x0 |  — |
|31:16|CHANNEL_MASK|  rw  | 0x0 |  — |

### AXIS_MASK3 register

- Absolute Address: 0x2C
- Base Offset: 0x2C
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 15:0|CREDIT_MASK|  rw  | 0x0 |  — |
|31:16|STREAM_MASK|  rw  | 0x0 |  — |

### CORE_PKT_MASK register

- Absolute Address: 0x40
- Base Offset: 0x40
- Size: 0x4

<p>bit[type]=1 drops that packet type</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| PKT_MASK |  rw  | 0x0 |  — |
|31:16|ERR_SELECT|  rw  | 0x0 |  — |

### CORE_MASK1 register

- Absolute Address: 0x44
- Base Offset: 0x44
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits| Identifier |Access|Reset|Name|
|-----|------------|------|-----|----|
| 15:0| ERROR_MASK |  rw  | 0x0 |  — |
|31:16|TIMEOUT_MASK|  rw  | 0x0 |  — |

### CORE_MASK2 register

- Absolute Address: 0x48
- Base Offset: 0x48
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 15:0| COMPL_MASK|  rw  | 0x0 |  — |
|31:16|THRESH_MASK|  rw  | 0x0 |  — |

### CORE_MASK3 register

- Absolute Address: 0x4C
- Base Offset: 0x4C
- Size: 0x4

<p>Per-event-code drop masks</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| PERF_MASK|  rw  | 0x0 |  — |
|31:16|DEBUG_MASK|  rw  | 0x0 |  — |

### OBS_CTRL register

- Absolute Address: 0x60
- Base Offset: 0x60
- Size: 0x4

<p>Monbus group drain + compression</p>

| Bits|   Identifier  |Access|Reset|Name|
|-----|---------------|------|-----|----|
| 15:0|FLUSH_WATERMARK|  rw  | 0x10|  — |
|  16 |  COMPRESS_EN  |  rw  | 0x0 |  — |
|31:17|      RSVD     |   r  | 0x0 |  — |

#### FLUSH_WATERMARK field

<p>Bulk-write flush watermark</p>

#### COMPRESS_EN field

<p>1 = compress the monbus write stream. The tally reassembles RAW 3-beat records, so leave 0 unless the consumer decompresses.</p>

### OBS_BASE_ADDR register

- Absolute Address: 0x64
- Base Offset: 0x64
- Size: 0x4

<p>Monbus bulk-write window low bound</p>

|Bits|Identifier|Access| Reset |Name|
|----|----------|------|-------|----|
|31:0|   VALUE  |  rw  |0x40000|  — |

### OBS_LIMIT_ADDR register

- Absolute Address: 0x68
- Base Offset: 0x68
- Size: 0x4

<p>Monbus bulk-write window high bound</p>

|Bits|Identifier|Access| Reset |Name|
|----|----------|------|-------|----|
|31:0|   VALUE  |  rw  |0x7FFFF|  — |
