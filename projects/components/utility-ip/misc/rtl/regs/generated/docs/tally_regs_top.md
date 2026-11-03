<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## tally_regs_top address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x124

<p>Top-level wrapper so peakrdl_generate emits RTL + regmap for the tally</p>

|Offset|Identifier|            Name           |
|------|----------|---------------------------|
|  0x0 |   TALLY  |monbus packet tally control|

## TALLY register file

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x124

<p>CAM programming and first-event capture control for monbus_tally_axil</p>

|Offset| Identifier |        Name        |
|------|------------|--------------------|
| 0x010|LATCH_STATUS|    Latch status    |
| 0x018| LATCH_PKT0 | Latch packet word 0|
| 0x020| LATCH_PKT1 | Latch packet word 1|
| 0x028| LATCH_PKT2 | Latch packet word 2|
| 0x030| LATCH_PKT3 | Latch packet word 3|
| 0x038| LATCH_TS_LO| Latch timestamp low|
| 0x040| LATCH_TS_HI|Latch timestamp high|
| 0x100|  CAM_CLEAR |      CAM clear     |
| 0x108|   CAM_KEY  |       CAM key      |
| 0x110|  CAM_LOAD  |      CAM load      |
| 0x118| WATCH_CTRL |    Watch control   |
| 0x120|  LATCH_SEL |    Latch select    |

### LATCH_STATUS register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>FILL = slots captured so far; VALID = selected slot holds an event.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|15:0|   FILL   |   r  | 0x0 |  — |
| 16 |   VALID  |   r  | 0x0 |  — |

### LATCH_PKT0 register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

<p>Selected slot packet[31:0].</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   DATA   |   r  | 0x0 |  — |

### LATCH_PKT1 register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

<p>Selected slot packet[63:32].</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   DATA   |   r  | 0x0 |  — |

### LATCH_PKT2 register

- Absolute Address: 0x28
- Base Offset: 0x28
- Size: 0x4

<p>Selected slot packet[95:64].</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   DATA   |   r  | 0x0 |  — |

### LATCH_PKT3 register

- Absolute Address: 0x30
- Base Offset: 0x30
- Size: 0x4

<p>Selected slot packet[127:96].</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   DATA   |   r  | 0x0 |  — |

### LATCH_TS_LO register

- Absolute Address: 0x38
- Base Offset: 0x38
- Size: 0x4

<p>Selected slot timestamp[31:0].</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   DATA   |   r  | 0x0 |  — |

### LATCH_TS_HI register

- Absolute Address: 0x40
- Base Offset: 0x40
- Size: 0x4

<p>Selected slot timestamp[63:32].</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   DATA   |   r  | 0x0 |  — |

### CAM_CLEAR register

- Absolute Address: 0x100
- Base Offset: 0x100
- Size: 0x4

<p>Any write invalidates every CAM entry. Self-clearing action.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |   CLEAR  |   w  | 0x0 |  — |

### CAM_KEY register

- Absolute Address: 0x108
- Base Offset: 0x108
- Size: 0x4

<p>Key latched here is loaded into the CAM by the next CAM_LOAD write. Holds its value.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    KEY   |  rw  | 0x0 |  — |

### CAM_LOAD register

- Absolute Address: 0x110
- Base Offset: 0x110
- Size: 0x4

<p>Writing loads CAM_KEY into entry[INDEX] with the given VALID. Self-clearing action.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|   INDEX  |   w  | 0x0 |  — |
| 31 |   VALID  |   w  | 0x0 |  — |

### WATCH_CTRL register

- Absolute Address: 0x118
- Base Offset: 0x118
- Size: 0x4

<p>MASK bit[pkt_type]=1 also captures that type; ARM enables capture.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|15:0|   MASK   |  rw  | 0x0 |  — |
| 31 |    ARM   |  rw  | 0x1 |  — |

### LATCH_SEL register

- Absolute Address: 0x120
- Base Offset: 0x120
- Size: 0x4

<p>Which capture slot the read port returns.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|    SEL   |  rw  | 0x0 |  — |
