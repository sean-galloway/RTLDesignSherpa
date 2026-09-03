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

|Offset|Identifier|     Name    |
|------|----------|-------------|
| 0x100| CAM_CLEAR|  CAM clear  |
| 0x108|  CAM_KEY |   CAM key   |
| 0x110| CAM_LOAD |   CAM load  |
| 0x118|WATCH_CTRL|Watch control|
| 0x120| LATCH_SEL| Latch select|

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
