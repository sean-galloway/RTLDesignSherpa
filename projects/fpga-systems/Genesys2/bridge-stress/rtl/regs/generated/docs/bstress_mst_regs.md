<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## bstress_mst_regs address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x26C

<p>Configuration and status of one bus-stress master</p>

|Offset| Identifier |Name|
|------|------------|----|
| 0x000|     ID     |  — |
| 0x004|   PARAMS   |  — |
| 0x010|   RD_CTRL  |  — |
| 0x014|RD_TXN_COUNT|  — |
| 0x018|   RD_SEED  |  — |
| 0x01C|  RD_ID_CFG |  — |
| 0x020|   RD_MEM   |  — |
| 0x030|   WR_CTRL  |  — |
| 0x034|WR_TXN_COUNT|  — |
| 0x038|   WR_SEED  |  — |
| 0x03C|  WR_ID_CFG |  — |
| 0x040|   WR_ATOM  |  — |
| 0x044|   WR_MEM   |  — |
| 0x100|   WIN[0]   |  — |
| 0x110|   WIN[1]   |  — |
| 0x120|   WIN[2]   |  — |
| 0x130|   WIN[3]   |  — |
| 0x140|   WIN[4]   |  — |
| 0x150|   WIN[5]   |  — |
| 0x160|   WIN[6]   |  — |
| 0x170|   WIN[7]   |  — |
| 0x200|  RD_STATUS |  — |
| 0x204|  RD_ISSUED |  — |
| 0x208|RD_COMPLETED|  — |
| 0x20C|  RD_BEATS  |  — |
| 0x210|   RD_ERR   |  — |
| 0x214|  RD_FE_ID  |  — |
| 0x218| RD_FE_ADDR |  — |
| 0x21C|  RD_FE_EXP |  — |
| 0x220|  RD_FE_ACT |  — |
| 0x224| RD_LAT_MAX |  — |
| 0x228| RD_LAT_SUM |  — |
| 0x240|  WR_STATUS |  — |
| 0x244|  WR_ISSUED |  — |
| 0x248|WR_COMPLETED|  — |
| 0x24C|  WR_BEATS  |  — |
| 0x250|   WR_ERR   |  — |
| 0x254|  WR_FE_ID  |  — |
| 0x258| WR_FE_ADDR |  — |
| 0x25C|  WR_FE_EXP |  — |
| 0x260|  WR_FE_ACT |  — |
| 0x264| WR_LAT_MAX |  — |
| 0x268| WR_LAT_SUM |  — |

### ID register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>Identity: 0x5354 ('ST') and the build parameters.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | BUS_BYTES|   r  | 0x0 |  — |
| 12:8| ID_WIDTH |   r  | 0x0 |  — |
|15:13| PROTOCOL |   r  | 0x0 |  — |
|31:16|   MAGIC  |   r  | 0x0 |  — |

#### BUS_BYTES field

<p>Data width / 8 (bus bytes).</p>

#### ID_WIDTH field

<p>AXI ID width.</p>

#### PROTOCOL field

<p>Protocol: 0 AXI4, 1 AXI3, 2 AXI5, 3 AXI4-Lite, 4 AXI5-Lite, 5 APB4, 6 APB5, 7 WB4.</p>

#### MAGIC field

<p>Constant 0x5354.</p>

### PARAMS register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

<p>Build parameters.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |   DEPTH  |   r  | 0x0 |  — |
| 11:8|   NWIN   |   r  | 0x0 |  — |
|  12 |  HAS_RD  |   r  | 0x0 |  — |
|  13 |  HAS_WR  |   r  | 0x0 |  — |
|19:16|   INDEX  |   r  | 0x0 |  — |

#### DEPTH field

<p>Bursts in flight per direction, as built.</p>

#### NWIN field

<p>Windows built.</p>

#### HAS_RD field

<p>Read direction built.</p>

#### HAS_WR field

<p>Write direction built.</p>

#### INDEX field

<p>Index of this master in the harness.</p>

### RD_CTRL register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

| Bits|  Identifier |Access|Reset|Name|
|-----|-------------|------|-----|----|
|  0  |    ENABLE   |  rw  | 0x0 |  — |
|  1  |   QOS_RAND  |  rw  | 0x0 |  — |
| 6:2 | TIMEOUT_LG2 |  rw  | 0x0 |  — |
|  7  |    IDUNQ    |  rw  | 0x0 |  — |
| 11:8|RESP_THROTTLE|  rw  | 0x0 |  — |
|15:12|DATA_THROTTLE|  rw  | 0x0 |  — |
|23:16|   GAP_MASK  |  rw  | 0x0 |  — |
|31:24|   MAX_OUT   |  rw  | 0x0 |  — |

#### ENABLE field

<p>This direction runs on GO.</p>

#### QOS_RAND field

<p>AxQOS random (else 0).</p>

#### TIMEOUT_LG2 field

<p>ERR_HANG after 2^n cycles with work outstanding and no response; 0 = off.</p>

#### IDUNQ field

<p>AXI5: mark AxIDUNQ on bursts an address hash picks, when their ID has nothing outstanding; nothing else is issued on that ID until it completes.</p>

#### RESP_THROTTLE field

<p>RREADY/BREADY low with probability n/16.</p>

#### DATA_THROTTLE field

<p>Writes: a WVALID bubble between beats with probability n/16.</p>

#### GAP_MASK field

<p>Idle cycles after a burst = random &amp; GAP_MASK.</p>

#### MAX_OUT field

<p>Bursts in flight; 0 = as built (PARAMS.DEPTH).</p>

### RD_TXN_COUNT register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

#### VALUE field

<p>Bursts per run; 0 = until STOP.</p>

### RD_SEED register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

#### VALUE field

<p>Transaction PRNG seed; 0 = the built-in seed. The burst sequence is a function of this alone.</p>

### RD_ID_CFG register

- Absolute Address: 0x1C
- Base Offset: 0x1C
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|   BASE   |  rw  | 0x0 |  — |
|31:16|   MASK   |  rw  | 0x0 |  — |

#### BASE field

<p>AxID = BASE ^ (random &amp; MASK).</p>

### RD_MEM register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |   FILL   |  rw  | 0x0 |  — |
|13:8|  MEM_LG2 |  rw  | 0x0 |  — |

#### FILL field

<p>Fill: sweep the lowest enabled window from its base in full-width INCR bursts, every strobe set, instead of drawing bursts. TXN_COUNT = window bytes / bytes per burst covers it once. How a real memory (a MEM window) gets known contents before it is read.</p>

#### MEM_LG2 field

<p>MEM windows hash the address modulo 2^MEM_LG2 (the window offset when the window is aligned to it), so two MEM windows with one tag hold one image.</p>

### WR_CTRL register

- Absolute Address: 0x30
- Base Offset: 0x30
- Size: 0x4

| Bits|  Identifier |Access|Reset|Name|
|-----|-------------|------|-----|----|
|  0  |    ENABLE   |  rw  | 0x0 |  — |
|  1  |   QOS_RAND  |  rw  | 0x0 |  — |
| 6:2 | TIMEOUT_LG2 |  rw  | 0x0 |  — |
|  7  |    IDUNQ    |  rw  | 0x0 |  — |
| 11:8|RESP_THROTTLE|  rw  | 0x0 |  — |
|15:12|DATA_THROTTLE|  rw  | 0x0 |  — |
|23:16|   GAP_MASK  |  rw  | 0x0 |  — |
|31:24|   MAX_OUT   |  rw  | 0x0 |  — |

#### ENABLE field

<p>This direction runs on GO.</p>

#### QOS_RAND field

<p>AxQOS random (else 0).</p>

#### TIMEOUT_LG2 field

<p>ERR_HANG after 2^n cycles with work outstanding and no response; 0 = off.</p>

#### IDUNQ field

<p>AXI5: mark AxIDUNQ on bursts an address hash picks, when their ID has nothing outstanding; nothing else is issued on that ID until it completes.</p>

#### RESP_THROTTLE field

<p>RREADY/BREADY low with probability n/16.</p>

#### DATA_THROTTLE field

<p>Writes: a WVALID bubble between beats with probability n/16.</p>

#### GAP_MASK field

<p>Idle cycles after a burst = random &amp; GAP_MASK.</p>

#### MAX_OUT field

<p>Bursts in flight; 0 = as built (PARAMS.DEPTH).</p>

### WR_TXN_COUNT register

- Absolute Address: 0x34
- Base Offset: 0x34
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

#### VALUE field

<p>Bursts per run; 0 = until STOP.</p>

### WR_SEED register

- Absolute Address: 0x38
- Base Offset: 0x38
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

#### VALUE field

<p>Transaction PRNG seed; 0 = the built-in seed. The burst sequence is a function of this alone.</p>

### WR_ID_CFG register

- Absolute Address: 0x3C
- Base Offset: 0x3C
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|   BASE   |  rw  | 0x0 |  — |
|31:16|   MASK   |  rw  | 0x0 |  — |

#### BASE field

<p>AxID = BASE ^ (random &amp; MASK).</p>

### WR_ATOM register

- Absolute Address: 0x40
- Base Offset: 0x40
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 3:0|    LG2   |  rw  | 0x0 |  — |

#### LG2 field

<p>AXI5: 1 write burst in 2^n to an ATOMIC window becomes a one-beat atomic (Store / Load / Swap / Compare, by address hash) on an ID with the MSB set; 0 = none. Keep RD_ID_CFG and WR_ID_CFG below the ID MSB when this is set: those IDs belong to atomics.</p>

### WR_MEM register

- Absolute Address: 0x44
- Base Offset: 0x44
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |   FILL   |  rw  | 0x0 |  — |
|13:8|  MEM_LG2 |  rw  | 0x0 |  — |

#### FILL field

<p>Fill: sweep the lowest enabled window from its base in full-width INCR bursts, every strobe set, instead of drawing bursts. TXN_COUNT = window bytes / bytes per burst covers it once. How a real memory (a MEM window) gets known contents before it is read.</p>

#### MEM_LG2 field

<p>MEM windows hash the address modulo 2^MEM_LG2 (the window offset when the window is aligned to it), so two MEM windows with one tag hold one image.</p>

## WIN register file

- Absolute Address: 0x100
- Base Offset: 0x100
- Size: 0xC
- Array Dimensions: [8]
- Array Stride: 0x10
- Total Size: 0x80

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   BASE   |  — |
|  0x4 |   CFG0   |  — |
|  0x8 |   CFG1   |  — |

### BASE register

- Absolute Address: 0x100
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

#### VALUE field

<p>Window base (aligned to its size).</p>

### CFG0 register

- Absolute Address: 0x104
- Base Offset: 0x4
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 5:0 | SIZE_LG2 |  rw  | 0x0 |  — |
| 7:6 |   RESP   |  rw  | 0x0 |  — |
| 15:8|    TAG   |  rw  | 0x0 |  — |
|23:16| LEN_MASK |  rw  | 0x0 |  — |

#### SIZE_LG2 field

<p>Window = 2^SIZE_LG2 bytes (&gt;= the bus width).</p>

#### RESP field

<p>Response every access must get: 0 OKAY, 2 SLVERR, 3 DECERR.</p>

#### TAG field

<p>Tag of the slave owning the window (folds into its data).</p>

#### LEN_MASK field

<p>AxLEN = random &amp; LEN_MASK (15 for an AXI3 path, 0 for single-beat protocols).</p>

### CFG1 register

- Absolute Address: 0x108
- Base Offset: 0x8
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 2:0 | SIZE_MIN |  rw  | 0x0 |  — |
| 6:4 | SIZE_MAX |  rw  | 0x7 |  — |
| 10:8|BURST_MASK|  rw  | 0x2 |  — |
|  12 | UNALIGNED|  rw  | 0x0 |  — |
|  13 | STRB_RAND|  rw  | 0x0 |  — |
|  14 |   RD_EN  |  rw  | 0x0 |  — |
|  15 |   WR_EN  |  rw  | 0x0 |  — |
|  16 |    SB    |  rw  | 0x0 |  — |
|23:20|POISON_LG2|  rw  | 0x0 |  — |
|  24 |  ATOMIC  |  rw  | 0x0 |  — |
|  25 |    MTE   |  rw  | 0x0 |  — |
|  26 |    MEM   |  rw  | 0x0 |  — |

#### SIZE_MIN field

<p>Smallest AxSIZE.</p>

#### SIZE_MAX field

<p>Largest AxSIZE (clamped to the bus).</p>

#### BURST_MASK field

<p>Burst types allowed: [0] FIXED [1] INCR [2] WRAP.</p>

#### UNALIGNED field

<p>INCR/FIXED may start off the size grid.</p>

#### STRB_RAND field

<p>Writes clear random strobes.</p>

#### RD_EN field

<p>Reads target this window.</p>

#### WR_EN field

<p>Writes target this window.</p>

#### SB field

<p>AXI5: BTRACE / RTRACE must echo the request's TRACE (the bridge echoes it at a trace-capable master port whatever the slave); else they must be 0.</p>

#### POISON_LG2 field

<p>AXI5: W beats poisoned, and R beats expected poisoned, 1 in 2^n by address; 0 = never. Set only on a poison path, to the slave's POISON_LG2.</p>

#### ATOMIC field

<p>AXI5: the path to this window carries atomics (both ends AXI5 with atomic), so writes to it may become atomics (WR_ATOM).</p>

#### MTE field

<p>AXI5 MTE: the far end of this window answers tags (both ends MTE), so RTAG / BTAGMATCH are checked against the tag contract; else they must be 0 (a fabric's own DECERR answers no tags).</p>

#### MEM field

<p>A real memory: it returns what was written. Writes carry the value a read expects, f_word(f_maddr(address), TAG, RD), so contents stay checkable whatever order writes land in; the window must be filled (FILL) before it is read.</p>

## WIN register file

- Absolute Address: 0x110
- Base Offset: 0x100
- Size: 0xC
- Array Dimensions: [8]
- Array Stride: 0x10
- Total Size: 0x80

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   BASE   |  — |
|  0x4 |   CFG0   |  — |
|  0x8 |   CFG1   |  — |

### BASE register

- Absolute Address: 0x110
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

#### VALUE field

<p>Window base (aligned to its size).</p>

### CFG0 register

- Absolute Address: 0x114
- Base Offset: 0x4
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 5:0 | SIZE_LG2 |  rw  | 0x0 |  — |
| 7:6 |   RESP   |  rw  | 0x0 |  — |
| 15:8|    TAG   |  rw  | 0x0 |  — |
|23:16| LEN_MASK |  rw  | 0x0 |  — |

#### SIZE_LG2 field

<p>Window = 2^SIZE_LG2 bytes (&gt;= the bus width).</p>

#### RESP field

<p>Response every access must get: 0 OKAY, 2 SLVERR, 3 DECERR.</p>

#### TAG field

<p>Tag of the slave owning the window (folds into its data).</p>

#### LEN_MASK field

<p>AxLEN = random &amp; LEN_MASK (15 for an AXI3 path, 0 for single-beat protocols).</p>

### CFG1 register

- Absolute Address: 0x118
- Base Offset: 0x8
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 2:0 | SIZE_MIN |  rw  | 0x0 |  — |
| 6:4 | SIZE_MAX |  rw  | 0x7 |  — |
| 10:8|BURST_MASK|  rw  | 0x2 |  — |
|  12 | UNALIGNED|  rw  | 0x0 |  — |
|  13 | STRB_RAND|  rw  | 0x0 |  — |
|  14 |   RD_EN  |  rw  | 0x0 |  — |
|  15 |   WR_EN  |  rw  | 0x0 |  — |
|  16 |    SB    |  rw  | 0x0 |  — |
|23:20|POISON_LG2|  rw  | 0x0 |  — |
|  24 |  ATOMIC  |  rw  | 0x0 |  — |
|  25 |    MTE   |  rw  | 0x0 |  — |
|  26 |    MEM   |  rw  | 0x0 |  — |

#### SIZE_MIN field

<p>Smallest AxSIZE.</p>

#### SIZE_MAX field

<p>Largest AxSIZE (clamped to the bus).</p>

#### BURST_MASK field

<p>Burst types allowed: [0] FIXED [1] INCR [2] WRAP.</p>

#### UNALIGNED field

<p>INCR/FIXED may start off the size grid.</p>

#### STRB_RAND field

<p>Writes clear random strobes.</p>

#### RD_EN field

<p>Reads target this window.</p>

#### WR_EN field

<p>Writes target this window.</p>

#### SB field

<p>AXI5: BTRACE / RTRACE must echo the request's TRACE (the bridge echoes it at a trace-capable master port whatever the slave); else they must be 0.</p>

#### POISON_LG2 field

<p>AXI5: W beats poisoned, and R beats expected poisoned, 1 in 2^n by address; 0 = never. Set only on a poison path, to the slave's POISON_LG2.</p>

#### ATOMIC field

<p>AXI5: the path to this window carries atomics (both ends AXI5 with atomic), so writes to it may become atomics (WR_ATOM).</p>

#### MTE field

<p>AXI5 MTE: the far end of this window answers tags (both ends MTE), so RTAG / BTAGMATCH are checked against the tag contract; else they must be 0 (a fabric's own DECERR answers no tags).</p>

#### MEM field

<p>A real memory: it returns what was written. Writes carry the value a read expects, f_word(f_maddr(address), TAG, RD), so contents stay checkable whatever order writes land in; the window must be filled (FILL) before it is read.</p>

## WIN register file

- Absolute Address: 0x120
- Base Offset: 0x100
- Size: 0xC
- Array Dimensions: [8]
- Array Stride: 0x10
- Total Size: 0x80

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   BASE   |  — |
|  0x4 |   CFG0   |  — |
|  0x8 |   CFG1   |  — |

### BASE register

- Absolute Address: 0x120
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

#### VALUE field

<p>Window base (aligned to its size).</p>

### CFG0 register

- Absolute Address: 0x124
- Base Offset: 0x4
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 5:0 | SIZE_LG2 |  rw  | 0x0 |  — |
| 7:6 |   RESP   |  rw  | 0x0 |  — |
| 15:8|    TAG   |  rw  | 0x0 |  — |
|23:16| LEN_MASK |  rw  | 0x0 |  — |

#### SIZE_LG2 field

<p>Window = 2^SIZE_LG2 bytes (&gt;= the bus width).</p>

#### RESP field

<p>Response every access must get: 0 OKAY, 2 SLVERR, 3 DECERR.</p>

#### TAG field

<p>Tag of the slave owning the window (folds into its data).</p>

#### LEN_MASK field

<p>AxLEN = random &amp; LEN_MASK (15 for an AXI3 path, 0 for single-beat protocols).</p>

### CFG1 register

- Absolute Address: 0x128
- Base Offset: 0x8
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 2:0 | SIZE_MIN |  rw  | 0x0 |  — |
| 6:4 | SIZE_MAX |  rw  | 0x7 |  — |
| 10:8|BURST_MASK|  rw  | 0x2 |  — |
|  12 | UNALIGNED|  rw  | 0x0 |  — |
|  13 | STRB_RAND|  rw  | 0x0 |  — |
|  14 |   RD_EN  |  rw  | 0x0 |  — |
|  15 |   WR_EN  |  rw  | 0x0 |  — |
|  16 |    SB    |  rw  | 0x0 |  — |
|23:20|POISON_LG2|  rw  | 0x0 |  — |
|  24 |  ATOMIC  |  rw  | 0x0 |  — |
|  25 |    MTE   |  rw  | 0x0 |  — |
|  26 |    MEM   |  rw  | 0x0 |  — |

#### SIZE_MIN field

<p>Smallest AxSIZE.</p>

#### SIZE_MAX field

<p>Largest AxSIZE (clamped to the bus).</p>

#### BURST_MASK field

<p>Burst types allowed: [0] FIXED [1] INCR [2] WRAP.</p>

#### UNALIGNED field

<p>INCR/FIXED may start off the size grid.</p>

#### STRB_RAND field

<p>Writes clear random strobes.</p>

#### RD_EN field

<p>Reads target this window.</p>

#### WR_EN field

<p>Writes target this window.</p>

#### SB field

<p>AXI5: BTRACE / RTRACE must echo the request's TRACE (the bridge echoes it at a trace-capable master port whatever the slave); else they must be 0.</p>

#### POISON_LG2 field

<p>AXI5: W beats poisoned, and R beats expected poisoned, 1 in 2^n by address; 0 = never. Set only on a poison path, to the slave's POISON_LG2.</p>

#### ATOMIC field

<p>AXI5: the path to this window carries atomics (both ends AXI5 with atomic), so writes to it may become atomics (WR_ATOM).</p>

#### MTE field

<p>AXI5 MTE: the far end of this window answers tags (both ends MTE), so RTAG / BTAGMATCH are checked against the tag contract; else they must be 0 (a fabric's own DECERR answers no tags).</p>

#### MEM field

<p>A real memory: it returns what was written. Writes carry the value a read expects, f_word(f_maddr(address), TAG, RD), so contents stay checkable whatever order writes land in; the window must be filled (FILL) before it is read.</p>

## WIN register file

- Absolute Address: 0x130
- Base Offset: 0x100
- Size: 0xC
- Array Dimensions: [8]
- Array Stride: 0x10
- Total Size: 0x80

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   BASE   |  — |
|  0x4 |   CFG0   |  — |
|  0x8 |   CFG1   |  — |

### BASE register

- Absolute Address: 0x130
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

#### VALUE field

<p>Window base (aligned to its size).</p>

### CFG0 register

- Absolute Address: 0x134
- Base Offset: 0x4
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 5:0 | SIZE_LG2 |  rw  | 0x0 |  — |
| 7:6 |   RESP   |  rw  | 0x0 |  — |
| 15:8|    TAG   |  rw  | 0x0 |  — |
|23:16| LEN_MASK |  rw  | 0x0 |  — |

#### SIZE_LG2 field

<p>Window = 2^SIZE_LG2 bytes (&gt;= the bus width).</p>

#### RESP field

<p>Response every access must get: 0 OKAY, 2 SLVERR, 3 DECERR.</p>

#### TAG field

<p>Tag of the slave owning the window (folds into its data).</p>

#### LEN_MASK field

<p>AxLEN = random &amp; LEN_MASK (15 for an AXI3 path, 0 for single-beat protocols).</p>

### CFG1 register

- Absolute Address: 0x138
- Base Offset: 0x8
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 2:0 | SIZE_MIN |  rw  | 0x0 |  — |
| 6:4 | SIZE_MAX |  rw  | 0x7 |  — |
| 10:8|BURST_MASK|  rw  | 0x2 |  — |
|  12 | UNALIGNED|  rw  | 0x0 |  — |
|  13 | STRB_RAND|  rw  | 0x0 |  — |
|  14 |   RD_EN  |  rw  | 0x0 |  — |
|  15 |   WR_EN  |  rw  | 0x0 |  — |
|  16 |    SB    |  rw  | 0x0 |  — |
|23:20|POISON_LG2|  rw  | 0x0 |  — |
|  24 |  ATOMIC  |  rw  | 0x0 |  — |
|  25 |    MTE   |  rw  | 0x0 |  — |
|  26 |    MEM   |  rw  | 0x0 |  — |

#### SIZE_MIN field

<p>Smallest AxSIZE.</p>

#### SIZE_MAX field

<p>Largest AxSIZE (clamped to the bus).</p>

#### BURST_MASK field

<p>Burst types allowed: [0] FIXED [1] INCR [2] WRAP.</p>

#### UNALIGNED field

<p>INCR/FIXED may start off the size grid.</p>

#### STRB_RAND field

<p>Writes clear random strobes.</p>

#### RD_EN field

<p>Reads target this window.</p>

#### WR_EN field

<p>Writes target this window.</p>

#### SB field

<p>AXI5: BTRACE / RTRACE must echo the request's TRACE (the bridge echoes it at a trace-capable master port whatever the slave); else they must be 0.</p>

#### POISON_LG2 field

<p>AXI5: W beats poisoned, and R beats expected poisoned, 1 in 2^n by address; 0 = never. Set only on a poison path, to the slave's POISON_LG2.</p>

#### ATOMIC field

<p>AXI5: the path to this window carries atomics (both ends AXI5 with atomic), so writes to it may become atomics (WR_ATOM).</p>

#### MTE field

<p>AXI5 MTE: the far end of this window answers tags (both ends MTE), so RTAG / BTAGMATCH are checked against the tag contract; else they must be 0 (a fabric's own DECERR answers no tags).</p>

#### MEM field

<p>A real memory: it returns what was written. Writes carry the value a read expects, f_word(f_maddr(address), TAG, RD), so contents stay checkable whatever order writes land in; the window must be filled (FILL) before it is read.</p>

## WIN register file

- Absolute Address: 0x140
- Base Offset: 0x100
- Size: 0xC
- Array Dimensions: [8]
- Array Stride: 0x10
- Total Size: 0x80

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   BASE   |  — |
|  0x4 |   CFG0   |  — |
|  0x8 |   CFG1   |  — |

### BASE register

- Absolute Address: 0x140
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

#### VALUE field

<p>Window base (aligned to its size).</p>

### CFG0 register

- Absolute Address: 0x144
- Base Offset: 0x4
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 5:0 | SIZE_LG2 |  rw  | 0x0 |  — |
| 7:6 |   RESP   |  rw  | 0x0 |  — |
| 15:8|    TAG   |  rw  | 0x0 |  — |
|23:16| LEN_MASK |  rw  | 0x0 |  — |

#### SIZE_LG2 field

<p>Window = 2^SIZE_LG2 bytes (&gt;= the bus width).</p>

#### RESP field

<p>Response every access must get: 0 OKAY, 2 SLVERR, 3 DECERR.</p>

#### TAG field

<p>Tag of the slave owning the window (folds into its data).</p>

#### LEN_MASK field

<p>AxLEN = random &amp; LEN_MASK (15 for an AXI3 path, 0 for single-beat protocols).</p>

### CFG1 register

- Absolute Address: 0x148
- Base Offset: 0x8
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 2:0 | SIZE_MIN |  rw  | 0x0 |  — |
| 6:4 | SIZE_MAX |  rw  | 0x7 |  — |
| 10:8|BURST_MASK|  rw  | 0x2 |  — |
|  12 | UNALIGNED|  rw  | 0x0 |  — |
|  13 | STRB_RAND|  rw  | 0x0 |  — |
|  14 |   RD_EN  |  rw  | 0x0 |  — |
|  15 |   WR_EN  |  rw  | 0x0 |  — |
|  16 |    SB    |  rw  | 0x0 |  — |
|23:20|POISON_LG2|  rw  | 0x0 |  — |
|  24 |  ATOMIC  |  rw  | 0x0 |  — |
|  25 |    MTE   |  rw  | 0x0 |  — |
|  26 |    MEM   |  rw  | 0x0 |  — |

#### SIZE_MIN field

<p>Smallest AxSIZE.</p>

#### SIZE_MAX field

<p>Largest AxSIZE (clamped to the bus).</p>

#### BURST_MASK field

<p>Burst types allowed: [0] FIXED [1] INCR [2] WRAP.</p>

#### UNALIGNED field

<p>INCR/FIXED may start off the size grid.</p>

#### STRB_RAND field

<p>Writes clear random strobes.</p>

#### RD_EN field

<p>Reads target this window.</p>

#### WR_EN field

<p>Writes target this window.</p>

#### SB field

<p>AXI5: BTRACE / RTRACE must echo the request's TRACE (the bridge echoes it at a trace-capable master port whatever the slave); else they must be 0.</p>

#### POISON_LG2 field

<p>AXI5: W beats poisoned, and R beats expected poisoned, 1 in 2^n by address; 0 = never. Set only on a poison path, to the slave's POISON_LG2.</p>

#### ATOMIC field

<p>AXI5: the path to this window carries atomics (both ends AXI5 with atomic), so writes to it may become atomics (WR_ATOM).</p>

#### MTE field

<p>AXI5 MTE: the far end of this window answers tags (both ends MTE), so RTAG / BTAGMATCH are checked against the tag contract; else they must be 0 (a fabric's own DECERR answers no tags).</p>

#### MEM field

<p>A real memory: it returns what was written. Writes carry the value a read expects, f_word(f_maddr(address), TAG, RD), so contents stay checkable whatever order writes land in; the window must be filled (FILL) before it is read.</p>

## WIN register file

- Absolute Address: 0x150
- Base Offset: 0x100
- Size: 0xC
- Array Dimensions: [8]
- Array Stride: 0x10
- Total Size: 0x80

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   BASE   |  — |
|  0x4 |   CFG0   |  — |
|  0x8 |   CFG1   |  — |

### BASE register

- Absolute Address: 0x150
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

#### VALUE field

<p>Window base (aligned to its size).</p>

### CFG0 register

- Absolute Address: 0x154
- Base Offset: 0x4
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 5:0 | SIZE_LG2 |  rw  | 0x0 |  — |
| 7:6 |   RESP   |  rw  | 0x0 |  — |
| 15:8|    TAG   |  rw  | 0x0 |  — |
|23:16| LEN_MASK |  rw  | 0x0 |  — |

#### SIZE_LG2 field

<p>Window = 2^SIZE_LG2 bytes (&gt;= the bus width).</p>

#### RESP field

<p>Response every access must get: 0 OKAY, 2 SLVERR, 3 DECERR.</p>

#### TAG field

<p>Tag of the slave owning the window (folds into its data).</p>

#### LEN_MASK field

<p>AxLEN = random &amp; LEN_MASK (15 for an AXI3 path, 0 for single-beat protocols).</p>

### CFG1 register

- Absolute Address: 0x158
- Base Offset: 0x8
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 2:0 | SIZE_MIN |  rw  | 0x0 |  — |
| 6:4 | SIZE_MAX |  rw  | 0x7 |  — |
| 10:8|BURST_MASK|  rw  | 0x2 |  — |
|  12 | UNALIGNED|  rw  | 0x0 |  — |
|  13 | STRB_RAND|  rw  | 0x0 |  — |
|  14 |   RD_EN  |  rw  | 0x0 |  — |
|  15 |   WR_EN  |  rw  | 0x0 |  — |
|  16 |    SB    |  rw  | 0x0 |  — |
|23:20|POISON_LG2|  rw  | 0x0 |  — |
|  24 |  ATOMIC  |  rw  | 0x0 |  — |
|  25 |    MTE   |  rw  | 0x0 |  — |
|  26 |    MEM   |  rw  | 0x0 |  — |

#### SIZE_MIN field

<p>Smallest AxSIZE.</p>

#### SIZE_MAX field

<p>Largest AxSIZE (clamped to the bus).</p>

#### BURST_MASK field

<p>Burst types allowed: [0] FIXED [1] INCR [2] WRAP.</p>

#### UNALIGNED field

<p>INCR/FIXED may start off the size grid.</p>

#### STRB_RAND field

<p>Writes clear random strobes.</p>

#### RD_EN field

<p>Reads target this window.</p>

#### WR_EN field

<p>Writes target this window.</p>

#### SB field

<p>AXI5: BTRACE / RTRACE must echo the request's TRACE (the bridge echoes it at a trace-capable master port whatever the slave); else they must be 0.</p>

#### POISON_LG2 field

<p>AXI5: W beats poisoned, and R beats expected poisoned, 1 in 2^n by address; 0 = never. Set only on a poison path, to the slave's POISON_LG2.</p>

#### ATOMIC field

<p>AXI5: the path to this window carries atomics (both ends AXI5 with atomic), so writes to it may become atomics (WR_ATOM).</p>

#### MTE field

<p>AXI5 MTE: the far end of this window answers tags (both ends MTE), so RTAG / BTAGMATCH are checked against the tag contract; else they must be 0 (a fabric's own DECERR answers no tags).</p>

#### MEM field

<p>A real memory: it returns what was written. Writes carry the value a read expects, f_word(f_maddr(address), TAG, RD), so contents stay checkable whatever order writes land in; the window must be filled (FILL) before it is read.</p>

## WIN register file

- Absolute Address: 0x160
- Base Offset: 0x100
- Size: 0xC
- Array Dimensions: [8]
- Array Stride: 0x10
- Total Size: 0x80

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   BASE   |  — |
|  0x4 |   CFG0   |  — |
|  0x8 |   CFG1   |  — |

### BASE register

- Absolute Address: 0x160
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

#### VALUE field

<p>Window base (aligned to its size).</p>

### CFG0 register

- Absolute Address: 0x164
- Base Offset: 0x4
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 5:0 | SIZE_LG2 |  rw  | 0x0 |  — |
| 7:6 |   RESP   |  rw  | 0x0 |  — |
| 15:8|    TAG   |  rw  | 0x0 |  — |
|23:16| LEN_MASK |  rw  | 0x0 |  — |

#### SIZE_LG2 field

<p>Window = 2^SIZE_LG2 bytes (&gt;= the bus width).</p>

#### RESP field

<p>Response every access must get: 0 OKAY, 2 SLVERR, 3 DECERR.</p>

#### TAG field

<p>Tag of the slave owning the window (folds into its data).</p>

#### LEN_MASK field

<p>AxLEN = random &amp; LEN_MASK (15 for an AXI3 path, 0 for single-beat protocols).</p>

### CFG1 register

- Absolute Address: 0x168
- Base Offset: 0x8
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 2:0 | SIZE_MIN |  rw  | 0x0 |  — |
| 6:4 | SIZE_MAX |  rw  | 0x7 |  — |
| 10:8|BURST_MASK|  rw  | 0x2 |  — |
|  12 | UNALIGNED|  rw  | 0x0 |  — |
|  13 | STRB_RAND|  rw  | 0x0 |  — |
|  14 |   RD_EN  |  rw  | 0x0 |  — |
|  15 |   WR_EN  |  rw  | 0x0 |  — |
|  16 |    SB    |  rw  | 0x0 |  — |
|23:20|POISON_LG2|  rw  | 0x0 |  — |
|  24 |  ATOMIC  |  rw  | 0x0 |  — |
|  25 |    MTE   |  rw  | 0x0 |  — |
|  26 |    MEM   |  rw  | 0x0 |  — |

#### SIZE_MIN field

<p>Smallest AxSIZE.</p>

#### SIZE_MAX field

<p>Largest AxSIZE (clamped to the bus).</p>

#### BURST_MASK field

<p>Burst types allowed: [0] FIXED [1] INCR [2] WRAP.</p>

#### UNALIGNED field

<p>INCR/FIXED may start off the size grid.</p>

#### STRB_RAND field

<p>Writes clear random strobes.</p>

#### RD_EN field

<p>Reads target this window.</p>

#### WR_EN field

<p>Writes target this window.</p>

#### SB field

<p>AXI5: BTRACE / RTRACE must echo the request's TRACE (the bridge echoes it at a trace-capable master port whatever the slave); else they must be 0.</p>

#### POISON_LG2 field

<p>AXI5: W beats poisoned, and R beats expected poisoned, 1 in 2^n by address; 0 = never. Set only on a poison path, to the slave's POISON_LG2.</p>

#### ATOMIC field

<p>AXI5: the path to this window carries atomics (both ends AXI5 with atomic), so writes to it may become atomics (WR_ATOM).</p>

#### MTE field

<p>AXI5 MTE: the far end of this window answers tags (both ends MTE), so RTAG / BTAGMATCH are checked against the tag contract; else they must be 0 (a fabric's own DECERR answers no tags).</p>

#### MEM field

<p>A real memory: it returns what was written. Writes carry the value a read expects, f_word(f_maddr(address), TAG, RD), so contents stay checkable whatever order writes land in; the window must be filled (FILL) before it is read.</p>

## WIN register file

- Absolute Address: 0x170
- Base Offset: 0x100
- Size: 0xC
- Array Dimensions: [8]
- Array Stride: 0x10
- Total Size: 0x80

|Offset|Identifier|Name|
|------|----------|----|
|  0x0 |   BASE   |  — |
|  0x4 |   CFG0   |  — |
|  0x8 |   CFG1   |  — |

### BASE register

- Absolute Address: 0x170
- Base Offset: 0x0
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

#### VALUE field

<p>Window base (aligned to its size).</p>

### CFG0 register

- Absolute Address: 0x174
- Base Offset: 0x4
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 5:0 | SIZE_LG2 |  rw  | 0x0 |  — |
| 7:6 |   RESP   |  rw  | 0x0 |  — |
| 15:8|    TAG   |  rw  | 0x0 |  — |
|23:16| LEN_MASK |  rw  | 0x0 |  — |

#### SIZE_LG2 field

<p>Window = 2^SIZE_LG2 bytes (&gt;= the bus width).</p>

#### RESP field

<p>Response every access must get: 0 OKAY, 2 SLVERR, 3 DECERR.</p>

#### TAG field

<p>Tag of the slave owning the window (folds into its data).</p>

#### LEN_MASK field

<p>AxLEN = random &amp; LEN_MASK (15 for an AXI3 path, 0 for single-beat protocols).</p>

### CFG1 register

- Absolute Address: 0x178
- Base Offset: 0x8
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 2:0 | SIZE_MIN |  rw  | 0x0 |  — |
| 6:4 | SIZE_MAX |  rw  | 0x7 |  — |
| 10:8|BURST_MASK|  rw  | 0x2 |  — |
|  12 | UNALIGNED|  rw  | 0x0 |  — |
|  13 | STRB_RAND|  rw  | 0x0 |  — |
|  14 |   RD_EN  |  rw  | 0x0 |  — |
|  15 |   WR_EN  |  rw  | 0x0 |  — |
|  16 |    SB    |  rw  | 0x0 |  — |
|23:20|POISON_LG2|  rw  | 0x0 |  — |
|  24 |  ATOMIC  |  rw  | 0x0 |  — |
|  25 |    MTE   |  rw  | 0x0 |  — |
|  26 |    MEM   |  rw  | 0x0 |  — |

#### SIZE_MIN field

<p>Smallest AxSIZE.</p>

#### SIZE_MAX field

<p>Largest AxSIZE (clamped to the bus).</p>

#### BURST_MASK field

<p>Burst types allowed: [0] FIXED [1] INCR [2] WRAP.</p>

#### UNALIGNED field

<p>INCR/FIXED may start off the size grid.</p>

#### STRB_RAND field

<p>Writes clear random strobes.</p>

#### RD_EN field

<p>Reads target this window.</p>

#### WR_EN field

<p>Writes target this window.</p>

#### SB field

<p>AXI5: BTRACE / RTRACE must echo the request's TRACE (the bridge echoes it at a trace-capable master port whatever the slave); else they must be 0.</p>

#### POISON_LG2 field

<p>AXI5: W beats poisoned, and R beats expected poisoned, 1 in 2^n by address; 0 = never. Set only on a poison path, to the slave's POISON_LG2.</p>

#### ATOMIC field

<p>AXI5: the path to this window carries atomics (both ends AXI5 with atomic), so writes to it may become atomics (WR_ATOM).</p>

#### MTE field

<p>AXI5 MTE: the far end of this window answers tags (both ends MTE), so RTAG / BTAGMATCH are checked against the tag contract; else they must be 0 (a fabric's own DECERR answers no tags).</p>

#### MEM field

<p>A real memory: it returns what was written. Writes carry the value a read expects, f_word(f_maddr(address), TAG, RD), so contents stay checkable whatever order writes land in; the window must be filled (FILL) before it is read.</p>

### RD_STATUS register

- Absolute Address: 0x200
- Base Offset: 0x200
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
|  0  |   BUSY   |   r  | 0x0 |  — |
|  1  |   DONE   |   r  | 0x0 |  — |
|  2  | FE_VALID |   r  | 0x0 |  — |
| 7:4 |  FE_KIND |   r  | 0x0 |  — |
| 15:8|   RUNS   |   r  | 0x0 |  — |
|23:16|  OUT_NOW |   r  | 0x0 |  — |
|31:24|  OUT_MAX |   r  | 0x0 |  — |

#### BUSY field

<p>Running (or draining).</p>

#### DONE field

<p>Run complete: budget issued and every burst retired.</p>

#### FE_VALID field

<p>A first error is captured in FE_*.</p>

#### FE_KIND field

<p>ERR_* code of the first error.</p>

#### RUNS field

<p>GOs this direction has taken (wraps): equal to the control block's GO_COUNT when it ran every run.</p>

#### OUT_NOW field

<p>Bursts outstanding now.</p>

#### OUT_MAX field

<p>Most bursts outstanding this run.</p>

### RD_ISSUED register

- Absolute Address: 0x204
- Base Offset: 0x204
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### RD_COMPLETED register

- Absolute Address: 0x208
- Base Offset: 0x208
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### RD_BEATS register

- Absolute Address: 0x20C
- Base Offset: 0x20C
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### RD_ERR register

- Absolute Address: 0x210
- Base Offset: 0x210
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|   MASK   |   r  | 0x0 |  — |
|31:16|   COUNT  |   r  | 0x0 |  — |

#### MASK field

<p>Sticky, one bit per ERR_* code.</p>

#### COUNT field

<p>Errors counted (saturating).</p>

### RD_FE_ID register

- Absolute Address: 0x214
- Base Offset: 0x214
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|15:0|   VALUE  |   r  | 0x0 |  — |

### RD_FE_ADDR register

- Absolute Address: 0x218
- Base Offset: 0x218
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### RD_FE_EXP register

- Absolute Address: 0x21C
- Base Offset: 0x21C
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### RD_FE_ACT register

- Absolute Address: 0x220
- Base Offset: 0x220
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### RD_LAT_MAX register

- Absolute Address: 0x224
- Base Offset: 0x224
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### RD_LAT_SUM register

- Absolute Address: 0x228
- Base Offset: 0x228
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_STATUS register

- Absolute Address: 0x240
- Base Offset: 0x240
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
|  0  |   BUSY   |   r  | 0x0 |  — |
|  1  |   DONE   |   r  | 0x0 |  — |
|  2  | FE_VALID |   r  | 0x0 |  — |
| 7:4 |  FE_KIND |   r  | 0x0 |  — |
| 15:8|   RUNS   |   r  | 0x0 |  — |
|23:16|  OUT_NOW |   r  | 0x0 |  — |
|31:24|  OUT_MAX |   r  | 0x0 |  — |

#### BUSY field

<p>Running (or draining).</p>

#### DONE field

<p>Run complete: budget issued and every burst retired.</p>

#### FE_VALID field

<p>A first error is captured in FE_*.</p>

#### FE_KIND field

<p>ERR_* code of the first error.</p>

#### RUNS field

<p>GOs this direction has taken (wraps): equal to the control block's GO_COUNT when it ran every run.</p>

#### OUT_NOW field

<p>Bursts outstanding now.</p>

#### OUT_MAX field

<p>Most bursts outstanding this run.</p>

### WR_ISSUED register

- Absolute Address: 0x244
- Base Offset: 0x244
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_COMPLETED register

- Absolute Address: 0x248
- Base Offset: 0x248
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_BEATS register

- Absolute Address: 0x24C
- Base Offset: 0x24C
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_ERR register

- Absolute Address: 0x250
- Base Offset: 0x250
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|   MASK   |   r  | 0x0 |  — |
|31:16|   COUNT  |   r  | 0x0 |  — |

#### MASK field

<p>Sticky, one bit per ERR_* code.</p>

#### COUNT field

<p>Errors counted (saturating).</p>

### WR_FE_ID register

- Absolute Address: 0x254
- Base Offset: 0x254
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|15:0|   VALUE  |   r  | 0x0 |  — |

### WR_FE_ADDR register

- Absolute Address: 0x258
- Base Offset: 0x258
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_FE_EXP register

- Absolute Address: 0x25C
- Base Offset: 0x25C
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_FE_ACT register

- Absolute Address: 0x260
- Base Offset: 0x260
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_LAT_MAX register

- Absolute Address: 0x264
- Base Offset: 0x264
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_LAT_SUM register

- Absolute Address: 0x268
- Base Offset: 0x268
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |
