<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## bstress_slv_regs address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x260

<p>Configuration and status of one bus-stress slave</p>

|Offset| Identifier|Name|
|------|-----------|----|
| 0x000|     ID    |  — |
| 0x004|   PARAMS  |  — |
| 0x010|  RD_BASE  |  — |
| 0x014|  RD_CTRL  |  — |
| 0x018|RD_ERR_BASE|  — |
| 0x01C|RD_ERR_MASK|  — |
| 0x020| RD_TIMING |  — |
| 0x024|  RD_SEED  |  — |
| 0x028|   RD_SB   |  — |
| 0x030|  WR_BASE  |  — |
| 0x034|  WR_CTRL  |  — |
| 0x038|WR_ERR_BASE|  — |
| 0x03C|WR_ERR_MASK|  — |
| 0x040| WR_TIMING |  — |
| 0x044|  WR_SEED  |  — |
| 0x048|   WR_SB   |  — |
| 0x200| RD_BURSTS |  — |
| 0x204|  RD_BEATS |  — |
| 0x208|   RD_ERR  |  — |
| 0x20C|   RD_FE   |  — |
| 0x210| RD_FE_ADDR|  — |
| 0x214| RD_FE_EXP |  — |
| 0x218| RD_FE_ACT |  — |
| 0x21C|   RD_OUT  |  — |
| 0x240| WR_BURSTS |  — |
| 0x244|  WR_BEATS |  — |
| 0x248|   WR_ERR  |  — |
| 0x24C|   WR_FE   |  — |
| 0x250| WR_FE_ADDR|  — |
| 0x254| WR_FE_EXP |  — |
| 0x258| WR_FE_ACT |  — |
| 0x25C|   WR_OUT  |  — |

### ID register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>Identity: 0x5353 ('SS') and the build parameters.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | BUS_BYTES|   r  | 0x0 |  — |
| 12:8| ID_WIDTH |   r  | 0x0 |  — |
|15:13| PROTOCOL |   r  | 0x0 |  — |
|31:16|   MAGIC  |   r  | 0x0 |  — |

#### BUS_BYTES field

<p>Data width / 8.</p>

#### ID_WIDTH field

<p>AXI ID width.</p>

#### PROTOCOL field

<p>Protocol (as bstress_mst_regs.ID.PROTOCOL).</p>

#### MAGIC field

<p>Constant 0x5353.</p>

### PARAMS register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |   DEPTH  |   r  | 0x0 |  — |
|  12 |  HAS_RD  |   r  | 0x0 |  — |
|  13 |  HAS_WR  |   r  | 0x0 |  — |
|19:16|   INDEX  |   r  | 0x0 |  — |

#### DEPTH field

<p>Requests held per direction, as built.</p>

#### HAS_RD field

<p>Read direction built.</p>

#### HAS_WR field

<p>Write direction built.</p>

#### INDEX field

<p>Index of this slave in the harness.</p>

### RD_BASE register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### RD_CTRL register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

| Bits|  Identifier |Access|Reset|Name|
|-----|-------------|------|-----|----|
| 5:0 |   SIZE_LG2  |  rw  | 0x0 |  — |
|  6  | OFFSET_MODE |  rw  | 0x0 |  — |
|  7  |    ERR_EN   |  rw  | 0x0 |  — |
| 15:8|     TAG     |  rw  | 0x0 |  — |
|  16 |   INORDER   |  rw  | 0x0 |  — |
|  17 |  INTERLEAVE |  rw  | 0x0 |  — |
|  18 |   W_FIRST   |  rw  | 0x0 |  — |
|23:20| REQ_THROTTLE|  rw  | 0x0 |  — |
|27:24|DATA_THROTTLE|  rw  | 0x0 |  — |

#### SIZE_LG2 field

<p>Window = 2^SIZE_LG2 bytes; a request outside is ERR_S_ADDR.</p>

#### OFFSET_MODE field

<p>The port carries an offset into the window (APB); the fabric address is BASE | offset.</p>

#### ERR_EN field

<p>(A &amp; ERR_MASK) == ERR_BASE answers SLVERR.</p>

#### TAG field

<p>Tag folded into this slave's data.</p>

#### INORDER field

<p>Complete in request order across IDs (required behind a FIFO-tracked bridge slave port).</p>

#### INTERLEAVE field

<p>Read: switch bursts between beats.</p>

#### W_FIRST field

<p>Write: AWREADY only while WVALID is up -- the slave waits for write data before it takes the address, as AXI A3.3.1 allows (an AXI CDMA register slave does). A fabric that holds WVALID until AWREADY deadlocks against it (bridge BUG-020).</p>

#### REQ_THROTTLE field

<p>AxREADY low with probability n/16.</p>

#### DATA_THROTTLE field

<p>WREADY low / an R bubble with probability n/16.</p>

### RD_ERR_BASE register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### RD_ERR_MASK register

- Absolute Address: 0x1C
- Base Offset: 0x1C
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### RD_TIMING register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  LAT_MIN |  rw  | 0x0 |  — |
| 15:8| LAT_MASK |  rw  | 0x0 |  — |
|23:16|  MAX_OUT |  rw  | 0x0 |  — |

#### LAT_MIN field

<p>Cycles before a request may answer ...</p>

#### LAT_MASK field

<p>... plus random &amp; LAT_MASK.</p>

#### MAX_OUT field

<p>Requests held; 0 = as built.</p>

### RD_SEED register

- Absolute Address: 0x24
- Base Offset: 0x24
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### RD_SB register

- Absolute Address: 0x28
- Base Offset: 0x28
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|    SRC   |  rw  | 0x0 |  — |
|11:8|POISON_LG2|  rw  | 0x0 |  — |

#### SRC field

<p>AXI5: bit i set = requests from master index i (the fabric's ID prefix) carry sideband natively and must match f_sb; from any other master the sideband must be 0.</p>

#### POISON_LG2 field

<p>AXI5: R beats poisoned, and W beats expected poisoned, 1 in 2^n by address; 0 = never.</p>

### WR_BASE register

- Absolute Address: 0x30
- Base Offset: 0x30
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### WR_CTRL register

- Absolute Address: 0x34
- Base Offset: 0x34
- Size: 0x4

| Bits|  Identifier |Access|Reset|Name|
|-----|-------------|------|-----|----|
| 5:0 |   SIZE_LG2  |  rw  | 0x0 |  — |
|  6  | OFFSET_MODE |  rw  | 0x0 |  — |
|  7  |    ERR_EN   |  rw  | 0x0 |  — |
| 15:8|     TAG     |  rw  | 0x0 |  — |
|  16 |   INORDER   |  rw  | 0x0 |  — |
|  17 |  INTERLEAVE |  rw  | 0x0 |  — |
|  18 |   W_FIRST   |  rw  | 0x0 |  — |
|23:20| REQ_THROTTLE|  rw  | 0x0 |  — |
|27:24|DATA_THROTTLE|  rw  | 0x0 |  — |

#### SIZE_LG2 field

<p>Window = 2^SIZE_LG2 bytes; a request outside is ERR_S_ADDR.</p>

#### OFFSET_MODE field

<p>The port carries an offset into the window (APB); the fabric address is BASE | offset.</p>

#### ERR_EN field

<p>(A &amp; ERR_MASK) == ERR_BASE answers SLVERR.</p>

#### TAG field

<p>Tag folded into this slave's data.</p>

#### INORDER field

<p>Complete in request order across IDs (required behind a FIFO-tracked bridge slave port).</p>

#### INTERLEAVE field

<p>Read: switch bursts between beats.</p>

#### W_FIRST field

<p>Write: AWREADY only while WVALID is up -- the slave waits for write data before it takes the address, as AXI A3.3.1 allows (an AXI CDMA register slave does). A fabric that holds WVALID until AWREADY deadlocks against it (bridge BUG-020).</p>

#### REQ_THROTTLE field

<p>AxREADY low with probability n/16.</p>

#### DATA_THROTTLE field

<p>WREADY low / an R bubble with probability n/16.</p>

### WR_ERR_BASE register

- Absolute Address: 0x38
- Base Offset: 0x38
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### WR_ERR_MASK register

- Absolute Address: 0x3C
- Base Offset: 0x3C
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### WR_TIMING register

- Absolute Address: 0x40
- Base Offset: 0x40
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  LAT_MIN |  rw  | 0x0 |  — |
| 15:8| LAT_MASK |  rw  | 0x0 |  — |
|23:16|  MAX_OUT |  rw  | 0x0 |  — |

#### LAT_MIN field

<p>Cycles before a request may answer ...</p>

#### LAT_MASK field

<p>... plus random &amp; LAT_MASK.</p>

#### MAX_OUT field

<p>Requests held; 0 = as built.</p>

### WR_SEED register

- Absolute Address: 0x44
- Base Offset: 0x44
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### WR_SB register

- Absolute Address: 0x48
- Base Offset: 0x48
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|    SRC   |  rw  | 0x0 |  — |
|11:8|POISON_LG2|  rw  | 0x0 |  — |

#### SRC field

<p>AXI5: bit i set = requests from master index i (the fabric's ID prefix) carry sideband natively and must match f_sb; from any other master the sideband must be 0.</p>

#### POISON_LG2 field

<p>AXI5: R beats poisoned, and W beats expected poisoned, 1 in 2^n by address; 0 = never.</p>

### RD_BURSTS register

- Absolute Address: 0x200
- Base Offset: 0x200
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### RD_BEATS register

- Absolute Address: 0x204
- Base Offset: 0x204
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### RD_ERR register

- Absolute Address: 0x208
- Base Offset: 0x208
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|   MASK   |   r  | 0x0 |  — |
|31:16|   COUNT  |   r  | 0x0 |  — |

#### MASK field

<p>Sticky, one bit per ERR_* code.</p>

#### COUNT field

<p>Errors counted (saturating).</p>

### RD_FE register

- Absolute Address: 0x20C
- Base Offset: 0x20C
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
|  0  | FE_VALID |   r  | 0x0 |  — |
| 7:4 |  FE_KIND |   r  | 0x0 |  — |
|31:16|   FE_ID  |   r  | 0x0 |  — |

#### FE_ID field

<p>First error: request / burst ID.</p>

### RD_FE_ADDR register

- Absolute Address: 0x210
- Base Offset: 0x210
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### RD_FE_EXP register

- Absolute Address: 0x214
- Base Offset: 0x214
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### RD_FE_ACT register

- Absolute Address: 0x218
- Base Offset: 0x218
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### RD_OUT register

- Absolute Address: 0x21C
- Base Offset: 0x21C
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  OUT_NOW |   r  | 0x0 |  — |
| 15:8|  OUT_MAX |   r  | 0x0 |  — |
|23:16|   RUNS   |   r  | 0x0 |  — |

#### RUNS field

<p>GOs (status clears) taken (wraps).</p>

### WR_BURSTS register

- Absolute Address: 0x240
- Base Offset: 0x240
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_BEATS register

- Absolute Address: 0x244
- Base Offset: 0x244
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_ERR register

- Absolute Address: 0x248
- Base Offset: 0x248
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0|   MASK   |   r  | 0x0 |  — |
|31:16|   COUNT  |   r  | 0x0 |  — |

#### MASK field

<p>Sticky, one bit per ERR_* code.</p>

#### COUNT field

<p>Errors counted (saturating).</p>

### WR_FE register

- Absolute Address: 0x24C
- Base Offset: 0x24C
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
|  0  | FE_VALID |   r  | 0x0 |  — |
| 7:4 |  FE_KIND |   r  | 0x0 |  — |
|31:16|   FE_ID  |   r  | 0x0 |  — |

#### FE_ID field

<p>First error: request / burst ID.</p>

### WR_FE_ADDR register

- Absolute Address: 0x250
- Base Offset: 0x250
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_FE_EXP register

- Absolute Address: 0x254
- Base Offset: 0x254
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_FE_ACT register

- Absolute Address: 0x258
- Base Offset: 0x258
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### WR_OUT register

- Absolute Address: 0x25C
- Base Offset: 0x25C
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  OUT_NOW |   r  | 0x0 |  — |
| 15:8|  OUT_MAX |   r  | 0x0 |  — |
|23:16|   RUNS   |   r  | 0x0 |  — |

#### RUNS field

<p>GOs (status clears) taken (wraps).</p>
