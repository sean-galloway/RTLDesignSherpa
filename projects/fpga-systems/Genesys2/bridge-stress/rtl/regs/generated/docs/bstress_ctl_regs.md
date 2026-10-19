<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## bstress_ctl_regs address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x24

<p>GO/STOP, the data seed, the run timer and the pass/fail roll-up</p>

|Offset|  Identifier  |Name|
|------|--------------|----|
| 0x00 |      ID      |  — |
| 0x04 |     CTRL     |  — |
| 0x08 |   HASH_SEED  |  — |
| 0x0C |    STATUS    |  — |
| 0x10 |     TIMER    |  — |
| 0x14 |UNMAPPED_COUNT|  — |
| 0x18 | UNMAPPED_ADDR|  — |
| 0x1C |    CYCLES    |  — |
| 0x20 |   GO_COUNT   |  — |

### ID register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>Identity: 0x4253 ('BS'), the build's master and slave counts.</p>

| Bits| Identifier|Access|Reset|Name|
|-----|-----------|------|-----|----|
| 3:0 |NUM_MASTERS|   r  | 0x0 |  — |
| 7:4 | NUM_SLAVES|   r  | 0x0 |  — |
| 15:8|  VARIANT  |   r  | 0x0 |  — |
|31:16|   MAGIC   |   r  | 0x0 |  — |

#### VARIANT field

<p>Build variant (which DUT bridge).</p>

#### MAGIC field

<p>Constant 0x4253.</p>

### CTRL register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|  0 |      GO      |  rw  | 0x0 |  — |
|  1 |     STOP     |  rw  | 0x0 |  — |
|  2 |UNMAPPED_CLEAR|  rw  | 0x0 |  — |

#### GO field

<p>Start every enabled master on one cycle; zero all status and the timer. Ignored by a block still busy.</p>

#### STOP field

<p>Stop issuing; outstanding bursts drain.</p>

#### UNMAPPED_CLEAR field

<p>Clear the bridge's unmapped-address status.</p>

### HASH_SEED register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4

|Bits|Identifier|Access|   Reset  |Name|
|----|----------|------|----------|----|
|31:0|   VALUE  |  rw  |0x12345678|  — |

#### VALUE field

<p>Seed of the data function, shared by every master and slave.</p>

### STATUS register

- Absolute Address: 0xC
- Base Offset: 0xC
- Size: 0x4

<p>Roll-up, live.</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
|  0  | ALL_DONE |   r  | 0x0 |  — |
|  1  |  ANY_ERR |   r  | 0x0 |  — |
|  2  | CLOCKS_OK|   r  | 0x0 |  — |
|  3  | UNMAPPED |   r  | 0x0 |  — |
| 15:8| MST_DONE |   r  | 0x0 |  — |
|23:16|  MST_ERR |   r  | 0x0 |  — |
|31:24|  SLV_ERR |   r  | 0x0 |  — |

#### ALL_DONE field

<p>Every master: both directions done.</p>

#### ANY_ERR field

<p>Any block has an error bit set.</p>

#### CLOCKS_OK field

<p>Every clock domain locked / out of reset.</p>

#### UNMAPPED field

<p>Bridge unmapped-address flag.</p>

#### MST_DONE field

<p>Per master: done.</p>

#### MST_ERR field

<p>Per master: error.</p>

#### SLV_ERR field

<p>Per slave: error.</p>

### TIMER register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

#### VALUE field

<p>aclk cycles from GO to ALL_DONE (counting while busy).</p>

### UNMAPPED_COUNT register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|   COUNT  |   r  | 0x0 |  — |

#### COUNT field

<p>Bridge unmapped-access count (saturates at 255).</p>

### UNMAPPED_ADDR register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

#### VALUE field

<p>Address of the first unmapped access.</p>

### CYCLES register

- Absolute Address: 0x1C
- Base Offset: 0x1C
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

#### VALUE field

<p>Free-running aclk cycle counter (liveness).</p>

### GO_COUNT register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|   VALUE  |   r  | 0x0 |  — |

#### VALUE field

<p>GOs issued (wraps at 256). Every block's RUNS must equal it: a block that missed a GO keeps the previous run's status.</p>
