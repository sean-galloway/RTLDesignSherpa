<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## fb_ctl_regs address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x20

<p>Run-timer endpoint select, board status and the S0 (DDR3) counters</p>

|Offset|   Identifier   |Name|
|------|----------------|----|
| 0x00 |    WORKLOAD    |  — |
| 0x04 |   S0_RD_BEATS  |  — |
| 0x08 |   S0_WR_BEATS  |  — |
| 0x0C |     STATUS     |  — |
| 0x10 |   S0_AW_COUNT  |  — |
| 0x14 |   S0_B_COUNT   |  — |
| 0x18 |   S0_AR_COUNT  |  — |
| 0x1C |S0_RVALID_CYCLES|  — |

### WORKLOAD register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>Where the run timer counts. Set before the run; the defaults are W2.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |  RD_SRC  |  rw  | 0x0 |  — |
|  1 |  WR_DST  |  rw  | 0x0 |  — |

#### RD_SRC field

<p>Read beats (first/last read timestamps): 0 = LFSR source (S2), 1 = DDR3 (S0).</p>

#### WR_DST field

<p>Write beats (first/last write timestamps and STOP): 0 = CRC sink (S3), 1 = DDR3 (S0).</p>

### S0_RD_BEATS register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

<p>Read beats accepted at the fabric's S0 port since CLEAR_STATS / soft reset.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### S0_WR_BEATS register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4

<p>Write beats accepted at the fabric's S0 port since CLEAR_STATS / soft reset.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### STATUS register

- Absolute Address: 0xC
- Base Offset: 0xC
- Size: 0x4

<p>Board status, live (not latched). DDR3 runs need INIT_CALIB_COMPLETE.</p>

|Bits|     Identifier    |Access|Reset|Name|
|----|-------------------|------|-----|----|
|  0 |INIT_CALIB_COMPLETE|   r  | 0x0 |  — |
|  1 |   DDR_PLL_LOCKED  |   r  | 0x0 |  — |
|  2 |   EP_MMCM_LOCKED  |   r  | 0x0 |  — |
|  3 |   DDR_INIT_ERROR  |   r  | 0x0 |  — |
|  8 |     S0_ARVALID    |   r  | 0x0 |  — |
|  9 |     S0_ARREADY    |   r  | 0x0 |  — |
| 10 |     S0_RVALID     |   r  | 0x0 |  — |
| 11 |     S0_RREADY     |   r  | 0x0 |  — |
| 12 |     S0_AWVALID    |   r  | 0x0 |  — |
| 13 |     S0_AWREADY    |   r  | 0x0 |  — |
| 14 |     S0_WVALID     |   r  | 0x0 |  — |
| 15 |     S0_WREADY     |   r  | 0x0 |  — |
| 16 |     S0_BVALID     |   r  | 0x0 |  — |
| 17 |     S0_BREADY     |   r  | 0x0 |  — |

#### INIT_CALIB_COMPLETE field

<p>S0 controller initialized and calibrated without error (LiteDRAM init_done and not init_error).</p>

#### DDR_PLL_LOCKED field

<p>S0 controller PLL locked (synchronized to aclk).</p>

#### EP_MMCM_LOCKED field

<p>Endpoint-clock MMCM locked (synchronized to aclk).</p>

#### DDR_INIT_ERROR field

<p>S0 controller calibration finished with an error (LiteDRAM init_error).</p>

#### S0_ARVALID field

<p>S0 ARVALID, live (a stalled run shows which side holds the channel).</p>

#### S0_ARREADY field

<p>S0 ARREADY, live.</p>

#### S0_RVALID field

<p>S0 RVALID, live.</p>

#### S0_RREADY field

<p>S0 RREADY, live.</p>

#### S0_AWVALID field

<p>S0 AWVALID, live.</p>

#### S0_AWREADY field

<p>S0 AWREADY, live.</p>

#### S0_WVALID field

<p>S0 WVALID, live.</p>

#### S0_WREADY field

<p>S0 WREADY, live.</p>

#### S0_BVALID field

<p>S0 BVALID, live.</p>

#### S0_BREADY field

<p>S0 BREADY, live.</p>

### S0_AW_COUNT register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>AW handshakes at S0 since CLEAR_STATS / soft reset.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### S0_B_COUNT register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

<p>B handshakes at S0 since CLEAR_STATS / soft reset.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### S0_AR_COUNT register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

<p>AR handshakes at S0 since CLEAR_STATS / soft reset.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### S0_RVALID_CYCLES register

- Absolute Address: 0x1C
- Base Offset: 0x1C
- Size: 0x4

<p>Cycles S0 RVALID was high since CLEAR_STATS / soft reset (with S0_RD_BEATS: cycles the fabric held RREADY low).</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |
