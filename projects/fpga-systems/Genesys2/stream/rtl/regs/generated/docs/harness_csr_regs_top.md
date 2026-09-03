<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## harness_csr_regs_top address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x200

<p>Control/status/timer/CRC/observability registers for the char harness</p>

|Offset|     Identifier     |Name|
|------|--------------------|----|
| 0x000|        CTRL        |  — |
| 0x004|       STATUS       |  — |
| 0x008|     DBG_WR_PTR     |  — |
| 0x00C|    DBG_OVERFLOW    |  — |
| 0x010|   CRC_RD_EXPECTED  |  — |
| 0x014|   CRC_WR_EXPECTED  |  — |
| 0x018|   CRC_WR_COMPUTED  |  — |
| 0x01C|      CRC_MATCH     |  — |
| 0x020|       SCRATCH      |  — |
| 0x024|      BUILD_ID      |  — |
| 0x028|     TIMER_CTRL     |  — |
| 0x02C|    TIMER_STATUS    |  — |
| 0x030|   TIMER_CYCLES_LO  |  — |
| 0x034|   TIMER_CYCLES_HI  |  — |
| 0x038|TIMER_EXPECTED_BEATS|  — |
| 0x03C|     RESP_DELAY     |  — |
| 0x040|  TIMER_R_FIRST_LO  |  — |
| 0x044|  TIMER_R_FIRST_HI  |  — |
| 0x048|   TIMER_R_LAST_LO  |  — |
| 0x04C|   TIMER_R_LAST_HI  |  — |
| 0x050|  TIMER_W_FIRST_LO  |  — |
| 0x054|  TIMER_W_FIRST_HI  |  — |
| 0x058|   TIMER_W_LAST_LO  |  — |
| 0x05C|   TIMER_W_LAST_HI  |  — |
| 0x060|   CRC_RD_PER_CH0   |  — |
| 0x064|   CRC_RD_PER_CH1   |  — |
| 0x068|   CRC_RD_PER_CH2   |  — |
| 0x06C|   CRC_RD_PER_CH3   |  — |
| 0x070|   CRC_RD_PER_CH4   |  — |
| 0x074|   CRC_RD_PER_CH5   |  — |
| 0x078|   CRC_RD_PER_CH6   |  — |
| 0x07C|   CRC_RD_PER_CH7   |  — |
| 0x080|   CRC_WR_PER_CH0   |  — |
| 0x084|   CRC_WR_PER_CH1   |  — |
| 0x088|   CRC_WR_PER_CH2   |  — |
| 0x08C|   CRC_WR_PER_CH3   |  — |
| 0x090|   CRC_WR_PER_CH4   |  — |
| 0x094|   CRC_WR_PER_CH5   |  — |
| 0x098|   CRC_WR_PER_CH6   |  — |
| 0x09C|   CRC_WR_PER_CH7   |  — |
| 0x0A0|   CRC_VALID_MASK   |  — |
| 0x0A4|   CRC_MATCH_MASK   |  — |
| 0x0D4|   DESC_SRAM_AR_HS  |  — |
| 0x0D8|   DESC_SRAM_R_HS   |  — |
| 0x0E0|     DESC_AR_HS     |  — |
| 0x0E4|    DESC_AR_STALL   |  — |
| 0x0E8|      DESC_R_HS     |  — |
| 0x0EC|    DESC_R_STALL    |  — |
| 0x0F0|     DESC_AW_HS     |  — |
| 0x0F4|      DESC_W_HS     |  — |
| 0x0F8|      DESC_B_HS     |  — |
| 0x0FC|    DESC_VR_LIVE    |  — |
| 0x1D0|    BUILD_VERSION   |  — |
| 0x1D4|    BUILD_CONFIG    |  — |
| 0x1D8|   BUILD_N_PROFILE  |  — |
| 0x1DC|    BUILD_CLK_HZ    |  — |
| 0x1E0|    COMP_TIER1_A    |  — |
| 0x1E4|    COMP_TIER1_B    |  — |
| 0x1E8|    COMP_TIER1_C    |  — |
| 0x1EC|     COMP_TIER0     |  — |
| 0x1F0|    COMP_CAM_MISS   |  — |
| 0x1F4|  COMP_DELTA_TS_OVF |  — |
| 0x1F8| COMP_EVENT_DATA_OVF|  — |
| 0x1FC|  COMP_ED_DELTA_OVF |  — |

### CTRL register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

|Bits| Identifier |Access|Reset|Name|
|----|------------|------|-----|----|
|  0 |    START   |  rw  | 0x0 |  — |
|  1 | CLEAR_STATS|  rw  | 0x0 |  — |
|  2 |FREEZE_TRACE|  rw  | 0x0 |  — |
|  3 | SOFT_RESET |  rw  | 0x0 |  — |
|  4 |  CAM_CLEAR |  rw  | 0x0 |  — |

### STATUS register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
|  0 |  STREAM_IRQ  |   r  | 0x0 |  — |
|  1 |   ANY_ERROR  |   r  | 0x0 |  — |
|  2 |TRACE_OVERFLOW|   r  | 0x0 |  — |
|  3 |  CLEAR_BUSY  |   r  | 0x0 |  — |

### DBG_WR_PTR register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### DBG_OVERFLOW register

- Absolute Address: 0xC
- Base Offset: 0xC
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_RD_EXPECTED register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_WR_EXPECTED register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_WR_COMPUTED register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_MATCH register

- Absolute Address: 0x1C
- Base Offset: 0x1C
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |   MATCH  |   r  | 0x0 |  — |
|  1 |   VALID  |   r  | 0x0 |  — |

### SCRATCH register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

<p>32-bit read-write word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### BUILD_ID register

- Absolute Address: 0x24
- Base Offset: 0x24
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### TIMER_CTRL register

- Absolute Address: 0x28
- Base Offset: 0x28
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |   CLEAR  |  rw  | 0x0 |  — |

### TIMER_STATUS register

- Absolute Address: 0x2C
- Base Offset: 0x2C
- Size: 0x4

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |   DONE   |   r  | 0x0 |  — |
|  1 |  RUNNING |   r  | 0x0 |  — |
|  2 |   PASS   |   r  | 0x0 |  — |

### TIMER_CYCLES_LO register

- Absolute Address: 0x30
- Base Offset: 0x30
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### TIMER_CYCLES_HI register

- Absolute Address: 0x34
- Base Offset: 0x34
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### TIMER_EXPECTED_BEATS register

- Absolute Address: 0x38
- Base Offset: 0x38
- Size: 0x4

<p>32-bit read-write word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |  rw  | 0x0 |  — |

### RESP_DELAY register

- Absolute Address: 0x3C
- Base Offset: 0x3C
- Size: 0x4

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 15:0| RD_DELAY |  rw  | 0x0 |  — |
|31:16| WR_DELAY |  rw  | 0x0 |  — |

### TIMER_R_FIRST_LO register

- Absolute Address: 0x40
- Base Offset: 0x40
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### TIMER_R_FIRST_HI register

- Absolute Address: 0x44
- Base Offset: 0x44
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### TIMER_R_LAST_LO register

- Absolute Address: 0x48
- Base Offset: 0x48
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### TIMER_R_LAST_HI register

- Absolute Address: 0x4C
- Base Offset: 0x4C
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### TIMER_W_FIRST_LO register

- Absolute Address: 0x50
- Base Offset: 0x50
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### TIMER_W_FIRST_HI register

- Absolute Address: 0x54
- Base Offset: 0x54
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### TIMER_W_LAST_LO register

- Absolute Address: 0x58
- Base Offset: 0x58
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### TIMER_W_LAST_HI register

- Absolute Address: 0x5C
- Base Offset: 0x5C
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_RD_PER_CH0 register

- Absolute Address: 0x60
- Base Offset: 0x60
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_RD_PER_CH1 register

- Absolute Address: 0x64
- Base Offset: 0x64
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_RD_PER_CH2 register

- Absolute Address: 0x68
- Base Offset: 0x68
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_RD_PER_CH3 register

- Absolute Address: 0x6C
- Base Offset: 0x6C
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_RD_PER_CH4 register

- Absolute Address: 0x70
- Base Offset: 0x70
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_RD_PER_CH5 register

- Absolute Address: 0x74
- Base Offset: 0x74
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_RD_PER_CH6 register

- Absolute Address: 0x78
- Base Offset: 0x78
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_RD_PER_CH7 register

- Absolute Address: 0x7C
- Base Offset: 0x7C
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_WR_PER_CH0 register

- Absolute Address: 0x80
- Base Offset: 0x80
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_WR_PER_CH1 register

- Absolute Address: 0x84
- Base Offset: 0x84
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_WR_PER_CH2 register

- Absolute Address: 0x88
- Base Offset: 0x88
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_WR_PER_CH3 register

- Absolute Address: 0x8C
- Base Offset: 0x8C
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_WR_PER_CH4 register

- Absolute Address: 0x90
- Base Offset: 0x90
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_WR_PER_CH5 register

- Absolute Address: 0x94
- Base Offset: 0x94
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_WR_PER_CH6 register

- Absolute Address: 0x98
- Base Offset: 0x98
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_WR_PER_CH7 register

- Absolute Address: 0x9C
- Base Offset: 0x9C
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_VALID_MASK register

- Absolute Address: 0xA0
- Base Offset: 0xA0
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### CRC_MATCH_MASK register

- Absolute Address: 0xA4
- Base Offset: 0xA4
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### DESC_SRAM_AR_HS register

- Absolute Address: 0xD4
- Base Offset: 0xD4
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### DESC_SRAM_R_HS register

- Absolute Address: 0xD8
- Base Offset: 0xD8
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### DESC_AR_HS register

- Absolute Address: 0xE0
- Base Offset: 0xE0
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### DESC_AR_STALL register

- Absolute Address: 0xE4
- Base Offset: 0xE4
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### DESC_R_HS register

- Absolute Address: 0xE8
- Base Offset: 0xE8
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### DESC_R_STALL register

- Absolute Address: 0xEC
- Base Offset: 0xEC
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### DESC_AW_HS register

- Absolute Address: 0xF0
- Base Offset: 0xF0
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### DESC_W_HS register

- Absolute Address: 0xF4
- Base Offset: 0xF4
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### DESC_B_HS register

- Absolute Address: 0xF8
- Base Offset: 0xF8
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### DESC_VR_LIVE register

- Absolute Address: 0xFC
- Base Offset: 0xFC
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### BUILD_VERSION register

- Absolute Address: 0x1D0
- Base Offset: 0x1D0
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### BUILD_CONFIG register

- Absolute Address: 0x1D4
- Base Offset: 0x1D4
- Size: 0x4

|Bits| Identifier |Access|Reset|Name|
|----|------------|------|-----|----|
| 4:0|NUM_CHANNELS|   r  | 0x0 |  — |
|  5 |ERROR_FLAVOR|   r  | 0x0 |  — |
|  6 |USE_MONITORS|   r  | 0x0 |  — |
|  7 |   GEN_MON  |   r  | 0x0 |  — |
|15:8|DATA_WIDTH_B|   r  | 0x0 |  — |
| 16 | MAIN_CONES |   r  | 0x0 |  — |

### BUILD_N_PROFILE register

- Absolute Address: 0x1D8
- Base Offset: 0x1D8
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### BUILD_CLK_HZ register

- Absolute Address: 0x1DC
- Base Offset: 0x1DC
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### COMP_TIER1_A register

- Absolute Address: 0x1E0
- Base Offset: 0x1E0
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### COMP_TIER1_B register

- Absolute Address: 0x1E4
- Base Offset: 0x1E4
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### COMP_TIER1_C register

- Absolute Address: 0x1E8
- Base Offset: 0x1E8
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### COMP_TIER0 register

- Absolute Address: 0x1EC
- Base Offset: 0x1EC
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### COMP_CAM_MISS register

- Absolute Address: 0x1F0
- Base Offset: 0x1F0
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### COMP_DELTA_TS_OVF register

- Absolute Address: 0x1F4
- Base Offset: 0x1F4
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### COMP_EVENT_DATA_OVF register

- Absolute Address: 0x1F8
- Base Offset: 0x1F8
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |

### COMP_ED_DELTA_OVF register

- Absolute Address: 0x1FC
- Base Offset: 0x1FC
- Size: 0x4

<p>32-bit read-only word</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   VALUE  |   r  | 0x0 |  — |
