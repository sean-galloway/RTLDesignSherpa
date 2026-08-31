<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## chargen_regs address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x418

<p>Per-bank AXI4 write/read pattern-generator config, staged then launched together</p>

|Offset|Identifier|Name|
|------|----------|----|
| 0x000| WR_GEN[0]|  — |
| 0x040| WR_GEN[1]|  — |
| 0x080| WR_GEN[2]|  — |
| 0x0C0| WR_GEN[3]|  — |
| 0x200| RD_GEN[0]|  — |
| 0x240| RD_GEN[1]|  — |
| 0x280| RD_GEN[2]|  — |
| 0x2C0| RD_GEN[3]|  — |
| 0x400|    GO    |  — |
| 0x404|   DONE   |  — |
| 0x408|  ERRORS  |  — |
| 0x410|GEN_CONFIG|  — |
| 0x414| BLOCK_ID |  — |

## WR_GEN register file

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x38
- Array Dimensions: [4]
- Array Stride: 0x40
- Total Size: 0x100

|Offset| Identifier |Name|
|------|------------|----|
| 0x00 | START_ADDR |  — |
| 0x04 |  STRIDE_0  |  — |
| 0x08 |  STRIDE_1  |  — |
| 0x0C | WRAP_MASK_0|  — |
| 0x10 | WRAP_MASK_1|  — |
| 0x14 |  BLEN_TXN  |  — |
| 0x18 |  AXI_ATTR  |  — |
| 0x1C |  LFSR_SEED |  — |
| 0x20 | HASH_SEED0 |  — |
| 0x24 | HASH_SEED1 |  — |
| 0x28 | HASH_SEED2 |  — |
| 0x30 |   STATUS   |  — |
| 0x34 |EXPECTED_CRC|  — |

### START_ADDR register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>32-bit address</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   addr   |  rw  | 0x0 |  — |

### STRIDE_0 register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### STRIDE_1 register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### WRAP_MASK_0 register

- Absolute Address: 0xC
- Base Offset: 0xC
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### WRAP_MASK_1 register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### BLEN_TXN register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

<p>Burst length / transaction count / inter-burst gap</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | burst_len|  rw  | 0x0 |  — |
| 23:8| txn_count|  rw  | 0x0 |  — |
|27:24|    gap   |  rw  | 0x0 |  — |

### AXI_ATTR register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

<p>AXI id / id_mode / size / burst / data_mode</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  axi_id  |  rw  | 0x0 |  — |
| 9:8 |  id_mode |  rw  | 0x0 |  — |
|12:10| axi_size |  rw  | 0x0 |  — |
|14:13| axi_burst|  rw  | 0x0 |  — |
|  15 | data_mode|  rw  | 0x0 |  — |

### LFSR_SEED register

- Absolute Address: 0x1C
- Base Offset: 0x1C
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED0 register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED1 register

- Absolute Address: 0x24
- Base Offset: 0x24
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED2 register

- Absolute Address: 0x28
- Base Offset: 0x28
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### STATUS register

- Absolute Address: 0x30
- Base Offset: 0x30
- Size: 0x4

<p>Per-generator completion and sticky error status</p>

|Bits| Identifier|Access|Reset|Name|
|----|-----------|------|-----|----|
|  0 |    done   |   r  | 0x0 |  — |
|  1 | crc_valid |   r  | 0x0 |  — |
|  2 |bresp_error|   r  | 0x0 |  — |

### EXPECTED_CRC register

- Absolute Address: 0x34
- Base Offset: 0x34
- Size: 0x4

<p>32-bit CRC, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    crc   |   r  | 0x0 |  — |

## WR_GEN register file

- Absolute Address: 0x40
- Base Offset: 0x0
- Size: 0x38
- Array Dimensions: [4]
- Array Stride: 0x40
- Total Size: 0x100

|Offset| Identifier |Name|
|------|------------|----|
| 0x00 | START_ADDR |  — |
| 0x04 |  STRIDE_0  |  — |
| 0x08 |  STRIDE_1  |  — |
| 0x0C | WRAP_MASK_0|  — |
| 0x10 | WRAP_MASK_1|  — |
| 0x14 |  BLEN_TXN  |  — |
| 0x18 |  AXI_ATTR  |  — |
| 0x1C |  LFSR_SEED |  — |
| 0x20 | HASH_SEED0 |  — |
| 0x24 | HASH_SEED1 |  — |
| 0x28 | HASH_SEED2 |  — |
| 0x30 |   STATUS   |  — |
| 0x34 |EXPECTED_CRC|  — |

### START_ADDR register

- Absolute Address: 0x40
- Base Offset: 0x0
- Size: 0x4

<p>32-bit address</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   addr   |  rw  | 0x0 |  — |

### STRIDE_0 register

- Absolute Address: 0x44
- Base Offset: 0x4
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### STRIDE_1 register

- Absolute Address: 0x48
- Base Offset: 0x8
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### WRAP_MASK_0 register

- Absolute Address: 0x4C
- Base Offset: 0xC
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### WRAP_MASK_1 register

- Absolute Address: 0x50
- Base Offset: 0x10
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### BLEN_TXN register

- Absolute Address: 0x54
- Base Offset: 0x14
- Size: 0x4

<p>Burst length / transaction count / inter-burst gap</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | burst_len|  rw  | 0x0 |  — |
| 23:8| txn_count|  rw  | 0x0 |  — |
|27:24|    gap   |  rw  | 0x0 |  — |

### AXI_ATTR register

- Absolute Address: 0x58
- Base Offset: 0x18
- Size: 0x4

<p>AXI id / id_mode / size / burst / data_mode</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  axi_id  |  rw  | 0x0 |  — |
| 9:8 |  id_mode |  rw  | 0x0 |  — |
|12:10| axi_size |  rw  | 0x0 |  — |
|14:13| axi_burst|  rw  | 0x0 |  — |
|  15 | data_mode|  rw  | 0x0 |  — |

### LFSR_SEED register

- Absolute Address: 0x5C
- Base Offset: 0x1C
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED0 register

- Absolute Address: 0x60
- Base Offset: 0x20
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED1 register

- Absolute Address: 0x64
- Base Offset: 0x24
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED2 register

- Absolute Address: 0x68
- Base Offset: 0x28
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### STATUS register

- Absolute Address: 0x70
- Base Offset: 0x30
- Size: 0x4

<p>Per-generator completion and sticky error status</p>

|Bits| Identifier|Access|Reset|Name|
|----|-----------|------|-----|----|
|  0 |    done   |   r  | 0x0 |  — |
|  1 | crc_valid |   r  | 0x0 |  — |
|  2 |bresp_error|   r  | 0x0 |  — |

### EXPECTED_CRC register

- Absolute Address: 0x74
- Base Offset: 0x34
- Size: 0x4

<p>32-bit CRC, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    crc   |   r  | 0x0 |  — |

## WR_GEN register file

- Absolute Address: 0x80
- Base Offset: 0x0
- Size: 0x38
- Array Dimensions: [4]
- Array Stride: 0x40
- Total Size: 0x100

|Offset| Identifier |Name|
|------|------------|----|
| 0x00 | START_ADDR |  — |
| 0x04 |  STRIDE_0  |  — |
| 0x08 |  STRIDE_1  |  — |
| 0x0C | WRAP_MASK_0|  — |
| 0x10 | WRAP_MASK_1|  — |
| 0x14 |  BLEN_TXN  |  — |
| 0x18 |  AXI_ATTR  |  — |
| 0x1C |  LFSR_SEED |  — |
| 0x20 | HASH_SEED0 |  — |
| 0x24 | HASH_SEED1 |  — |
| 0x28 | HASH_SEED2 |  — |
| 0x30 |   STATUS   |  — |
| 0x34 |EXPECTED_CRC|  — |

### START_ADDR register

- Absolute Address: 0x80
- Base Offset: 0x0
- Size: 0x4

<p>32-bit address</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   addr   |  rw  | 0x0 |  — |

### STRIDE_0 register

- Absolute Address: 0x84
- Base Offset: 0x4
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### STRIDE_1 register

- Absolute Address: 0x88
- Base Offset: 0x8
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### WRAP_MASK_0 register

- Absolute Address: 0x8C
- Base Offset: 0xC
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### WRAP_MASK_1 register

- Absolute Address: 0x90
- Base Offset: 0x10
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### BLEN_TXN register

- Absolute Address: 0x94
- Base Offset: 0x14
- Size: 0x4

<p>Burst length / transaction count / inter-burst gap</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | burst_len|  rw  | 0x0 |  — |
| 23:8| txn_count|  rw  | 0x0 |  — |
|27:24|    gap   |  rw  | 0x0 |  — |

### AXI_ATTR register

- Absolute Address: 0x98
- Base Offset: 0x18
- Size: 0x4

<p>AXI id / id_mode / size / burst / data_mode</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  axi_id  |  rw  | 0x0 |  — |
| 9:8 |  id_mode |  rw  | 0x0 |  — |
|12:10| axi_size |  rw  | 0x0 |  — |
|14:13| axi_burst|  rw  | 0x0 |  — |
|  15 | data_mode|  rw  | 0x0 |  — |

### LFSR_SEED register

- Absolute Address: 0x9C
- Base Offset: 0x1C
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED0 register

- Absolute Address: 0xA0
- Base Offset: 0x20
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED1 register

- Absolute Address: 0xA4
- Base Offset: 0x24
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED2 register

- Absolute Address: 0xA8
- Base Offset: 0x28
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### STATUS register

- Absolute Address: 0xB0
- Base Offset: 0x30
- Size: 0x4

<p>Per-generator completion and sticky error status</p>

|Bits| Identifier|Access|Reset|Name|
|----|-----------|------|-----|----|
|  0 |    done   |   r  | 0x0 |  — |
|  1 | crc_valid |   r  | 0x0 |  — |
|  2 |bresp_error|   r  | 0x0 |  — |

### EXPECTED_CRC register

- Absolute Address: 0xB4
- Base Offset: 0x34
- Size: 0x4

<p>32-bit CRC, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    crc   |   r  | 0x0 |  — |

## WR_GEN register file

- Absolute Address: 0xC0
- Base Offset: 0x0
- Size: 0x38
- Array Dimensions: [4]
- Array Stride: 0x40
- Total Size: 0x100

|Offset| Identifier |Name|
|------|------------|----|
| 0x00 | START_ADDR |  — |
| 0x04 |  STRIDE_0  |  — |
| 0x08 |  STRIDE_1  |  — |
| 0x0C | WRAP_MASK_0|  — |
| 0x10 | WRAP_MASK_1|  — |
| 0x14 |  BLEN_TXN  |  — |
| 0x18 |  AXI_ATTR  |  — |
| 0x1C |  LFSR_SEED |  — |
| 0x20 | HASH_SEED0 |  — |
| 0x24 | HASH_SEED1 |  — |
| 0x28 | HASH_SEED2 |  — |
| 0x30 |   STATUS   |  — |
| 0x34 |EXPECTED_CRC|  — |

### START_ADDR register

- Absolute Address: 0xC0
- Base Offset: 0x0
- Size: 0x4

<p>32-bit address</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   addr   |  rw  | 0x0 |  — |

### STRIDE_0 register

- Absolute Address: 0xC4
- Base Offset: 0x4
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### STRIDE_1 register

- Absolute Address: 0xC8
- Base Offset: 0x8
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### WRAP_MASK_0 register

- Absolute Address: 0xCC
- Base Offset: 0xC
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### WRAP_MASK_1 register

- Absolute Address: 0xD0
- Base Offset: 0x10
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### BLEN_TXN register

- Absolute Address: 0xD4
- Base Offset: 0x14
- Size: 0x4

<p>Burst length / transaction count / inter-burst gap</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | burst_len|  rw  | 0x0 |  — |
| 23:8| txn_count|  rw  | 0x0 |  — |
|27:24|    gap   |  rw  | 0x0 |  — |

### AXI_ATTR register

- Absolute Address: 0xD8
- Base Offset: 0x18
- Size: 0x4

<p>AXI id / id_mode / size / burst / data_mode</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  axi_id  |  rw  | 0x0 |  — |
| 9:8 |  id_mode |  rw  | 0x0 |  — |
|12:10| axi_size |  rw  | 0x0 |  — |
|14:13| axi_burst|  rw  | 0x0 |  — |
|  15 | data_mode|  rw  | 0x0 |  — |

### LFSR_SEED register

- Absolute Address: 0xDC
- Base Offset: 0x1C
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED0 register

- Absolute Address: 0xE0
- Base Offset: 0x20
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED1 register

- Absolute Address: 0xE4
- Base Offset: 0x24
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED2 register

- Absolute Address: 0xE8
- Base Offset: 0x28
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### STATUS register

- Absolute Address: 0xF0
- Base Offset: 0x30
- Size: 0x4

<p>Per-generator completion and sticky error status</p>

|Bits| Identifier|Access|Reset|Name|
|----|-----------|------|-----|----|
|  0 |    done   |   r  | 0x0 |  — |
|  1 | crc_valid |   r  | 0x0 |  — |
|  2 |bresp_error|   r  | 0x0 |  — |

### EXPECTED_CRC register

- Absolute Address: 0xF4
- Base Offset: 0x34
- Size: 0x4

<p>32-bit CRC, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    crc   |   r  | 0x0 |  — |

## RD_GEN register file

- Absolute Address: 0x200
- Base Offset: 0x200
- Size: 0x40
- Array Dimensions: [4]
- Array Stride: 0x40
- Total Size: 0x100

|Offset| Identifier|Name|
|------|-----------|----|
| 0x00 | START_ADDR|  — |
| 0x04 |  STRIDE_0 |  — |
| 0x08 |  STRIDE_1 |  — |
| 0x0C |WRAP_MASK_0|  — |
| 0x10 |WRAP_MASK_1|  — |
| 0x14 |  BLEN_TXN |  — |
| 0x18 |  AXI_ATTR |  — |
| 0x1C | LFSR_SEED |  — |
| 0x20 | HASH_SEED0|  — |
| 0x24 | HASH_SEED1|  — |
| 0x28 | HASH_SEED2|  — |
| 0x30 |   STATUS  |  — |
| 0x34 | ACTUAL_CRC|  — |
| 0x38 | BEATS_MISM|  — |
| 0x3C |STRAY_BEATS|  — |

### START_ADDR register

- Absolute Address: 0x200
- Base Offset: 0x0
- Size: 0x4

<p>32-bit address</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   addr   |  rw  | 0x0 |  — |

### STRIDE_0 register

- Absolute Address: 0x204
- Base Offset: 0x4
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### STRIDE_1 register

- Absolute Address: 0x208
- Base Offset: 0x8
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### WRAP_MASK_0 register

- Absolute Address: 0x20C
- Base Offset: 0xC
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### WRAP_MASK_1 register

- Absolute Address: 0x210
- Base Offset: 0x10
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### BLEN_TXN register

- Absolute Address: 0x214
- Base Offset: 0x14
- Size: 0x4

<p>Burst length / transaction count / inter-burst gap</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | burst_len|  rw  | 0x0 |  — |
| 23:8| txn_count|  rw  | 0x0 |  — |
|27:24|    gap   |  rw  | 0x0 |  — |

### AXI_ATTR register

- Absolute Address: 0x218
- Base Offset: 0x18
- Size: 0x4

<p>AXI id / id_mode / size / burst / data_mode</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  axi_id  |  rw  | 0x0 |  — |
| 9:8 |  id_mode |  rw  | 0x0 |  — |
|12:10| axi_size |  rw  | 0x0 |  — |
|14:13| axi_burst|  rw  | 0x0 |  — |
|  15 | data_mode|  rw  | 0x0 |  — |

### LFSR_SEED register

- Absolute Address: 0x21C
- Base Offset: 0x1C
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED0 register

- Absolute Address: 0x220
- Base Offset: 0x20
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED1 register

- Absolute Address: 0x224
- Base Offset: 0x24
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED2 register

- Absolute Address: 0x228
- Base Offset: 0x28
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### STATUS register

- Absolute Address: 0x230
- Base Offset: 0x30
- Size: 0x4

<p>Per-generator completion and sticky error status</p>

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
|  0 |      done      |   r  | 0x0 |  — |
|  1 |    crc_valid   |   r  | 0x0 |  — |
|  2 |   data_error   |   r  | 0x0 |  — |
|  3 |   rresp_error  |   r  | 0x0 |  — |
|  4 |stray_beat_error|   r  | 0x0 |  — |

### ACTUAL_CRC register

- Absolute Address: 0x234
- Base Offset: 0x34
- Size: 0x4

<p>32-bit CRC, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    crc   |   r  | 0x0 |  — |

### BEATS_MISM register

- Absolute Address: 0x238
- Base Offset: 0x38
- Size: 0x4

<p>32-bit event count, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   beats  |   r  | 0x0 |  — |

### STRAY_BEATS register

- Absolute Address: 0x23C
- Base Offset: 0x3C
- Size: 0x4

<p>32-bit event count, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   beats  |   r  | 0x0 |  — |

## RD_GEN register file

- Absolute Address: 0x240
- Base Offset: 0x200
- Size: 0x40
- Array Dimensions: [4]
- Array Stride: 0x40
- Total Size: 0x100

|Offset| Identifier|Name|
|------|-----------|----|
| 0x00 | START_ADDR|  — |
| 0x04 |  STRIDE_0 |  — |
| 0x08 |  STRIDE_1 |  — |
| 0x0C |WRAP_MASK_0|  — |
| 0x10 |WRAP_MASK_1|  — |
| 0x14 |  BLEN_TXN |  — |
| 0x18 |  AXI_ATTR |  — |
| 0x1C | LFSR_SEED |  — |
| 0x20 | HASH_SEED0|  — |
| 0x24 | HASH_SEED1|  — |
| 0x28 | HASH_SEED2|  — |
| 0x30 |   STATUS  |  — |
| 0x34 | ACTUAL_CRC|  — |
| 0x38 | BEATS_MISM|  — |
| 0x3C |STRAY_BEATS|  — |

### START_ADDR register

- Absolute Address: 0x240
- Base Offset: 0x0
- Size: 0x4

<p>32-bit address</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   addr   |  rw  | 0x0 |  — |

### STRIDE_0 register

- Absolute Address: 0x244
- Base Offset: 0x4
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### STRIDE_1 register

- Absolute Address: 0x248
- Base Offset: 0x8
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### WRAP_MASK_0 register

- Absolute Address: 0x24C
- Base Offset: 0xC
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### WRAP_MASK_1 register

- Absolute Address: 0x250
- Base Offset: 0x10
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### BLEN_TXN register

- Absolute Address: 0x254
- Base Offset: 0x14
- Size: 0x4

<p>Burst length / transaction count / inter-burst gap</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | burst_len|  rw  | 0x0 |  — |
| 23:8| txn_count|  rw  | 0x0 |  — |
|27:24|    gap   |  rw  | 0x0 |  — |

### AXI_ATTR register

- Absolute Address: 0x258
- Base Offset: 0x18
- Size: 0x4

<p>AXI id / id_mode / size / burst / data_mode</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  axi_id  |  rw  | 0x0 |  — |
| 9:8 |  id_mode |  rw  | 0x0 |  — |
|12:10| axi_size |  rw  | 0x0 |  — |
|14:13| axi_burst|  rw  | 0x0 |  — |
|  15 | data_mode|  rw  | 0x0 |  — |

### LFSR_SEED register

- Absolute Address: 0x25C
- Base Offset: 0x1C
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED0 register

- Absolute Address: 0x260
- Base Offset: 0x20
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED1 register

- Absolute Address: 0x264
- Base Offset: 0x24
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED2 register

- Absolute Address: 0x268
- Base Offset: 0x28
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### STATUS register

- Absolute Address: 0x270
- Base Offset: 0x30
- Size: 0x4

<p>Per-generator completion and sticky error status</p>

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
|  0 |      done      |   r  | 0x0 |  — |
|  1 |    crc_valid   |   r  | 0x0 |  — |
|  2 |   data_error   |   r  | 0x0 |  — |
|  3 |   rresp_error  |   r  | 0x0 |  — |
|  4 |stray_beat_error|   r  | 0x0 |  — |

### ACTUAL_CRC register

- Absolute Address: 0x274
- Base Offset: 0x34
- Size: 0x4

<p>32-bit CRC, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    crc   |   r  | 0x0 |  — |

### BEATS_MISM register

- Absolute Address: 0x278
- Base Offset: 0x38
- Size: 0x4

<p>32-bit event count, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   beats  |   r  | 0x0 |  — |

### STRAY_BEATS register

- Absolute Address: 0x27C
- Base Offset: 0x3C
- Size: 0x4

<p>32-bit event count, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   beats  |   r  | 0x0 |  — |

## RD_GEN register file

- Absolute Address: 0x280
- Base Offset: 0x200
- Size: 0x40
- Array Dimensions: [4]
- Array Stride: 0x40
- Total Size: 0x100

|Offset| Identifier|Name|
|------|-----------|----|
| 0x00 | START_ADDR|  — |
| 0x04 |  STRIDE_0 |  — |
| 0x08 |  STRIDE_1 |  — |
| 0x0C |WRAP_MASK_0|  — |
| 0x10 |WRAP_MASK_1|  — |
| 0x14 |  BLEN_TXN |  — |
| 0x18 |  AXI_ATTR |  — |
| 0x1C | LFSR_SEED |  — |
| 0x20 | HASH_SEED0|  — |
| 0x24 | HASH_SEED1|  — |
| 0x28 | HASH_SEED2|  — |
| 0x30 |   STATUS  |  — |
| 0x34 | ACTUAL_CRC|  — |
| 0x38 | BEATS_MISM|  — |
| 0x3C |STRAY_BEATS|  — |

### START_ADDR register

- Absolute Address: 0x280
- Base Offset: 0x0
- Size: 0x4

<p>32-bit address</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   addr   |  rw  | 0x0 |  — |

### STRIDE_0 register

- Absolute Address: 0x284
- Base Offset: 0x4
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### STRIDE_1 register

- Absolute Address: 0x288
- Base Offset: 0x8
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### WRAP_MASK_0 register

- Absolute Address: 0x28C
- Base Offset: 0xC
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### WRAP_MASK_1 register

- Absolute Address: 0x290
- Base Offset: 0x10
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### BLEN_TXN register

- Absolute Address: 0x294
- Base Offset: 0x14
- Size: 0x4

<p>Burst length / transaction count / inter-burst gap</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | burst_len|  rw  | 0x0 |  — |
| 23:8| txn_count|  rw  | 0x0 |  — |
|27:24|    gap   |  rw  | 0x0 |  — |

### AXI_ATTR register

- Absolute Address: 0x298
- Base Offset: 0x18
- Size: 0x4

<p>AXI id / id_mode / size / burst / data_mode</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  axi_id  |  rw  | 0x0 |  — |
| 9:8 |  id_mode |  rw  | 0x0 |  — |
|12:10| axi_size |  rw  | 0x0 |  — |
|14:13| axi_burst|  rw  | 0x0 |  — |
|  15 | data_mode|  rw  | 0x0 |  — |

### LFSR_SEED register

- Absolute Address: 0x29C
- Base Offset: 0x1C
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED0 register

- Absolute Address: 0x2A0
- Base Offset: 0x20
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED1 register

- Absolute Address: 0x2A4
- Base Offset: 0x24
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED2 register

- Absolute Address: 0x2A8
- Base Offset: 0x28
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### STATUS register

- Absolute Address: 0x2B0
- Base Offset: 0x30
- Size: 0x4

<p>Per-generator completion and sticky error status</p>

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
|  0 |      done      |   r  | 0x0 |  — |
|  1 |    crc_valid   |   r  | 0x0 |  — |
|  2 |   data_error   |   r  | 0x0 |  — |
|  3 |   rresp_error  |   r  | 0x0 |  — |
|  4 |stray_beat_error|   r  | 0x0 |  — |

### ACTUAL_CRC register

- Absolute Address: 0x2B4
- Base Offset: 0x34
- Size: 0x4

<p>32-bit CRC, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    crc   |   r  | 0x0 |  — |

### BEATS_MISM register

- Absolute Address: 0x2B8
- Base Offset: 0x38
- Size: 0x4

<p>32-bit event count, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   beats  |   r  | 0x0 |  — |

### STRAY_BEATS register

- Absolute Address: 0x2BC
- Base Offset: 0x3C
- Size: 0x4

<p>32-bit event count, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   beats  |   r  | 0x0 |  — |

## RD_GEN register file

- Absolute Address: 0x2C0
- Base Offset: 0x200
- Size: 0x40
- Array Dimensions: [4]
- Array Stride: 0x40
- Total Size: 0x100

|Offset| Identifier|Name|
|------|-----------|----|
| 0x00 | START_ADDR|  — |
| 0x04 |  STRIDE_0 |  — |
| 0x08 |  STRIDE_1 |  — |
| 0x0C |WRAP_MASK_0|  — |
| 0x10 |WRAP_MASK_1|  — |
| 0x14 |  BLEN_TXN |  — |
| 0x18 |  AXI_ATTR |  — |
| 0x1C | LFSR_SEED |  — |
| 0x20 | HASH_SEED0|  — |
| 0x24 | HASH_SEED1|  — |
| 0x28 | HASH_SEED2|  — |
| 0x30 |   STATUS  |  — |
| 0x34 | ACTUAL_CRC|  — |
| 0x38 | BEATS_MISM|  — |
| 0x3C |STRAY_BEATS|  — |

### START_ADDR register

- Absolute Address: 0x2C0
- Base Offset: 0x0
- Size: 0x4

<p>32-bit address</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   addr   |  rw  | 0x0 |  — |

### STRIDE_0 register

- Absolute Address: 0x2C4
- Base Offset: 0x4
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### STRIDE_1 register

- Absolute Address: 0x2C8
- Base Offset: 0x8
- Size: 0x4

<p>Signed address stride, STRIDE_WIDTH=24 (two's complement)</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|23:0|  stride  |  rw  | 0x0 |  — |

### WRAP_MASK_0 register

- Absolute Address: 0x2CC
- Base Offset: 0xC
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### WRAP_MASK_1 register

- Absolute Address: 0x2D0
- Base Offset: 0x10
- Size: 0x4

<p>32-bit address wrap mask</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   mask   |  rw  | 0x0 |  — |

### BLEN_TXN register

- Absolute Address: 0x2D4
- Base Offset: 0x14
- Size: 0x4

<p>Burst length / transaction count / inter-burst gap</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 | burst_len|  rw  | 0x0 |  — |
| 23:8| txn_count|  rw  | 0x0 |  — |
|27:24|    gap   |  rw  | 0x0 |  — |

### AXI_ATTR register

- Absolute Address: 0x2D8
- Base Offset: 0x18
- Size: 0x4

<p>AXI id / id_mode / size / burst / data_mode</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |  axi_id  |  rw  | 0x0 |  — |
| 9:8 |  id_mode |  rw  | 0x0 |  — |
|12:10| axi_size |  rw  | 0x0 |  — |
|14:13| axi_burst|  rw  | 0x0 |  — |
|  15 | data_mode|  rw  | 0x0 |  — |

### LFSR_SEED register

- Absolute Address: 0x2DC
- Base Offset: 0x1C
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED0 register

- Absolute Address: 0x2E0
- Base Offset: 0x20
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED1 register

- Absolute Address: 0x2E4
- Base Offset: 0x24
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### HASH_SEED2 register

- Absolute Address: 0x2E8
- Base Offset: 0x28
- Size: 0x4

<p>32-bit generator seed</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   seed   |  rw  | 0x0 |  — |

### STATUS register

- Absolute Address: 0x2F0
- Base Offset: 0x30
- Size: 0x4

<p>Per-generator completion and sticky error status</p>

|Bits|   Identifier   |Access|Reset|Name|
|----|----------------|------|-----|----|
|  0 |      done      |   r  | 0x0 |  — |
|  1 |    crc_valid   |   r  | 0x0 |  — |
|  2 |   data_error   |   r  | 0x0 |  — |
|  3 |   rresp_error  |   r  | 0x0 |  — |
|  4 |stray_beat_error|   r  | 0x0 |  — |

### ACTUAL_CRC register

- Absolute Address: 0x2F4
- Base Offset: 0x34
- Size: 0x4

<p>32-bit CRC, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|    crc   |   r  | 0x0 |  — |

### BEATS_MISM register

- Absolute Address: 0x2F8
- Base Offset: 0x38
- Size: 0x4

<p>32-bit event count, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   beats  |   r  | 0x0 |  — |

### STRAY_BEATS register

- Absolute Address: 0x2FC
- Base Offset: 0x3C
- Size: 0x4

<p>32-bit event count, computed by the engine</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|31:0|   beats  |   r  | 0x0 |  — |

### GO register

- Absolute Address: 0x400
- Base Offset: 0x400
- Size: 0x4

<p>Launch. Writing a 1 starts that generator; bits are self-clearing, so one write starts any subset on a single cycle.</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
|  0 |  wr_go0  |   w  | 0x0 |  — |
|  1 |  wr_go1  |   w  | 0x0 |  — |
|  2 |  wr_go2  |   w  | 0x0 |  — |
|  3 |  wr_go3  |   w  | 0x0 |  — |
|  8 |  rd_go0  |   w  | 0x0 |  — |
|  9 |  rd_go1  |   w  | 0x0 |  — |
| 10 |  rd_go2  |   w  | 0x0 |  — |
| 11 |  rd_go3  |   w  | 0x0 |  — |

### DONE register

- Absolute Address: 0x404
- Base Offset: 0x404
- Size: 0x4

<p>Per-generator done, gathered so a poll costs one read instead of sixteen</p>

|Bits|Identifier|Access|Reset|Name|
|----|----------|------|-----|----|
| 7:0|  wr_done |   r  | 0x0 |  — |
|15:8|  rd_done |   r  | 0x0 |  — |

### ERRORS register

- Absolute Address: 0x408
- Base Offset: 0x408
- Size: 0x4

<p>Sticky error roll-up across all generators; read STATUS per generator to localise</p>

|Bits|  Identifier  |Access|Reset|Name|
|----|--------------|------|-----|----|
| 7:0|wr_bresp_error|   r  | 0x0 |  — |
|15:8| rd_any_error |   r  | 0x0 |  — |

### GEN_CONFIG register

- Absolute Address: 0x410
- Base Offset: 0x410
- Size: 0x4

<p>Compile-time generator array shape</p>

| Bits|Identifier|Access|Reset|Name|
|-----|----------|------|-----|----|
| 7:0 |num_wr_gen|   r  | 0x4 |  — |
| 15:8|num_rd_gen|   r  | 0x4 |  — |
|23:16| num_banks|   r  | 0x8 |  — |

### BLOCK_ID register

- Absolute Address: 0x414
- Base Offset: 0x414
- Size: 0x4

<p>Block identity (ASCII CGEN)</p>

|Bits|Identifier|Access|   Reset  |Name|
|----|----------|------|----------|----|
|31:0|    id    |   r  |0x4347454E|  — |
