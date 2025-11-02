# AXI4 Interface Specification and Assumptions

## Overview

This document defines the formal specification and assumptions for an AXI4 interface implementation that supports two distinct transfer modes to optimize for different interface types while ensuring robust, predictable operation.

## Interface Summary

### Number of Interfaces

- **5 Master Read Interfaces**: Descriptor sink, descriptor source, data source, flag sink, and flag source
- **3 Master Write Interfaces**: Data sink, control sink, and control source

### Interface Parameters

| Parameter | Description | Valid Values | Default |
|-----------|-------------|--------------|---------|
| `DATA_WIDTH` | AXI data bus width in bits | 32, 64, 128, 256, 512, 1024 | 32 |
| `ADDR_WIDTH` | AXI address bus width in bits | 32, 64 | 37 |
| `ID_WIDTH` | AXI ID tag width in bits | 1-16 | 8 |
| `USER_WIDTH` | AXI user signal width in bits (optional) | 0-16 | 1 |

### Interface Types and Transfer Modes

| Interface Group | Channels | Transfer Mode | Address Alignment | Monitor | DCG | Notes |
|----------------|----------|---------------|-------------------|----------|------------|-------|
| **AXI4 Master Read-Split** | AR, R | **Flexible** | 4-byte | Yes | Yes | Data interfaces with chunk enables |
| **AXI4 Master Write-Split**  | AW, W, B | **Flexible** | 4-byte | Yes | Yes | Data interfaces with chunk enables |
| **AXI4 Master Read** | AR, R | **Simplified** | Bus-width | No | Yes | Control interfaces, fully aligned |
| **AXI4 Master Write**  | AW, W, B | **Simplified** | Bus-width | Yes | Yes | Control interfaces, fully aligned |

### Interface Group Parameter Settings

| Interface Group | Data Width | Address Width | ID Width | User Width | Transfer Mode |
|-----------------|---------------|----------|------------|-------|---------------|
| **AXI4 Master Read-Split** | 512 bits | 37 bits | 8 bits | 1 bit | **Flexible** |
| **AXI4 Master Write-Split**  | 512 bits | 37 bits | 8 bits | 1 bit | **Flexible** |
| **AXI4 Master Read** | 32 bits | 37 bits | 8 bits | 1 bit | **Simplified** |
| **AXI4 Master Write** | 32 bits | 37 bits | 8 bits | 1 bit | **Simplified** |

### Interface Configuration Summary

| Interface Type | Interface Group | Transfer Mode | Alignment | Notes|
|----------------|-----------------|---------------|-----------|------|
| **Descriptor Sink** | **AXI4 Master Read** | **Simplified** | 32-bit aligned | Control interface |
| **Descriptor Source** | **AXI4 Master Read** | **Simplified** | 32-bit aligned | Control interface |
| **Data Source** | **AXI4 Master Read-Split** | **Flexible** | 4-byte aligned | High-bandwidth data |
| **Data Sink** | **AXI4 Master Write-Split** | **Flexible** | 4-byte aligned | High-bandwidth data |
| **Program Sink** | **AXI4 Master Write** | **Simplified** | 32-bit aligned | Control interface |
| **Program Source** | **AXI4 Master Write** | **Simplified** | 32-bit aligned | Control interface |
| **Flag Sink** | **AXI4 Master Read** | **Simplified** | 32-bit aligned | Control interface |
| **Flag Source** | **AXI4 Master Read** | **Simplified** | 32-bit aligned | Control interface |

## Transfer Mode Specifications

This specification defines two distinct transfer modes to optimize different interface types:

### Mode 1: Simplified Transfer Mode (Control Interfaces)

Used for control interfaces (descriptors, programs, flags) that prioritize simplicity and predictable timing.

#### **Simplified Mode Assumptions**

| Aspect | Requirement |
|--------|-------------|
| **Address Alignment** | All addresses aligned to full data bus width |
| **Transfer Size** | All transfers use maximum size equal to bus width |
| **Burst Type** | Incrementing bursts only (AxBURST = 2'b01) |
| **Transfer Complexity** | Maximum simplicity for predictable operation |

### Mode 2: Flexible Transfer Mode (Data Interfaces)

Used for high-bandwidth data interfaces that need to handle arbitrary address alignment while maintaining efficiency.

#### **Flexible Mode Assumptions**

| Aspect | Requirement |
|--------|-------------|
| **Address Alignment** | 4-byte aligned addresses (minimum alignment) |
| **Transfer Sizes** | Multiple sizes supported: 4, 8, 16, 32, 64 bytes |
| **Burst Type** | Incrementing bursts only (AxBURST = 2'b01) |
| **Alignment Strategy** | Progressive alignment to optimize bus utilization |

---

## Mode 1: Simplified Transfer Mode Specification

### Assumption 1: Address Alignment to Data Bus Width

| Aspect | Requirement |
|--------|-------------|
| **Alignment Rule** | All AXI transactions aligned to data bus width |
| **32-bit bus (4 bytes)** | Address[1:0] must be 2'b00 |
| **64-bit bus (8 bytes)** | Address[2:0] must be 3'b000 |
| **128-bit bus (16 bytes)** | Address[3:0] must be 4'b0000 |
| **256-bit bus (32 bytes)** | Address[4:0] must be 5'b00000 |
| **512-bit bus (64 bytes)** | Address[5:0] must be 6'b000000 |
| **1024-bit bus (128 bytes)** | Address[6:0] must be 7'b0000000 |
| **Rationale** | Maximizes bus efficiency and eliminates unaligned access complexity |

### Assumption 2: Fixed Transfer Size

| Aspect | Requirement |
|--------|-------------|
| **Transfer Size Rule** | All transfers use maximum size equal to bus width |
| **32-bit bus** | AxSIZE = 3'b010 (4 bytes) |
| **64-bit bus** | AxSIZE = 3'b011 (8 bytes) |
| **128-bit bus** | AxSIZE = 3'b100 (16 bytes) |
| **256-bit bus** | AxSIZE = 3'b101 (32 bytes) |
| **512-bit bus** | AxSIZE = 3'b110 (64 bytes) |
| **1024-bit bus** | AxSIZE = 3'b111 (128 bytes) |
| **Rationale** | Maximizes bus utilization and simplifies address alignment |

---

## Mode 2: Flexible Transfer Mode Specification

### Assumption 1: 4-Byte Address Alignment

| Aspect | Requirement |
|--------|-------------|
| **Alignment Rule** | All AXI transactions aligned to 4-byte boundaries |
| **Address Constraint** | Address[1:0] must be 2'b00 |
| **Rationale** | Balances flexibility with AXI protocol requirements |
| **Benefit** | Supports arbitrary data placement while maintaining AXI compliance |

### Assumption 2: Multiple Transfer Sizes

| Transfer Size | AxSIZE Value | Use Case |
|---------------|--------------|----------|
| **4 bytes** | 3'b010 | Initial alignment, small transfers |
| **8 bytes** | 3'b011 | Progressive alignment |
| **16 bytes** | 3'b100 | Progressive alignment |
| **32 bytes** | 3'b101 | Progressive alignment |
| **64 bytes** | 3'b110 | Optimal full-width transfers |
| **128 bytes** | 3'b111 | Maximum efficiency (1024-bit bus) |

### Assumption 3: Progressive Alignment Strategy

| Aspect | Requirement |
|--------|-------------|
| **Alignment Goal** | Align to 64-byte boundaries for optimal bus utilization |
| **Alignment Sequence** | Use progressive sizes: 4 -> 8 -> 16 -> 32 -> 64 bytes |
| **Optimization** | Choose largest possible transfer size at each step |
| **Example** | Address 0x1004: 4-byte transfer -> aligned to 0x1008, then larger transfers |

### Assumption 4: Chunk Enable Support

| Aspect | Requirement |
|--------|-------------|
| **Chunk Granularity** | 16 chunks of 32-bits each (512-bit bus) |
| **Write Strobes** | Generated from chunk enables for precise byte control |
| **Alignment Transfers** | Chunk patterns optimized for alignment sequences |
| **Benefits** | Precise data validity, optimal memory utilization |

---

## Common Protocol Assumptions (Both Modes)

### Assumption 1: Incrementing Bursts Only

| Aspect | Requirement |
|--------|-------------|
| **Burst Type** | All AXI bursts use incrementing address mode (AxBURST = 2'b01) |
| **Excluded Types** | No FIXED (2'b00) or WRAP (2'b10) bursts supported |
| **Rationale** | Simplifies address generation logic and covers most use cases |
| **Benefit** | Eliminates wrap boundary calculations and fixed address handling |

### Assumption 2: No Address Wraparound

| Aspect | Requirement |
|--------|-------------|
| **Wraparound Rule** | Transactions never wrap around top of address space |
| **Example** | No 0xFFFFFFFF -> 0x00000000 transitions |
| **Rationale** | Real systems never allow this due to memory layout |
| **Benefit** | Dramatically simplified boundary crossing detection logic |

---

## Flexible Mode: Address Calculation Examples

### Progressive Alignment Examples

**Example 1: Address 0x1004 -> 0x1040 (64-byte boundary)**

| Step | Address | Size | AxSIZE | Length | Bytes Transferred | Notes |
|------|---------|------|--------|--------|-------------------|-------|
| 1 | 0x1004 | 4 bytes | 3'b010 | 1 beat | 4 | Initial alignment |
| 2 | 0x1008 | 8 bytes | 3'b011 | 1 beat | 8 | Progressive alignment |
| 3 | 0x1010 | 16 bytes | 3'b100 | 1 beat | 16 | Progressive alignment |
| 4 | 0x1020 | 32 bytes | 3'b101 | 1 beat | 32 | Progressive alignment |
| 5 | 0x1040 | **64 bytes** | 3'b110 | N beats | 64xN | **Optimal transfers** |

**Example 2: Address 0x1010 -> 0x1040 (64-byte boundary)**

| Step | Address | Size | AxSIZE | Length | Bytes Transferred | Notes |
|------|---------|------|--------|--------|-------------------|-------|
| 1 | 0x1010 | 16 bytes | 3'b100 | 1 beat | 16 | Optimal initial size |
| 2 | 0x1020 | 32 bytes | 3'b101 | 1 beat | 32 | Progressive alignment |
| 3 | 0x1040 | **64 bytes** | 3'b110 | N beats | 64xN | **Optimal transfers** |

### Chunk Enable Pattern Examples

**512-bit Bus with 16x32-bit chunks**

| Transfer Size | Address Offset | Chunk Pattern | Description |
|---------------|----------------|---------------|-------------|
| **4 bytes** | 0x04 | 16'h0002 | Chunk 1 only |
| **8 bytes** | 0x08 | 16'h000C | Chunks 2-3 |
| **16 bytes** | 0x10 | 16'h00F0 | Chunks 4-7 |
| **32 bytes** | 0x20 | 16'hFF00 | Chunks 8-15 |
| **64 bytes** | 0x00 | 16'hFFFF | All chunks |

---

## Master Read Interface Specification

### Read Address Channel (AR)

| Signal | Width | Direction | Simplified Mode | Flexible Mode | Description |
|--------|-------|-----------|-----------------|---------------|-------------|
| `ar_addr` | `ADDR_WIDTH` | Master->Slave | **Bus-width aligned** | **4-byte aligned** | Read address |
| `ar_len` | 8 | Master->Slave | 0-255 | 0-255 | Burst length - 1 |
| `ar_size` | 3 | Master->Slave | **Fixed per bus** | **Variable: 4-64 bytes** | Transfer size |
| `ar_burst` | 2 | Master->Slave | **2'b01 (INCR only)** | **2'b01 (INCR only)** | Burst type |
| `ar_id` | `ID_WIDTH` | Master->Slave | Any | Any | Transaction ID |
| `ar_lock` | 1 | Master->Slave | 1'b0 | 1'b0 | Lock type (normal) |
| `ar_cache` | 4 | Master->Slave | Implementation specific | 4'b0011 | Cache attributes |
| `ar_prot` | 3 | Master->Slave | Implementation specific | 3'b000 | Protection attributes |
| `ar_qos` | 4 | Master->Slave | 4'b0000 | 4'b0000 | Quality of Service |
| `ar_region` | 4 | Master->Slave | 4'b0000 | 4'b0000 | Region identifier |
| `ar_user` | `USER_WIDTH` | Master->Slave | Optional | Optional | User-defined |
| `ar_valid` | 1 | Master->Slave | 0 or 1 | 0 or 1 | Address valid |
| `ar_ready` | 1 | Slave->Master | 0 or 1 | 0 or 1 | Address ready |

### Read Data Channel (R)

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `r_data` | `DATA_WIDTH` | Slave->Master | Read data |
| `r_id` | `ID_WIDTH` | Slave->Master | Transaction ID |
| `r_resp` | 2 | Slave->Master | Read response |
| `r_last` | 1 | Slave->Master | Last transfer in burst |
| `r_user` | `USER_WIDTH` | Slave->Master | User-defined (optional) |
| `r_valid` | 1 | Slave->Master | Read data valid |
| `r_ready` | 1 | Master->Slave | Read data ready |

---

## Master Write Interface Specification

### Write Address Channel (AW)

| Signal | Width | Direction | Simplified Mode | Flexible Mode | Description |
|--------|-------|-----------|-----------------|---------------|-------------|
| `aw_addr` | `ADDR_WIDTH` | Master->Slave | **Bus-width aligned** | **4-byte aligned** | Write address |
| `aw_len` | 8 | Master->Slave | 0-255 | 0-255 | Burst length - 1 |
| `aw_size` | 3 | Master->Slave | **Fixed per bus** | **Variable: 4-64 bytes** | Transfer size |
| `aw_burst` | 2 | Master->Slave | **2'b01 (INCR only)** | **2'b01 (INCR only)** | Burst type |
| `aw_id` | `ID_WIDTH` | Master->Slave | Any | Any | Transaction ID |
| `aw_lock` | 1 | Master->Slave | 1'b0 | 1'b0 | Lock type (normal) |
| `aw_cache` | 4 | Master->Slave | Implementation specific | 4'b0011 | Cache attributes |
| `aw_prot` | 3 | Master->Slave | Implementation specific | 3'b000 | Protection attributes |
| `aw_qos` | 4 | Master->Slave | 4'b0000 | 4'b0000 | Quality of Service |
| `aw_region` | 4 | Master->Slave | 4'b0000 | 4'b0000 | Region identifier |
| `aw_user` | `USER_WIDTH` | Master->Slave | Optional | Optional | User-defined |
| `aw_valid` | 1 | Master->Slave | 0 or 1 | 0 or 1 | Address valid |
| `aw_ready` | 1 | Slave->Master | 0 or 1 | 0 or 1 | Address ready |

### Write Data Channel (W)

| Signal | Width | Direction | Simplified Mode | Flexible Mode | Description |
|--------|-------|-----------|-----------------|---------------|-------------|
| `w_data` | `DATA_WIDTH` | Master->Slave | Write data | Write data | Write data |
| `w_strb` | `DATA_WIDTH/8` | Master->Slave | **All 1's** | **From chunk enables** | Write strobes |
| `w_last` | 1 | Master->Slave | Last transfer | Last transfer | Last transfer in burst |
| `w_user` | `USER_WIDTH` | Master->Slave | Optional | Optional | User-defined |
| `w_valid` | 1 | Master->Slave | 0 or 1 | 0 or 1 | Write data valid |
| `w_ready` | 1 | Slave->Master | 0 or 1 | 0 or 1 | Write data ready |

### Write Response Channel (B)

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `b_id` | `ID_WIDTH` | Slave->Master | Transaction ID |
| `b_resp` | 2 | Slave->Master | Write response |
| `b_user` | `USER_WIDTH` | Slave->Master | User-defined (optional) |
| `b_valid` | 1 | Slave->Master | Response valid |
| `b_ready` | 1 | Master->Slave | Response ready |

---

## Address Calculation Rules

### Simplified Mode Address Generation

| Parameter | Formula | Description |
|-----------|---------|-------------|
| **First Address** | Must be bus-width aligned | Starting address |
| **Address N** | First_Address + (N x Bus_Width_Bytes) | Address for beat N |
| **Alignment Check** | (Address % Bus_Width_Bytes) == 0 | Must always be true |

### Flexible Mode Address Generation

| Parameter | Formula | Description |
|-----------|---------|-------------|
| **First Address** | Must be 4-byte aligned | Starting address |
| **Address N** | First_Address + (N x Transfer_Size) | Address for beat N |
| **Alignment Check** | (Address % 4) == 0 | Must always be true |
| **Progressive Alignment** | Choose largest size <= bytes_to_boundary | Optimization strategy |

### 4KB Boundary Considerations (Both Modes)

| Validation Rule | Formula | Description |
|----------------|---------|-------------|
| **4KB Boundary** | Bursts cannot cross 4KB (0x1000) boundaries | AXI specification |
| **Max Burst Calculation** | Max_Beats = (4KB - (Start_Address % 4KB)) / Transfer_Size | Burst limit |
| **Boundary Check** | Verify no 4KB crossings in burst | Mandatory validation |

---

## Write Strobe Generation

### Simplified Mode Strobe Generation

| Bus Width | Strobe Pattern | Description |
|-----------|----------------|-------------|
| **32-bit** | 4'b1111 | All bytes valid |
| **512-bit** | 64'hFFFFFFFFFFFFFFFF | All bytes valid |

### Flexible Mode Strobe Generation

**From Chunk Enables (512-bit bus example):**

```verilog
// Convert 16x32-bit chunk enables to 64x8-bit write strobes
for (int chunk = 0; chunk < 16; chunk++) begin
    if (chunk_enable[chunk]) begin
        w_strb[chunk*4 +: 4] = 4'hF; // 4 bytes per chunk
    end
end
```

**Alignment Transfer Examples:**

| Transfer Size | Chunk Pattern | Strobe Pattern | Description |
|---------------|---------------|----------------|-------------|
| **4 bytes** | 16'h0001 | 64'h000000000000000F | First 4 bytes |
| **16 bytes** | 16'h000F | 64'h00000000000000FF | First 16 bytes |
| **32 bytes** | 16'h00FF | 64'h0000000000FFFFFF | First 32 bytes |
| **64 bytes** | 16'hFFFF | 64'hFFFFFFFFFFFFFFFF | All 64 bytes |

---

## Response Codes

### Response Code Specification

| Value | Name | Description | Simplified Mode Usage | Flexible Mode Usage |
|-------|------|-------------|----------------------|-------------------|
| **2'b00** | OKAY | Normal access success | Bus-width aligned access | 4-byte aligned access |
| **2'b01** | EXOKAY | Exclusive access success | Bus-width aligned exclusive | 4-byte aligned exclusive |
| **2'b10** | SLVERR | Slave error | Slave-specific error | Slave-specific error |
| **2'b11** | DECERR | Decode error | **Bus-width misalignment** | **4-byte misalignment** |

---

## Implementation Benefits

### Simplified Mode Benefits

| Benefit Area | Simplification | Impact |
|-------------|----------------|---------|
| **Address Generation** | Simple increment by bus width | Minimal logic complexity |
| **Size Checking** | No dynamic size validation | No validation logic needed |
| **Strobe Generation** | All strobes always high | Trivial implementation |
| **Timing** | Predictable single-size transfers | Optimal timing closure |

### Flexible Mode Benefits

| Benefit Area | Capability | Impact |
|-------------|------------|--------|
| **Data Placement** | Arbitrary 4-byte aligned placement | Maximum flexibility |
| **Bus Utilization** | Progressive alignment optimization | High efficiency achieved |
| **Chunk Control** | Precise byte-level validity | Optimal memory utilization |
| **Alignment Strategy** | Automatic alignment to boundaries | Performance optimization |

### Mode Selection Guidelines

| Interface Type | Recommended Mode | Rationale |
|----------------|------------------|-----------|
| **High-bandwidth data** | **Flexible** | Maximize throughput, handle arbitrary alignment |
| **Control/status** | **Simplified** | Predictable timing, minimal complexity |
| **Descriptors** | **Simplified** | Fixed-size structures, simple implementation |
| **Programs** | **Simplified** | Single-word writes, minimal overhead |
| **Flags** | **Simplified** | Fixed-size status, predictable behavior |

---

## Validation Requirements

### Simplified Mode Validation

| Validation Area | Requirements |
|----------------|-------------|
| **Address Alignment** | Verify all addresses aligned to full bus width |
| **Fixed Size** | Verify AxSIZE always matches DATA_WIDTH |
| **Full Strobes** | Verify w_strb is always all 1's |
| **Burst Type** | Verify AxBURST is always 2'b01 |

### Flexible Mode Validation

| Validation Area | Requirements |
|----------------|-------------|
| **Address Alignment** | Verify all addresses are 4-byte aligned |
| **Size Validation** | Verify AxSIZE matches actual transfer size |
| **Chunk Consistency** | Verify chunk enables match transfer size |
| **Strobe Generation** | Verify strobes generated correctly from chunks |
| **Progressive Alignment** | Verify alignment strategy optimization |
| **Boundary Checking** | Verify no 4KB boundary crossings |

### Common Validation

| Validation Area | Requirements |
|----------------|-------------|
| **No Wraparound** | Verify addresses never wrap around |
| **Incrementing Only** | Verify AxBURST is always 2'b01 |
| **Response Handling** | Verify proper response generation |
| **Error Conditions** | Verify alignment violation responses |

---

## Performance Characteristics

### Simplified Mode Performance

| Metric | Typical Value | Description |
|--------|---------------|-------------|
| **Latency** | 3 cycles | Address + Data + Response |
| **Throughput** | 1 transfer per clock | Sustained rate |
| **Efficiency** | 100% | Perfect bus utilization |
| **Complexity** | Minimal | Simple implementation |

### Flexible Mode Performance

| Metric | Alignment Phase | Optimized Phase | Description |
|--------|----------------|-----------------|-------------|
| **Latency** | 3-15 cycles | 3 cycles | Variable based on alignment |
| **Throughput** | Variable | 1 transfer per clock | Depends on alignment pattern |
| **Efficiency** | 25-100% | 100% | Improves with alignment |
| **Complexity** | Moderate | Minimal | Progressive optimization |

### Performance Optimization Strategy

**Flexible Mode Alignment Strategy:**
1. **Initial Phase**: Use largest possible transfer size for current alignment
2. **Progressive Phase**: Incrementally align to larger boundaries  
3. **Optimized Phase**: Use full bus-width transfers once aligned
4. **Result**: Achieve maximum efficiency while handling arbitrary starting addresses

This dual-mode approach provides the best of both worlds: simplified, predictable operation for control interfaces and flexible, high-performance operation for data interfaces.
