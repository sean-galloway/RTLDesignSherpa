# AXI4-Lite Interface Specification and Assumptions

## Overview

This document defines the formal specification and assumptions for an AXI4-Lite interface implementation. AXI4-Lite is a subset of AXI4 optimized for simple, lightweight control register interfaces with inherent protocol simplifications.

## Interface Summary

### Number of Interfaces

- **2 Master Read Interface**: Single read channel for Monitor Packets (one for each Source and Sink)
- **2 Master Write Interface**: Single write channel for Monitor Packets plus a timestamp (one for each Source and Sink)

### Interface Parameters

| Parameter | Description | Valid Values | Default |
|-----------|-------------|--------------|---------|
| `DATA_WIDTH` | AXI data bus width in bits | 32, 64 | 32, 64 |
| `ADDR_WIDTH` | AXI address bus width in bits | 32, 64 | 37 |
| `STRB_WIDTH` | Write strobe width | `DATA_WIDTH/8` | 8 |

## Core Protocol Assumptions

### Inherent AXI4-Lite Simplifications

AXI4-Lite protocol inherently provides the following constraints:

| Constraint | Description |
|------------|-------------|
| **Single Transfers Only** | No burst transactions supported |
| **No Transaction IDs** | All transactions are in-order |
| **Fixed Transfer Size** | Always uses full data bus width |
| **No User Signals** | Simplified interface without user-defined extensions |

### Implementation Assumptions

#### Assumption 1: Address Alignment to Data Bus Width

| Aspect | Requirement |
|--------|-------------|
| **Alignment Rule** | All AXI4-Lite transactions aligned to data bus width |
| **32-bit bus alignment** | Address[1:0] must be 2'b00 (4-byte aligned) |
| **64-bit bus alignment** | Address[2:0] must be 3'b000 (8-byte aligned) |
| **Rationale** | Maximizes bus efficiency and eliminates unaligned access complexity |
| **Benefit** | Simplifies address decode and data steering logic |

#### Assumption 2: Fixed Transfer Size

| Aspect | Requirement |
|--------|-------------|
| **Transfer Size Rule** | All transfers use maximum size equal to bus width |
| **32-bit bus** | AxSIZE = 3'b010 (4 bytes) |
| **64-bit bus** | AxSIZE = 3'b011 (8 bytes) |
| **Rationale** | Maximizes bus utilization and simplifies control logic |
| **Benefit** | No size decode logic required |

#### Assumption 3: No Address Wraparound

| Aspect | Requirement |
|--------|-------------|
| **Wraparound Rule** | Transactions never wrap around top of address space |
| **Rationale** | Control register accesses never require wraparound behavior |
| **Benefit** | Simplified address boundary checking |

#### Assumption 4: Standard Protection Attributes

| Access Type | AxPROT Value | Description |
|-------------|-------------|-------------|
| **Normal Access** | 3'b000 | Data, secure, unprivileged |
| **Privileged Access** | 3'b001 | Data, secure, privileged |
| **Rationale** | | Covers the majority of control register access patterns |

## Master Read Interface Specification

### Read Address Channel (AR)

| Signal | Width | Direction | Required Values | Description |
|--------|-------|-----------|-----------------|-------------|
| `ar_addr` | `ADDR_WIDTH` | Master→Slave | **8-byte aligned** | Read address |
| `ar_prot` | 3 | Master→Slave | Implementation specific | Protection attributes |
| `ar_valid` | 1 | Master→Slave | 0 or 1 | Address valid |
| `ar_ready` | 1 | Slave→Master | 0 or 1 | Address ready |

### Read Data Channel (R)

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `r_data` | 64 | Slave→Master | Read data |
| `r_resp` | 2 | Slave→Master | Read response |
| `r_valid` | 1 | Slave→Master | Read data valid |
| `r_ready` | 1 | Master→Slave | Read data ready |

### AXI4-Lite Simplifications (Read)

| Removed Signal | AXI4 Usage | AXI4-Lite Reason |
|----------------|-------------|-------------------|
| **ar_id** | Transaction ID | Single transfers, no transaction IDs |
| **ar_len** | Burst length | Single transfers only |
| **ar_size** | Transfer size | Fixed to bus width |
| **ar_burst** | Burst type | Single transfers only |
| **ar_lock** | Lock type | Simplified access model |
| **ar_cache** | Cache attributes | Simplified memory model |
| **ar_qos** | Quality of Service | Simplified priority model |
| **ar_region** | Region identifier | Simplified address space |
| **ar_user** | User-defined | Simplified interface |
| **r_id** | Transaction ID | No transaction IDs needed |
| **r_last** | Last transfer | Single transfers only |
| **r_user** | User-defined | Simplified interface |

## Master Write Interface Specification

### Write Address Channel (AW)

| Signal | Width | Direction | Required Values | Description |
|--------|-------|-----------|-----------------|-------------|
| `aw_addr` | `ADDR_WIDTH` | Master→Slave | **8-byte aligned** | Write address |
| `aw_prot` | 3 | Master→Slave | Implementation specific | Protection attributes |
| `aw_valid` | 1 | Master→Slave | 0 or 1 | Address valid |
| `aw_ready` | 1 | Slave→Master | 0 or 1 | Address ready |

### Write Data Channel (W)

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `w_data` | 32 | Master→Slave | Write data |
| `w_strb` | 4 | Master→Slave | Write strobes (byte enables) |
| `w_valid` | 1 | Master→Slave | Write data valid |
| `w_ready` | 1 | Slave→Master | Write data ready |

### Write Response Channel (B)

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `b_resp` | 2 | Slave→Master | Write response |
| `b_valid` | 1 | Slave→Master | Response valid |
| `b_ready` | 1 | Master→Slave | Response ready |

### AXI4-Lite Simplifications (Write)

| Removed Signal | AXI4 Usage | AXI4-Lite Reason |
|----------------|-------------|-------------------|
| **aw_id** | Transaction ID | Single transfers, no transaction IDs |
| **aw_len** | Burst length | Single transfers only |
| **aw_size** | Transfer size | Fixed to bus width |
| **aw_burst** | Burst type | Single transfers only |
| **aw_lock** | Lock type | Simplified access model |
| **aw_cache** | Cache attributes | Simplified memory model |
| **aw_qos** | Quality of Service | Simplified priority model |
| **aw_region** | Region identifier | Simplified address space |
| **aw_user** | User-defined | Simplified interface |
| **w_last** | Last transfer | Single transfers only |
| **w_user** | User-defined | Simplified interface |
| **b_id** | Transaction ID | No transaction IDs needed |
| **b_user** | User-defined | Simplified interface |

## Address Requirements

### Address Alignment Rules

| Alignment Type | Formula | Description |
|----------------|---------|-------------|
| **Valid Address** | (Address % 4) == 0 | Must be 8-byte aligned |
| **Mandatory Alignment** | Address[2:0] must be 3'b000 | Per Assumption 1 |

### Address Validation Examples

| Address Category | Examples | Status |
|------------------|----------|--------|
| **Valid (84byte aligned)** | 0x1000, 0x1004, 0x1008, 0x100C | Accepted |
| **Invalid (unaligned)** | 0x1001, 0x1002, 0x1003 | DECERR response |

## Response Codes

### Response Code Specification

| Value | Name | Description | Usage in Control Registers |
|-------|------|-------------|----------------------------|
| **2'b00** | OKAY | Normal access success | Successful register access |
| **2'b01** | EXOKAY | Exclusive access success | **Not used in AXI4-Lite** |
| **2'b10** | SLVERR | Slave error | Invalid register access |
| **2'b11** | DECERR | Decode error | **Address decode failure or misalignment** |

### Response Usage Guidelines

| Response Type | Usage | Description |
|---------------|-------|-------------|
| **OKAY** | Normal completion | Successful register access |
| **EXOKAY** | Not applicable | AXI4-Lite doesn't support exclusive accesses |
| **SLVERR** | Register error | Invalid register operation |
| **DECERR** | Address error | Misalignment or decode failure per Assumption 1 |

## Protection Signal Usage

### Protection Signal Encoding

| Bit | Name | Description | Recommended Usage |
|-----|------|-------------|-------------------|
| **[0]** | Privileged | 0=Normal, 1=Privileged | Set based on processor mode |
| **[1]** | Non-secure | 0=Secure, 1=Non-secure | Set based on security domain |
| **[2]** | Instruction | 0=Data, 1=Instruction | Always 0 for control registers |

### Common Protection Patterns

| Pattern | AxPROT Value | Description |
|---------|-------------|-------------|
| **Normal Data Access** | 3'b000 | Standard register access |
| **Privileged Data Access** | 3'b001 | Privileged register access |
| **Debug Access** | 3'b010 | Debug register access |
| **Privileged Debug** | 3'b011 | Privileged debug access |

## Implementation Benefits

### Simplified Control Register Interface

| Benefit Area | Simplification | Impact |
|-------------|----------------|---------|
| **Address Decode** | Simple 8-byte aligned address comparison | Reduced decode logic |
| **Transaction Handling** | No burst or ID tracking required | Simplified state machines |
| **Flow Control** | Straightforward valid-ready handshakes | Reduced complexity |
| **Response Generation** | Simple OKAY/SLVERR/DECERR responses | Minimal response logic |
| **Size Handling** | Fixed 64-bit transfers only | No size decode needed |

### Address Decode Implementation

| Implementation Aspect | Method | Benefit |
|----------------------|--------|---------|
| **4-byte Alignment Check** | addr[1:0] == 2'b00 | Simple bit masking |
| **Address Range Check** | addr >= base && addr <= limit | Simple comparisons |
| **Combined Check** | alignment_ok && range_ok | Single decode decision |

### Error Generation Logic

| Error Condition | Check | Response |
|----------------|-------|----------|
| **Address Misalignment** | addr[1:0] != 2'b00 | Generate DECERR |
| **Address Out of Range** | !addr_in_range(addr) | Generate DECERR |
| **Register Error** | register_error_condition | Generate SLVERR |
| **Normal Access** | All checks pass | Generate OKAY |

## Timing Requirements

### Handshake Protocol

| Protocol Rule | Requirement | Description |
|---------------|-------------|-------------|
| **Valid-Ready Transfer** | Transfer occurs when both VALID and READY are high | Standard AXI handshake |
| **Valid Independence** | VALID can be asserted independently of READY | Master controls valid |
| **Ready Dependency** | READY can depend on VALID state | Slave controls ready |
| **Signal Stability** | Once VALID asserted, all signals stable until READY | Data integrity |

### Channel Dependencies

| Dependency | Requirement | Description |
|------------|-------------|-------------|
| **Write Channels** | AW and W channels are independent | Can be presented in any order |
| **Write Response** | B channel waits for both AW and W completion | Response dependency |
| **Read Channels** | R channel waits for AR channel completion | Response dependency |
| **Transaction Ordering** | Multiple outstanding transactions not supported | Inherent AXI4-Lite limitation |

### Reset Behavior

| Reset Phase | Requirement | Description |
|-------------|-------------|-------------|
| **Active Reset** | aresetn is active-low reset signal | Standard AXI reset |
| **Reset Requirements** | All VALID signals deasserted during reset | Clean reset state |
| **Reset Recovery** | All VALID signals low after reset deassertion | Proper startup |

## Validation Requirements

### Functional Validation

| Validation Area | Requirements |
|----------------|-------------|
| **Address Alignment** | Verify all accesses are 8-byte aligned per Assumption 1 |
| **Fixed Size** | Verify all transfers are full 64-bit width per Assumption 2 |
| **Response Correctness** | Verify appropriate response codes (DECERR for misaligned access) |
| **Handshake Compliance** | Verify all valid-ready handshakes |
| **Register Behavior** | Verify read/write register functionality |
| **No Wraparound** | Verify no address wraparound scenarios per Assumption 3 |

### Timing Validation

| Validation Area | Requirements |
|----------------|-------------|
| **Setup/Hold** | Verify signal timing requirements |
| **Reset Behavior** | Verify proper reset sequence |
| **Back-pressure** | Verify ready signal behavior under load |

### Error Injection Testing

| Test Type | Injection Method | Expected Response |
|-----------|------------------|-------------------|
| **Misaligned Address** | Inject addresses with addr[2:0] != 0 | DECERR response |
| **Out of Range** | Inject addresses outside valid range | DECERR response |
| **Register Errors** | Inject register-specific errors | SLVERR response |

## Example Transactions

### 64-bit Register Write

| Parameter | Value | Description |
|-----------|-------|-------------|
| **Bus Width** | 64 bits (8 bytes) | Data bus configuration |
| **Target Address** | 0x1000 (8-byte aligned) | Valid aligned address |
| **Write Data** | 0xDEADBEEFCAFEBABE | 64-bit data value |
| **Required Settings** | aw_addr=0x1000, aw_prot=3'b000, w_data=0xDEADBEEFCAFEBABE, w_strb=8'b11111111 | Transaction configuration |

### AW Transaction Flow

| Step | Action | Signal States |
|------|--------|---------------|
| **1** | Assert aw_valid with address | aw_valid=1, aw_addr=0x1000 |
| **2** | Assert w_valid with data | w_valid=1, w_data=0xDEADBEEFCAFEBABE |
| **3** | Wait for handshakes | aw_ready=1, w_ready=1 |
| **4** | Wait for response | b_valid=1, b_resp=OKAY |
| **5** | Complete transaction | b_ready=1 |

### 64-bit Register Read

| Parameter | Value | Description |
|-----------|-------|-------------|
| **Bus Width** | 64 bits (8 bytes) | Data bus configuration |
| **Target Address** | 0x1008 (8-byte aligned) | Valid aligned address |
| **Required Settings** | ar_addr=0x1008, ar_prot=3'b000 | Transaction configuration |

### AR Transaction Flow

| Step | Action | Signal States |
|------|--------|---------------|
| **1** | Assert ar_valid with address | ar_valid=1, ar_addr=0x1008 |
| **2** | Wait for address handshake | ar_ready=1 |
| **3** | Wait for data response | r_valid=1, r_resp=OKAY |
| **4** | Complete transaction | r_ready=1 |
| **5** | Capture data | r_data (64 bits) |

### Misaligned Address Example

| Parameter | Value | Description |
|-----------|-------|-------------|
| **Bus Width** | 64 bits (8 bytes) | Data bus configuration |
| **Target Address** | 0x1004 (misaligned) | Invalid address |
| **Expected Behavior** | Address decode detects misalignment → DECERR response → No register access | Error handling |

## Common Use Cases

### Typical Applications

| Application | Description |
|-------------|-------------|
| **Control/Status Registers** | 64-bit device configuration and monitoring |
| **Memory-Mapped Peripherals** | Simple register-based devices |
| **Debug Interfaces** | Debug and trace control registers |
| **Configuration Space** | PCIe configuration space access |
| **Performance Counters** | 64-bit performance monitoring registers |

### Performance Considerations

| Consideration | Impact | Description |
|---------------|---------|-------------|
| **Latency** | Single-cycle responses preferred | Simple registers |
| **Throughput** | Limited by single outstanding transaction | AXI4-Lite constraint |
| **Efficiency** | 64-bit transfers maximize data efficiency | Modern system optimization |
