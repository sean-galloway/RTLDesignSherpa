# AXI4 Interface Specification and Assumptions

## Overview

This document defines the formal specification and assumptions for an AXI4 interface implementation with specific constraints that simplify the protocol complexity.

## Interface Parameters

| Parameter | Description | Valid Values | Default |
|-----------|-------------|--------------|---------|
| `DATA_WIDTH` | AXI data bus width in bits | 32, 64, 128, 256, 512, 1024 | 32 |
| `ADDR_WIDTH` | AXI address bus width in bits | 32, 64 | 32 |
| `ID_WIDTH` | AXI ID tag width in bits | 1-16 | 4 |
| `USER_WIDTH` | AXI user signal width in bits (optional) | 0-16 | 0 |

## Core Assumptions

### Assumption 1: Fixed Transfer Size
**Assumption**: All AXI transfers use the maximum transfer size equal to the bus width.

- **Implication**: `AxSIZE` is always set to match the data bus width
- **Rationale**: Maximizes bus utilization and simplifies address alignment
- **Implementation**: 
  - 32-bit bus → `AxSIZE = 3'b010` (4 bytes)
  - 64-bit bus → `AxSIZE = 3'b011` (8 bytes)
  - 128-bit bus → `AxSIZE = 3'b100` (16 bytes)

### Assumption 2: Incrementing Bursts Only
**Assumption**: All AXI bursts use incrementing address mode (`AxBURST = 2'b01`).

- **Implication**: No FIXED (`2'b00`) or WRAP (`2'b10`) bursts supported
- **Rationale**: Simplifies address generation logic and covers most use cases
- **Benefit**: Eliminates wrap boundary calculations and fixed address handling

## Protocol Requirements

### Address Channel Requirements

#### Write Address Channel (AW)
| Signal | Width | Direction | Required Values | Description |
|--------|-------|-----------|-----------------|-------------|
| `AWADDR` | `ADDR_WIDTH` | Master→Slave | Aligned to `AxSIZE` | Write address |
| `AWLEN` | 8 | Master→Slave | 0-255 | Burst length - 1 |
| `AWSIZE` | 3 | Master→Slave | **Fixed per bus width** | Transfer size |
| `AWBURST` | 2 | Master→Slave | **2'b01 (INCR only)** | Burst type |
| `AWID` | `ID_WIDTH` | Master→Slave | Any | Transaction ID |
| `AWLOCK` | 1 | Master→Slave | 1'b0 | Lock type (normal) |
| `AWCACHE` | 4 | Master→Slave | Implementation specific | Cache attributes |
| `AWPROT` | 3 | Master→Slave | Implementation specific | Protection attributes |
| `AWQOS` | 4 | Master→Slave | 4'b0000 | Quality of Service |
| `AWREGION` | 4 | Master→Slave | 4'b0000 | Region identifier |
| `AWUSER` | `USER_WIDTH` | Master→Slave | Optional | User-defined |
| `AWVALID` | 1 | Master→Slave | 0 or 1 | Address valid |
| `AWREADY` | 1 | Slave→Master | 0 or 1 | Address ready |

#### Read Address Channel (AR)
| Signal | Width | Direction | Required Values | Description |
|--------|-------|-----------|-----------------|-------------|
| `ARADDR` | `ADDR_WIDTH` | Master→Slave | Aligned to `AxSIZE` | Read address |
| `ARLEN` | 8 | Master→Slave | 0-255 | Burst length - 1 |
| `ARSIZE` | 3 | Master→Slave | **Fixed per bus width** | Transfer size |
| `ARBURST` | 2 | Master→Slave | **2'b01 (INCR only)** | Burst type |
| `ARID` | `ID_WIDTH` | Master→Slave | Any | Transaction ID |
| `ARLOCK` | 1 | Master→Slave | 1'b0 | Lock type (normal) |
| `ARCACHE` | 4 | Master→Slave | Implementation specific | Cache attributes |
| `ARPROT` | 3 | Master→Slave | Implementation specific | Protection attributes |
| `ARQOS` | 4 | Master→Slave | 4'b0000 | Quality of Service |
| `ARREGION` | 4 | Master→Slave | 4'b0000 | Region identifier |
| `ARUSER` | `USER_WIDTH` | Master→Slave | Optional | User-defined |
| `ARVALID` | 1 | Master→Slave | 0 or 1 | Address valid |
| `ARREADY` | 1 | Slave→Master | 0 or 1 | Address ready |

### Data Channel Requirements

#### Write Data Channel (W)
| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `WDATA` | `DATA_WIDTH` | Master→Slave | Write data |
| `WSTRB` | `DATA_WIDTH/8` | Master→Slave | Write strobes (byte enables) |
| `WLAST` | 1 | Master→Slave | Last transfer in burst |
| `WUSER` | `USER_WIDTH` | Master→Slave | User-defined (optional) |
| `WVALID` | 1 | Master→Slave | Write data valid |
| `WREADY` | 1 | Slave→Master | Write data ready |

#### Read Data Channel (R)
| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `RDATA` | `DATA_WIDTH` | Slave→Master | Read data |
| `RID` | `ID_WIDTH` | Slave→Master | Transaction ID |
| `RRESP` | 2 | Slave→Master | Read response |
| `RLAST` | 1 | Slave→Master | Last transfer in burst |
| `RUSER` | `USER_WIDTH` | Slave→Master | User-defined (optional) |
| `RVALID` | 1 | Slave→Master | Read data valid |
| `RREADY` | 1 | Master→Slave | Read data ready |

#### Write Response Channel (B)
| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `BID` | `ID_WIDTH` | Slave→Master | Transaction ID |
| `BRESP` | 2 | Slave→Master | Write response |
| `BUSER` | `USER_WIDTH` | Slave→Master | User-defined (optional) |
| `BVALID` | 1 | Slave→Master | Response valid |
| `BREADY` | 1 | Master→Slave | Response ready |

## Address Calculation Rules

### Incrementing Burst Address Generation
Given the constraints, address calculation is simplified:

```
First_Address = AWADDR (or ARADDR)
Address_N = First_Address + (N × Number_Bytes)

Where:
- N = Beat number (0, 1, 2, ...)
- Number_Bytes = DATA_WIDTH / 8
```

### Address Alignment Requirements
- **Start addresses** must be aligned to `Number_Bytes` boundaries
- **4KB boundary rule**: Bursts cannot cross 4KB (0x1000) boundaries
- **Maximum burst calculation**: `Max_Beats = (4KB - (Start_Address % 4KB)) / Number_Bytes`

## Response Codes

### RRESP and BRESP Encoding
| Value | Name | Description |
|-------|------|-------------|
| 2'b00 | OKAY | Normal access success |
| 2'b01 | EXOKAY | Exclusive access success |
| 2'b10 | SLVERR | Slave error |
| 2'b11 | DECERR | Decode error |

## Timing Requirements

### Handshake Protocol
1. **Valid-Ready Handshake**: Transfer occurs when both `VALID` and `READY` are high
2. **Valid Dependency**: `VALID` can be asserted without waiting for `READY`
3. **Ready Dependency**: `READY` can depend on `VALID`
4. **Valid Stability**: Once `VALID` is asserted, it must remain high until `READY` is asserted

### Reset Behavior
- **Active-low reset**: `aresetn` is the reset signal
- **Reset requirements**: All `VALID` signals must be low during reset
- **Reset recovery**: First cycle after reset deassertion, all `VALID` signals must be low

## Implementation Constraints

### Simplified Implementation Benefits
1. **Address Generation**: Simple increment by bus width
2. **Size Checking**: No dynamic size validation needed
3. **Burst Handling**: No wrap boundary calculations
4. **Memory Interface**: Predictable access patterns

### Verification Requirements
1. **Address Alignment**: Verify all addresses are properly aligned
2. **Burst Boundaries**: Verify no 4KB boundary crossings
3. **Handshake Compliance**: Verify all valid-ready handshakes
4. **Response Handling**: Verify proper response generation and handling

## Example Transaction

### 64-bit Bus Write Burst Example
```
Bus Width: 64 bits (8 bytes)
Start Address: 0x1000
Burst Length: 4 beats (AWLEN = 3)

Required Settings:
- AWSIZE = 3'b011 (8 bytes per transfer)
- AWBURST = 2'b01 (INCR)

Generated Addresses:
Beat 0: 0x1000
Beat 1: 0x1008  
Beat 2: 0x1010
Beat 3: 0x1018

Total Data Transferred: 32 bytes
```

This specification ensures a predictable, high-performance AXI4 interface suitable for most memory and streaming applications while significantly reducing implementation complexity.