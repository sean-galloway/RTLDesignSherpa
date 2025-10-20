# APB Interface Specification and Assumptions

## Overview

This document defines the formal specification and assumptions for an APB (Advanced Peripheral Bus) interface implementation. APB is the simplest ARM AMBA protocol, designed for low-power, low-speed control register interfaces with minimal logic overhead.

This implementation includes advanced features such as dynamic clock gating for power optimization and robust clock domain crossing (CDC) handshaking for multi-clock environments.

## Interface Summary

### Number of Interfaces

- **2 APB Interfaces**: Source and Sink
- **Source Interface**: Master drives transactions to peripheral
- **Sink Interface**: Peripheral responds to master requests

### Interface Parameters

| Parameter | Description | Valid Values | Default |
|-----------|-------------|--------------|---------|
| `DATA_WIDTH` | APB data bus width in bits | 8, 16, 32 | 32 |
| `ADDR_WIDTH` | APB address bus width in bits | 16, 24, 32 | 32 |
| `STRB_WIDTH` | Write strobe width (APB4 only) | `DATA_WIDTH/8` | 4 |
| `NUM_SLAVES` | Number of peripheral slaves | 1-32 | 1 |
| `DEPTH` | Internal buffer depth | 2+ | 2 |

## Core Protocol Assumptions

### Inherent APB Simplifications

APB protocol inherently provides the following constraints:

1. **Single Master Only**: Only one bus master supported
2. **Non-Pipelined**: One transaction completes before next begins
3. **Simple 2-Phase Protocol**: Setup phase followed by access phase
4. **No Burst Transfers**: Only single transfers supported
5. **In-Order Completion**: No out-of-order transaction capability

### Implementation Assumptions

#### Assumption 1: Word-Aligned Access Only

| Aspect | Requirement |
|--------|-------------|
| **Alignment Rule** | All APB transfers are aligned to natural word boundaries |
| **8-bit transfers** | Byte aligned (no restriction) |
| **16-bit transfers** | 2-byte aligned (PADDR[0] = 0) |
| **32-bit transfers** | 4-byte aligned (PADDR[1:0] = 2'b00) |
| **Rationale** | Simplifies peripheral decode logic and ensures efficient access |

#### Assumption 2: Standard Transfer Sizes

| Bus Width | Supported Transfer Sizes | Rationale |
|-----------|-------------------------|-----------|
| **32-bit bus** | 8-bit, 16-bit, 32-bit | Covers typical register access patterns |
| **16-bit bus** | 8-bit, 16-bit | Keeps decode logic simple |
| **8-bit bus** | 8-bit only | Minimal complexity |

#### Assumption 3: Single-Cycle Default Operation

| Aspect | Requirement |
|--------|-------------|
| **Default Behavior** | Most peripherals respond in a single cycle (PREADY tied high) |
| **Optimization** | PREADY optimization for simple registers |
| **Exception** | Complex peripherals may use PREADY for wait states |
| **Rationale** | Minimizes latency for control register access |

## Interface Signal Specification

### Clock and Reset Signals

| Signal | IO | Description |
|--------|-----------|-------------|
| `src_clk` | I | Source APB clock signal |
| `snk_rdata[31:0]` | I | Read data |
| `src_wdata[31:0]` | O | Write data |
### Address and Control Signals

| Signal | Width | Direction | Required Values | Description |
|--------|-------|-----------|-----------------|-------------|
| `src_addr` | 11 bits | Master->Slave | **Aligned per transfer size** | Peripheral address (2KB space) |
| `src_sel` | 1 | Master->Slave | 0 or 1 | Peripheral select |
| `src_enable` | 1 | Master->Slave | 0 or 1 | Enable signal |
| `src_write` | 1 | Master->Slave | 0 or 1 | Write enable (1=write, 0=read) |
| `snk_addr` | 11 bits | Master->Slave | **Aligned per transfer size** | Peripheral address (2KB space) |
| `snk_sel` | 1 | Master->Slave | 0 or 1 | Peripheral select |
| `snk_enable` | 1 | Master->Slave | 0 or 1 | Enable signal |
| `snk_write` | 1 | Master->Slave | 0 or 1 | Write enable (1=write, 0=read) |

### Data Signals

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `src_wdata` | 32 | Master->Slave | Write data |
| `src_rdata` | 32 | Slave->Master | Read data |
| `snk_wdata` | 32 | Master->Slave | Write data |
| `snk_rdata` | 32 | Slave->Master | Read data |

### Response Signals

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `src_ready` | 1 | Slave->Master | Transfer ready |
| `src_slverr` | 1 | Slave->Master | Slave error |
| `snk_ready` | 1 | Slave->Master | Transfer ready |
| `snk_slverr` | 1 | Slave->Master | Slave error |

## Address Space Configuration

### Address Range Specification

| Parameter | Value | Description |
|-----------|-------|-------------|
| **Address Width** | 11 bits (src_addr[10:0]) | Full address space |
| **Address Space** | 2KB (2048 bytes) | Total addressable space |
| **Register Alignment** | 32-bit aligned (4-byte boundaries) | Address constraints |
| **Usable Addresses** | 0x000 to 0x7FF | Valid address range |

### Address Decode Implementation

| Register | Address Bits | Address Value | Description |
|----------|-------------|---------------|-------------|
| **reg0** | src_addr[10:2] == 9'h000 | 0x000 | First register |
| **reg1** | src_addr[10:2] == 9'h001 | 0x004 | Second register |
| **reg2** | src_addr[10:2] == 9'h002 | 0x008 | Third register |
| **...** | ... | ... | Up to 512 32-bit registers |

## Transaction Protocol

### 2-Phase Transaction States

| Phase | State | Duration | Signal Requirements |
|-------|-------|----------|-------------------|
| **Setup (T1)** | SETUP | 1 clock cycle | src_sel=1, src_enable=0, address/data stable |
| **Access (T2+)** | ACCESS | 1+ clock cycles | src_sel=1, src_enable=1, wait for src_ready |
| **Idle** | IDLE | Variable | src_sel=0, src_enable=0 |

### State Transitions

| Current State | Next State | Condition | Description |
|---------------|------------|-----------|-------------|
| **IDLE** | SETUP | Transaction start | Master drives address and control |
| **SETUP** | ACCESS | Clock edge | Master asserts src_enable |
| **ACCESS** | IDLE | src_ready=1 | Transaction completes |
| **ACCESS** | ACCESS | src_ready=0 | Wait state continues |

### Transaction Timing Requirements

| Timing Parameter | Requirement | Description |
|------------------|-------------|-------------|
| **Setup Time** | All master signals stable before rising src_clk | Signal stability |
| **Hold Time** | All master signals held after rising src_clk | Signal stability |
| **Output Delay** | Slave outputs valid after rising src_clk | Response timing |

## Advanced Features

### Dynamic Clock Gating

| Feature | Description | Benefit |
|---------|-------------|---------|
| **Automatic Power Reduction** | Clocks gated when no activity detected | Significant power savings |
| **Configurable Idle Threshold** | Programmable idle count before gating | Tunable power/performance |
| **Multi-Domain Support** | Independent gating for APB (PCLK) and backend (ACLK) | Flexible power management |
| **Graceful Handoff** | Ready signals forced to zero during gating | Protocol compliance |
| **Activity Detection** | Monitors valid signals across interfaces | Intelligent gating control |

### Clock Domain Crossing (CDC) Handshaking

| Feature | Description | Benefit |
|---------|-------------|---------|
| **Arbitrary Frequency Support** | Works across any clock frequency ratios | Design flexibility |
| **Robust Reliability** | Proven handshaking with proper synchronization | Zero data loss |
| **Command/Response Separation** | Independent CDC paths | Maximum throughput |
| **Skid Buffer Integration** | Internal buffering prevents backpressure | Smooth operation |
| **Deterministic Latency** | Predictable timing characteristics | System predictability |

### Buffering and Flow Control

| Feature | Description | Benefit |
|---------|-------------|---------|
| **Internal Skid Buffers** | Configurable depth buffering | Improved performance |
| **Backpressure Handling** | Proper ready/valid handshaking | Flow control |
| **Command Pipelining** | Backend processes while APB handles responses | Efficiency |
| **Response Queuing** | Responses buffered for varying latencies | Latency tolerance |

## Error Handling

### Error Response Specification

| Condition | src_slverr | Description |
|-----------|----------|-------------|
| **Successful access** | 0 | Normal completion |
| **Address decode error** | 1 | Invalid address |
| **Protection violation** | 1 | Insufficient privilege |
| **Backend error** | 1 | Downstream error condition |

### Error Response Timing

| Timing Requirement | Description |
|-------------------|-------------|
| **src_slverr Validity** | Must be valid when src_ready is asserted |
| **Error Completion** | Error response completes transaction normally |
| **Master Responsibility** | Master must check src_slverr status |

## Reset Behavior

### Reset Requirements

| Reset Phase | Signal Requirements | Description |
|-------------|-------------------|-------------|
| **Reset Assertion** | All outputs to known states | Deterministic reset |
| **Reset Deassertion** | src_sel=0, src_enable=0 in first cycle | Clean startup |
| **Reset Values** | src_ready=0, src_slverr=0, src_rdata=0 | Default states |

## Implementation Variants

### Available Implementations

| Variant | Features | Use Case |
|---------|----------|----------|
| **Basic APB Slave** | Single clock domain, internal buffering | Simple peripherals |
| **CDC-Enabled APB Slave** | Dual clock domain (PCLK/ACLK) | Mixed-frequency systems |
| **Power-Optimized APB Slave** | Dynamic clock gating | Power-sensitive designs |

## Performance Characteristics

### Latency Specifications

| Metric | Value | Description |
|--------|-------|-------------|
| **Minimum Read Latency** | 2 clock cycles | Setup + access phases |
| **Minimum Write Latency** | 2 clock cycles | Setup + access phases |
| **CDC Additional Latency** | 2-6 clock cycles | Depends on clock relationships |
| **Buffer Latency** | Minimal | Skid buffer design |

### Throughput Specifications

| Metric | Value | Description |
|--------|-------|-------------|
| **Single Transaction** | 2 clocks minimum | Basic transaction time |
| **Back-to-back Transactions** | Limited by src_ready | Depends on peripheral |
| **CDC Throughput** | Maintained across domains | Proper buffering |

### Power Consumption

| Power Category | Characteristics | Description |
|----------------|-----------------|-------------|
| **Active Power** | Standard CMOS logic | Normal operation |
| **Idle Power** | Significantly reduced with clock gating | Power optimization |
| **Gating Overhead** | Minimal additional logic | Efficient implementation |

## Validation Requirements

### Functional Validation

| Validation Area | Requirements |
|----------------|-------------|
| **Protocol Compliance** | Verify 2-phase setup/access sequence |
| **Address Decode** | Verify 11-bit address handling and alignment |
| **Error Response** | Verify src_slverr generation and handling |
| **Wait States** | Verify src_ready functionality |
| **CDC Operation** | Verify cross-clock domain transfers |
| **Clock Gating** | Verify power management behavior |
| **Buffer Operation** | Verify skid buffer and flow control |

### Timing Validation

| Validation Area | Requirements |
|----------------|-------------|
| **Setup/Hold** | Verify signal timing requirements |
| **Reset Sequence** | Verify proper reset behavior |
| **Multi-Clock** | Verify CDC timing across frequency ranges |
| **Gating Transitions** | Verify clock enable/disable timing |

## Example Transactions

### 32-bit Register Write

| Clock Cycle | src_sel | src_enable | src_write | src_addr | src_wdata | src_ready | Phase |
|-------------|---------|------------|-----------|----------|-----------|-----------|-------|
| 1 | 1 | 0 | 1 | 0x100 | 0xABCD | 0 | Setup |
| 2 | 1 | 1 | 1 | 0x100 | 0xABCD | 1 | Access |
| 3 | 0 | 0 | - | - | - | 0 | Idle |

### 32-bit Register Read with Wait State

| Clock Cycle | src_sel | src_enable | src_write | src_addr | src_rdata | src_ready | Phase |
|-------------|---------|------------|-----------|----------|-----------|-----------|-------|
| 1 | 1 | 0 | 0 | 0x104 | - | 0 | Setup |
| 2 | 1 | 1 | 0 | 0x104 | - | 0 | Access |
| 3 | 1 | 1 | 0 | 0x104 | 0x1234 | 1 | Complete |
| 4 | 0 | 0 | - | - | - | 0 | Idle |
