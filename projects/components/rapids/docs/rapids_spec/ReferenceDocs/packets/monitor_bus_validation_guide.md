# Monitor Bus Architecture and Validation Guide

## Overview

The monitor bus system provides comprehensive event monitoring, error detection, and performance tracking across multiple protocol interfaces (AXI, Network, APB) within an SoC. This document serves as a validation guide for understanding the architecture, packet format, routing mechanisms, and validation considerations.

## Architecture Overview

### System Components

```
+-----------------------------------------------------------------+
|                        SoC Unit                                 |
+-----------------------------------------------------------------+
|  +---------+  +---------+  +---------+  +---------+           |
|  |   AXI   |  |  Network   |  |   APB   |  | Custom  |           |
|  |Interface|  |Interface|  |Interface|  |Interface|           |
|  +----+----+  +----+----+  +----+----+  +----+----+           |
|       |            |            |            |                |
|       +------------+------------+------------+                |
|                    |            |                             |
|              +-----▼------------▼-----+                       |
|              |  Monitor Bus Arbiter   |                       |
|              |   (Packet Router)      |                       |
|              +-----+------------------+                       |
|                    |                                          |
+--------------------+------------------------------------------+
|                    ▼                                          |
|  +---------------------------------------------------------+  |
|  |              Central Monitor Hub                       |  |
|  |                                                         |  |
|  |  +-----------------+    +-----------------------------+ |  |
|  |  | Interrupt       |    | Memory-Mapped Event Buffer | |  |
|  |  | Controller      |    |                             | |  |
|  |  |                 |    | +---------+ +-------------+ | |  |
|  |  | • ERROR Events  |    | |  Base   | |   Limit     | | |  |
|  |  | • TIMEOUT Events|    | |Register | |  Register   | | |  |
|  |  |                 |    | +---------+ +-------------+ | |  |
|  |  +-----------------+    +-----------------------------+ |  |
|  +---------------------------------------------------------+  |
+-----------------------------------------------------------------+
```

### Packet Routing Logic

1. **Local Generation**: Interface monitors generate 64-bit monitor packets
2. **Central Collection**: Packets are routed to a central monitor hub
3. **Classification**: Packets are classified based on `packet_type` field
4. **Routing Decision**:
   - **ERROR/TIMEOUT packets** -> Interrupt Controller (64-bit packet only)
   - **All other packets** -> Memory-mapped circular buffer (64-bit packet + 32-bit timestamp = 96 bits total)

## Monitor Packet Format

### 64-bit Packet Structure

```
+---------+----------+------------+------------+----------+----------+----------------------------------+
|  63:60  |  59:58   |   57:54    |   53:48    |  47:44   |  43:36   |              35:0                |
+---------+----------+------------+------------+----------+----------+----------------------------------+
|Pkt Type | Protocol | Event Code | Channel ID | Unit ID  | Agent ID |           Event Data             |
| 4 bits  |  2 bits  |   4 bits   |   6 bits   |  4 bits  |  8 bits  |            36 bits               |
+---------+----------+------------+------------+----------+----------+----------------------------------+
```

### Field Descriptions

| Field | Bits | Description |
|-------|------|-------------|
| **Packet Type** | [63:60] | Event category (Error, Completion, Threshold, etc.) |
| **Protocol** | [59:58] | Source protocol (AXI=00, Network=01, APB=10, Custom=11) |
| **Event Code** | [57:54] | Specific event within the packet type category |
| **Channel ID** | [53:48] | Interface-specific channel/ID information |
| **Unit ID** | [47:44] | Subsystem identifier within the SoC |
| **Agent ID** | [43:36] | Specific module/agent identifier |
| **Event Data** | [35:0] | Event-specific payload data |

### Packet Types and Routing

| Packet Type | Value | Routing Destination | Interrupt Generated | Size |
|-------------|-------|-------------------|-------------------|------|
| **PktTypeError** | 4'h0 | Interrupt Controller | [PASS] Yes | 64 bits |
| **PktTypeTimeout** | 4'h3 | Interrupt Controller | [PASS] Yes | 64 bits |
| **PktTypeCompletion** | 4'h1 | Memory Buffer + Timestamp | [FAIL] No | 96 bits |
| **PktTypeThreshold** | 4'h2 | Memory Buffer + Timestamp | [FAIL] No | 96 bits |
| **PktTypePerf** | 4'h4 | Memory Buffer + Timestamp | [FAIL] No | 96 bits |
| **PktTypeCredit** | 4'h5 | Memory Buffer + Timestamp | [FAIL] No | 96 bits |
| **PktTypeChannel** | 4'h6 | Memory Buffer + Timestamp | [FAIL] No | 96 bits |
| **PktTypeStream** | 4'h7 | Memory Buffer + Timestamp | [FAIL] No | 96 bits |
| **PktTypeAddrMatch** | 4'h8 | Memory Buffer + Timestamp | [FAIL] No | 96 bits |
| **PktTypeAPB** | 4'h9 | Memory Buffer + Timestamp | [FAIL] No | 96 bits |
| **PktTypeDebug** | 4'hF | Memory Buffer + Timestamp | [FAIL] No | 96 bits |

## Protocol-Specific Event Codes

### AXI Protocol Events

#### Error Events (PktTypeError + PROTOCOL_AXI)
| Event Code | Name | Description |
|------------|------|-------------|
| 4'h0 | AXI_ERR_RESP_SLVERR | Slave error response received |
| 4'h1 | AXI_ERR_RESP_DECERR | Decode error response received |
| 4'h2 | AXI_ERR_DATA_ORPHAN | Data transfer without corresponding address |
| 4'h3 | AXI_ERR_RESP_ORPHAN | Response without corresponding transaction |
| 4'h4 | AXI_ERR_PROTOCOL | Protocol violation detected |
| 4'h5 | AXI_ERR_BURST_LENGTH | Invalid burst length specified |
| 4'h6 | AXI_ERR_BURST_SIZE | Invalid burst size specified |
| 4'h7 | AXI_ERR_BURST_TYPE | Invalid burst type specified |
| 4'h8 | AXI_ERR_ID_COLLISION | Transaction ID collision detected |
| 4'h9 | AXI_ERR_WRITE_BEFORE_ADDR | Write data received before address |

#### Timeout Events (PktTypeTimeout + PROTOCOL_AXI)
| Event Code | Name | Description |
|------------|------|-------------|
| 4'h0 | AXI_TIMEOUT_CMD | Command/Address phase timeout |
| 4'h1 | AXI_TIMEOUT_DATA | Data phase timeout |
| 4'h2 | AXI_TIMEOUT_RESP | Response phase timeout |
| 4'h3 | AXI_TIMEOUT_HANDSHAKE | Handshake timeout (ready/valid) |
| 4'h4 | AXI_TIMEOUT_BURST | Burst completion timeout |

### Network Protocol Events

#### Error Events (PktTypeError + PROTOCOL_MNOC)
| Event Code | Name | Description |
|------------|------|-------------|
| 4'h0 | NETWORK_ERR_PARITY | Parity error in header/payload/ACK |
| 4'h1 | NETWORK_ERR_PROTOCOL | Protocol violation detected |
| 4'h2 | NETWORK_ERR_OVERFLOW | Buffer or credit overflow |
| 4'h3 | NETWORK_ERR_UNDERFLOW | Buffer or credit underflow |
| 4'h4 | NETWORK_ERR_ORPHAN | Orphaned packet or ACK |
| 4'h5 | NETWORK_ERR_INVALID | Invalid packet type/channel/payload |
| 4'h6 | NETWORK_ERR_HEADER_CRC | Header CRC error |
| 4'h7 | NETWORK_ERR_PAYLOAD_CRC | Payload CRC error |

#### Credit Events (PktTypeCredit + PROTOCOL_MNOC)
| Event Code | Name | Description |
|------------|------|-------------|
| 4'h0 | NETWORK_CREDIT_ALLOCATED | Credits allocated to channel |
| 4'h1 | NETWORK_CREDIT_CONSUMED | Credits consumed by packet transmission |
| 4'h2 | NETWORK_CREDIT_RETURNED | Credits returned after ACK |
| 4'h3 | NETWORK_CREDIT_OVERFLOW | Credit count overflow detected |
| 4'h4 | NETWORK_CREDIT_UNDERFLOW | Credit count underflow detected |

### APB Protocol Events

#### Error Events (PktTypeError + PROTOCOL_APB)
| Event Code | Name | Description |
|------------|------|-------------|
| 4'h0 | APB_ERR_PSLVERR | Peripheral slave error (PSLVERR asserted) |
| 4'h1 | APB_ERR_SETUP_VIOLATION | Setup phase protocol violation |
| 4'h2 | APB_ERR_ACCESS_VIOLATION | Access phase protocol violation |
| 4'h3 | APB_ERR_STROBE_ERROR | Write strobe (PSTRB) error |
| 4'h4 | APB_ERR_ADDR_DECODE | Address decode error |
| 4'h5 | APB_ERR_PROT_VIOLATION | Protection violation (PPROT) |

## Memory Buffer Management

### Memory Buffer Entry Format

When non-ERROR/TIMEOUT packets are written to the memory buffer, they are expanded from 64 bits to 96 bits by adding a 32-bit timestamp:

```
Memory Buffer Entry (96 bits):
+------------------------------------------------------------------+----------------------------------+
|                    Original Monitor Packet                      |         Timestamp                |
|                         64 bits                                 |         32 bits                  |
+------------------------------------------------------------------+----------------------------------+
| PktType | Protocol | EventCode | ChannelID | UnitID | AgentID | EventData |      Hardware Timestamp      |
|  4 bits |  2 bits  |  4 bits   |  6 bits   | 4 bits | 8 bits |  36 bits  |           32 bits            |
+------------------------------------------------------------------+----------------------------------+
```

**Note**: ERROR and TIMEOUT packets routed to the interrupt controller remain as 64-bit packets without timestamp addition.

### Circular Buffer Operation

The memory-mapped event buffer operates as a circular buffer with configurable base and limit registers, storing 96-bit timestamped entries:

```
Memory Layout:
+-----------------------------------------+ <- Limit Register
|                                         |
|         Available Buffer Space          |
|                                         |
+-----------------------------------------+ <- Current Write Pointer
|    96-bit Event Entry (Packet + TS)     |
+-----------------------------------------+
|    96-bit Event Entry (Packet + TS)     |
+-----------------------------------------+
|    96-bit Event Entry (Packet + TS)     |
|                ...                      |
+-----------------------------------------+ <- Current Read Pointer
|    96-bit Event Entry (Packet + TS)     |
+-----------------------------------------+
|    96-bit Event Entry (Packet + TS)     |
+-----------------------------------------+ <- Base Register
```

### Buffer Configuration Registers

| Register | Description | Access |
|----------|-------------|--------|
| **BASE_ADDR** | Starting address of circular buffer | R/W |
| **LIMIT_ADDR** | Ending address of circular buffer | R/W |
| **WRITE_PTR** | Current write pointer | R/O |
| **READ_PTR** | Current read pointer (software managed) | R/W |
| **BUFFER_STATUS** | Buffer full/empty status flags | R/O |

### Wraparound Behavior

When the write pointer reaches the limit address:
1. **Automatic Wraparound**: Write pointer resets to base address
2. **Overwrite Mode**: New packets overwrite oldest data if buffer is full
3. **Status Updates**: Buffer status flags updated accordingly

## Validation Considerations

### 1. Packet Generation Verification

#### Test Scenarios
- **Protocol Compliance**: Verify correct packet generation for each protocol
- **Event Code Validation**: Ensure proper event codes for each packet type
- **Field Population**: Verify all packet fields are correctly populated
- **Timing Verification**: Confirm packets are generated at appropriate times

#### Checklist
- [ ] Verify packet_type field matches the event category
- [ ] Confirm protocol field corresponds to generating interface
- [ ] Validate event_code is appropriate for packet_type + protocol combination
- [ ] Check channel_id, unit_id, and agent_id for uniqueness and consistency
- [ ] Verify event_data contains relevant information

### 2. Routing Verification

#### Interrupt Path Testing
- **Error Packet Routing**: Verify ERROR packets generate interrupts
- **Timeout Packet Routing**: Verify TIMEOUT packets generate interrupts
- **Interrupt Latency**: Measure and verify interrupt response times
- **Interrupt Priority**: Test interrupt prioritization if applicable

#### Memory Buffer Path Testing
- **Non-Error Routing**: Verify non-ERROR/TIMEOUT packets go to memory with timestamp
- **Timestamp Accuracy**: Verify 32-bit timestamp is correctly appended
- **96-bit Entry Format**: Confirm proper 96-bit entry formatting in memory
- **Buffer Addressing**: Confirm correct base/limit register usage for 96-bit entries
- **Wraparound Logic**: Test buffer wraparound at limit boundary with 96-bit entries
- **Ordering Preservation**: Verify packet ordering and timestamp monotonicity

### 3. Buffer Management Verification

#### Circular Buffer Tests
```systemverilog
// Example test sequence
initial begin
    // Configure buffer for 96-bit entries
    write_reg(BASE_ADDR_REG, 32'h1000_0000);
    write_reg(LIMIT_ADDR_REG, 32'h1000_1800);  // 6KB buffer (512 x 96-bit entries)
    
    // Generate test packets
    for (int i = 0; i < 1000; i++) begin
        generate_test_packet(COMPLETION, AXI, TRANS_COMPLETE);
        check_write_pointer_increment();  // Should increment by 12 bytes (96 bits)
        verify_timestamp_addition();      // Verify 32-bit timestamp appended
    end
    
    // Verify wraparound
    check_write_pointer_wraparound();
    
    // Verify buffer status
    check_buffer_full_flag();
    
    // Verify timestamp ordering
    check_timestamp_monotonicity();
end
```

#### Buffer Overflow Scenarios
- **Full Buffer Handling**: Test behavior when buffer becomes full (96-bit entries)
- **Overwrite Mode**: Verify oldest 96-bit data is overwritten correctly
- **Pointer Management**: Ensure read/write pointers remain synchronized for 96-bit boundaries
- **Timestamp Integrity**: Verify timestamp consistency during buffer wraparound

### 4. Multi-Protocol Integration Testing

#### Cross-Protocol Scenarios
- **Simultaneous Events**: Generate events from multiple protocols simultaneously
- **Priority Handling**: Verify proper handling of concurrent ERROR and non-ERROR events
- **Resource Contention**: Test arbiter behavior under high packet load

#### Performance Testing
- **Throughput Measurement**: Measure maximum packet processing rate
- **Latency Analysis**: Analyze end-to-end latency from event to interrupt/buffer
- **Buffer Utilization**: Monitor buffer usage patterns under various loads

### 5. Error Injection and Recovery

#### Error Injection Techniques
```systemverilog
// Error injection example
task inject_axi_error();
    force axi_monitor.error_inject = 1;
    generate_axi_transaction();
    release axi_monitor.error_inject;
    
    // Verify error packet generation
    wait_for_interrupt();
    check_error_packet_in_interrupt_queue();
endtask
```

#### Recovery Verification
- **Error Clearing**: Verify error conditions can be cleared
- **System Recovery**: Confirm system continues operation after errors
- **Buffer Recovery**: Test buffer operation after overflow conditions

### 6. Debug and Observability

#### Debug Packet Utilization
- **Debug Events**: Verify DEBUG packet types provide useful information
- **State Tracking**: Use debug packets to track transaction states
- **Performance Monitoring**: Leverage PERF packets for performance analysis

#### Observability Features
- **Real-time Monitoring**: Implement real-time packet monitoring
- **Historical Analysis**: Use memory buffer for post-processing analysis
- **Filtering Capabilities**: Implement packet filtering based on criteria

## Common Validation Pitfalls

### 1. Packet Format Issues
- **Bit Field Errors**: Incorrect bit field assignments or overlaps
- **Endianness**: Ensure consistent byte ordering across interfaces
- **Reserved Fields**: Verify reserved fields are properly handled

### 2. Timing Issues
- **Clock Domain Crossing**: Verify proper synchronization across clock domains
- **Metastability**: Test for metastability in asynchronous interfaces
- **Setup/Hold Violations**: Check timing requirements at interface boundaries

### 3. Buffer Management
- **Pointer Arithmetic**: Verify correct pointer calculations and wraparound for 96-bit entries
- **Atomic Operations**: Ensure 96-bit entry writes are atomic
- **Memory Coherency**: Verify memory coherency in multi-master systems
- **Timestamp Clock Domain**: Ensure timestamp clock domain is properly handled

### 4. Protocol-Specific Considerations
- **AXI Compliance**: Ensure full AXI protocol compliance
- **Network Credit Management**: Verify correct credit flow control
- **APB Timing**: Confirm APB setup/access/enable timing requirements

## Validation Test Plan Template

### Phase 1: Basic Functionality
1. **Packet Generation**
   - Single protocol, single event type
   - Verify basic packet format
   - Confirm routing to correct destination

2. **Buffer Operations**
   - Basic 96-bit entry write operations
   - Timestamp addition verification
   - Simple wraparound test with 96-bit entries
   - Buffer status verification

### Phase 2: Protocol Integration
1. **Multi-Protocol Testing**
   - Simultaneous events from different protocols
   - Priority and arbitration verification
   - Cross-protocol interference testing

2. **Error Path Testing**
   - Error packet generation and routing
   - Interrupt generation and handling
   - Error recovery scenarios

### Phase 3: Stress Testing
1. **High Load Scenarios**
   - Maximum packet generation rate
   - Buffer overflow testing with 96-bit entries
   - Timestamp accuracy under high load
   - System stability under stress

2. **Corner Cases**
   - Boundary conditions
   - Unusual packet combinations
   - Recovery from error states

### Phase 4: Performance Validation
1. **Latency Measurements**
   - Event to interrupt latency
   - Event to memory buffer latency
   - End-to-end performance metrics

2. **Throughput Analysis**
   - Maximum sustainable packet rate
   - Bottleneck identification
   - Performance optimization verification

## Conclusion

The monitor bus architecture provides comprehensive observability and error detection across multiple protocol interfaces. Successful validation requires thorough testing of packet generation, routing logic, buffer management, and multi-protocol integration. The structured event code system enables precise error classification and efficient debugging of complex SoC designs.

Key validation success factors:
- **Systematic Approach**: Follow structured test phases
- **Protocol Expertise**: Understand each protocol's specific requirements
- **Stress Testing**: Verify operation under extreme conditions
- **Observability**: Leverage debug packets for comprehensive analysis