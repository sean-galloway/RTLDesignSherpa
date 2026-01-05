<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Monitor Bus Architecture and Event Code Organization

## Overview

The Monitor Bus architecture provides a unified, scalable framework for monitoring and error reporting across multiple bus protocols in complex SoC designs. This system supports AXI, APB, Network (Mesh Network on Chip), ARB (Arbiter), CORE, and custom protocols through a standardized 64-bit packet format with protocol-aware event categorization.

## Interface Summary

### Number of Interfaces

- **1 Monitor Bus Output Interface**: Unified 64-bit packet stream
- **Multiple Protocol Input Interfaces**: AXI, APB, Network, ARB, CORE, Custom protocol monitors
- **Local Memory Interface**: Error/interrupt packet storage
- **External Memory Interface**: Bulk packet storage

### Interface Parameters

| Parameter | Description | Valid Values | Default |
|-----------|-------------|--------------|---------|
| `PACKET_WIDTH` | Monitor bus packet width | 64 | 64 |
| `PROTOCOL_WIDTH` | Protocol identifier width | 3 | 3 |
| `EVENT_CODE_WIDTH` | Event code width | 4 | 4 |
| `PACKET_TYPE_WIDTH` | Packet type width | 4 | 4 |
| `CHANNEL_ID_WIDTH` | Channel identifier width | 6 | 6 |
| `UNIT_ID_WIDTH` | Unit identifier width | 4 | 4 |
| `AGENT_ID_WIDTH` | Agent identifier width | 8 | 8 |
| `EVENT_DATA_WIDTH` | Event data width | 35 | 35 |

## Core Design Assumptions

### Assumption 1: Hierarchical Event Organization

| Aspect | Requirement |
|--------|-------------|
| **Organization Rule** | Protocol -> Packet Type -> Event Code hierarchy |
| **Event Space** | Each protocol x packet type combination has exactly 16 event codes |
| **Mapping** | 1:1 mapping between packet types and event codes |
| **Rationale** | Provides clear, scalable event organization |

### Assumption 2: Protocol Isolation

| Aspect | Requirement |
|--------|-------------|
| **Isolation Rule** | Each protocol owns its event space |
| **Conflict Prevention** | No cross-protocol event conflicts |
| **Independent Evolution** | Protocols can evolve independently |
| **Rationale** | Prevents interference and enables protocol-specific optimization |

### Assumption 3: Two-Tier Memory Architecture

| Aspect | Requirement |
|--------|-------------|
| **Local Storage** | Critical events (errors/interrupts) stored locally |
| **External Storage** | Non-critical events routed to external memory |
| **Routing Decision** | Based on packet type configuration |
| **Rationale** | Balances immediate access with bulk storage needs |

### Assumption 4: Configurable Packet Routing

| Aspect | Requirement |
|--------|-------------|
| **Routing Rule** | Different packet types can route to different destinations |
| **Configuration** | Base/limit registers define routing per packet type |
| **Priority Support** | Configurable priority levels per packet type |
| **Rationale** | Enables flexible memory allocation and access patterns |

## Interface Signal Specification

### Monitor Bus Output Interface

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `mon_packet` | 64 | Monitor->System | Monitor packet data |
| `mon_valid` | 1 | Monitor->System | Packet valid signal |
| `mon_ready` | 1 | System->Monitor | Ready to accept packet |
| `mon_error` | 1 | Monitor->System | Monitor error condition |

### Protocol Input Interfaces

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `axi_event` | 64 | AXI Monitor->Bus | AXI event packet |
| `axi_event_valid` | 1 | AXI Monitor->Bus | AXI event valid |
| `axi_event_ready` | 1 | Bus->AXI Monitor | Ready for AXI event |
| `apb_event` | 64 | APB Monitor->Bus | APB event packet |
| `apb_event_valid` | 1 | APB Monitor->Bus | APB event valid |
| `apb_event_ready` | 1 | Bus->APB Monitor | Ready for APB event |
| `network_event` | 64 | Network Monitor->Bus | Network event packet |
| `network_event_valid` | 1 | Network Monitor->Bus | Network event valid |
| `network_event_ready` | 1 | Bus->Network Monitor | Ready for Network event |
| `arb_event` | 64 | ARB Monitor->Bus | ARB event packet |
| `arb_event_valid` | 1 | ARB Monitor->Bus | ARB event valid |
| `arb_event_ready` | 1 | Bus->ARB Monitor | Ready for ARB event |
| `core_event` | 64 | CORE Monitor->Bus | CORE event packet |
| `core_event_valid` | 1 | CORE Monitor->Bus | CORE event valid |
| `core_event_ready` | 1 | Bus->CORE Monitor | Ready for CORE event |

### Control and Status Signals

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `clk` | 1 | Input | System clock |
| `resetn` | 1 | Input | Active-low reset |
| `monitor_enable` | 1 | Input | Global monitor enable |
| `packet_type_enables` | 16 | Input | Per-type enable bits |
| `local_memory_full` | 1 | Output | Local memory full flag |
| `external_memory_error` | 1 | Output | External memory error |

## Packet Format and Field Allocation

### 64-bit Monitor Bus Packet Structure

| Field | Bits | Width | Description |
|-------|------|-------|-------------|
| **Packet Type** | [63:60] | 4 | Event category (Error, Completion, etc.) |
| **Protocol** | [59:57] | 3 | Bus protocol (AXI=0, Network=1, APB=2, ARB=3, CORE=4) |
| **Event Code** | [56:53] | 4 | Specific events within category |
| **Channel ID** | [52:47] | 6 | Transaction/channel identifier |
| **Unit ID** | [46:43] | 4 | Subsystem identifier |
| **Agent ID** | [42:35] | 8 | Module identifier |
| **Event Data** | [34:0] | 35 | Event-specific payload |

### Packet Type Definitions

| Value | Name | Purpose | Applicable Protocols |
|-------|------|---------|---------------------|
| **0x0** | Error | Protocol violations, response errors | All |
| **0x1** | Completion | Successful transaction completion | All |
| **0x2** | Threshold | Threshold crossed events | All |
| **0x3** | Timeout | Timeout conditions | All |
| **0x4** | Performance | Performance metrics | All |
| **0x5** | Credit | Credit management | Network only |
| **0x6** | Channel | Channel status | Network only |
| **0x7** | Stream | Stream events | Network only |
| **0x8** | Address Match | Address matching | AXI only |
| **0x9** | APB Specific | APB protocol events | APB only |
| **0xA-0xE** | Reserved | Future expansion | - |
| **0xF** | Debug | Debug and trace events | All |

## Protocol-Specific Event Codes

### AXI Protocol Events

#### Error Events (PktTypeError + PROTOCOL_AXI)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | AXI_ERR_RESP_SLVERR | Slave error response |
| **0x1** | AXI_ERR_RESP_DECERR | Decode error response |
| **0x2** | AXI_ERR_DATA_ORPHAN | Data without command |
| **0x3** | AXI_ERR_RESP_ORPHAN | Response without transaction |
| **0x4** | AXI_ERR_PROTOCOL | Protocol violation |
| **0x5** | AXI_ERR_BURST_LENGTH | Invalid burst length |
| **0x6** | AXI_ERR_BURST_SIZE | Invalid burst size |
| **0x7** | AXI_ERR_BURST_TYPE | Invalid burst type |
| **0x8** | AXI_ERR_ID_COLLISION | ID collision detected |
| **0x9** | AXI_ERR_WRITE_BEFORE_ADDR | Write data before address |
| **0xA** | AXI_ERR_RESP_BEFORE_DATA | Response before data complete |
| **0xB** | AXI_ERR_LAST_MISSING | Missing LAST signal |
| **0xC** | AXI_ERR_STROBE_ERROR | Write strobe error |
| **0xD** | AXI_ERR_RESERVED_D | Reserved |
| **0xE** | AXI_ERR_RESERVED_E | Reserved |
| **0xF** | AXI_ERR_USER_DEFINED | User-defined error |

#### Timeout Events (PktTypeTimeout + PROTOCOL_AXI)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | AXI_TIMEOUT_CMD | Command/Address timeout |
| **0x1** | AXI_TIMEOUT_DATA | Data timeout |
| **0x2** | AXI_TIMEOUT_RESP | Response timeout |
| **0x3** | AXI_TIMEOUT_HANDSHAKE | Handshake timeout |
| **0x4** | AXI_TIMEOUT_BURST | Burst completion timeout |
| **0x5** | AXI_TIMEOUT_EXCLUSIVE | Exclusive access timeout |
| **0x6-0xE** | Reserved | Future expansion |
| **0xF** | AXI_TIMEOUT_USER_DEFINED | User-defined timeout |

#### Performance Events (PktTypePerf + PROTOCOL_AXI)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | AXI_PERF_ADDR_LATENCY | Address phase latency |
| **0x1** | AXI_PERF_DATA_LATENCY | Data phase latency |
| **0x2** | AXI_PERF_RESP_LATENCY | Response phase latency |
| **0x3** | AXI_PERF_TOTAL_LATENCY | Total transaction latency |
| **0x4** | AXI_PERF_THROUGHPUT | Transaction throughput |
| **0x5** | AXI_PERF_ERROR_RATE | Error rate |
| **0x6** | AXI_PERF_ACTIVE_COUNT | Active transaction count |
| **0x7** | AXI_PERF_BANDWIDTH_UTIL | Bandwidth utilization |
| **0x8** | AXI_PERF_QUEUE_DEPTH | Average queue depth |
| **0x9** | AXI_PERF_BURST_EFFICIENCY | Burst efficiency metric |
| **0xA-0xE** | Reserved | Future expansion |
| **0xF** | AXI_PERF_USER_DEFINED | User-defined performance |

### APB Protocol Events

#### Error Events (PktTypeError + PROTOCOL_APB)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | APB_ERR_PSLVERR | Peripheral slave error |
| **0x1** | APB_ERR_SETUP_VIOLATION | Setup phase protocol violation |
| **0x2** | APB_ERR_ACCESS_VIOLATION | Access phase protocol violation |
| **0x3** | APB_ERR_STROBE_ERROR | Write strobe error |
| **0x4** | APB_ERR_ADDR_DECODE | Address decode error |
| **0x5** | APB_ERR_PROT_VIOLATION | Protection violation (PPROT) |
| **0x6** | APB_ERR_ENABLE_ERROR | Enable phase error |
| **0x7** | APB_ERR_READY_ERROR | PREADY protocol error |
| **0x8-0xE** | Reserved | Future expansion |
| **0xF** | APB_ERR_USER_DEFINED | User-defined error |

#### Timeout Events (PktTypeTimeout + PROTOCOL_APB)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | APB_TIMEOUT_SETUP | Setup phase timeout |
| **0x1** | APB_TIMEOUT_ACCESS | Access phase timeout |
| **0x2** | APB_TIMEOUT_ENABLE | Enable phase timeout (PREADY stuck) |
| **0x3** | APB_TIMEOUT_PREADY_STUCK | PREADY stuck low |
| **0x4** | APB_TIMEOUT_TRANSFER | Overall transfer timeout |
| **0x5-0xE** | Reserved | Future expansion |
| **0xF** | APB_TIMEOUT_USER_DEFINED | User-defined timeout |

#### Completion Events (PktTypeCompletion + PROTOCOL_APB)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | APB_COMPL_TRANS_COMPLETE | Transaction completed |
| **0x1** | APB_COMPL_READ_COMPLETE | Read transaction complete |
| **0x2** | APB_COMPL_WRITE_COMPLETE | Write transaction complete |
| **0x3-0xE** | Reserved | Future expansion |
| **0xF** | APB_COMPL_USER_DEFINED | User-defined completion |

#### Threshold Events (PktTypeThreshold + PROTOCOL_APB)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | APB_THRESH_LATENCY | APB latency threshold |
| **0x1** | APB_THRESH_ERROR_RATE | APB error rate threshold |
| **0x2** | APB_THRESH_ACCESS_COUNT | Access count threshold |
| **0x3** | APB_THRESH_BANDWIDTH | Bandwidth threshold |
| **0x4-0xE** | Reserved | Future expansion |
| **0xF** | APB_THRESH_USER_DEFINED | User-defined threshold |

#### Performance Events (PktTypePerf + PROTOCOL_APB)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | APB_PERF_READ_LATENCY | Read transaction latency |
| **0x1** | APB_PERF_WRITE_LATENCY | Write transaction latency |
| **0x2** | APB_PERF_THROUGHPUT | Transaction throughput |
| **0x3** | APB_PERF_ERROR_RATE | Error rate |
| **0x4** | APB_PERF_ACTIVE_COUNT | Active transaction count |
| **0x5** | APB_PERF_COMPLETED_COUNT | Completed transaction count |
| **0x6-0xE** | Reserved | Future expansion |
| **0xF** | APB_PERF_USER_DEFINED | User-defined performance |

#### Debug Events (PktTypeDebug + PROTOCOL_APB)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | APB_DEBUG_STATE_CHANGE | APB state changed |
| **0x1** | APB_DEBUG_SETUP_PHASE | Setup phase event |
| **0x2** | APB_DEBUG_ACCESS_PHASE | Access phase event |
| **0x3** | APB_DEBUG_ENABLE_PHASE | Enable phase event |
| **0x4** | APB_DEBUG_PSEL_TRACE | PSEL trace |
| **0x5** | APB_DEBUG_PENABLE_TRACE | PENABLE trace |
| **0x6** | APB_DEBUG_PREADY_TRACE | PREADY trace |
| **0x7** | APB_DEBUG_PPROT_TRACE | PPROT trace |
| **0x8** | APB_DEBUG_PSTRB_TRACE | PSTRB trace |
| **0x9-0xE** | Reserved | Future expansion |
| **0xF** | APB_DEBUG_USER_DEFINED | User-defined debug |

### Network Protocol Events

#### Error Events (PktTypeError + PROTOCOL_MNOC)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | NETWORK_ERR_PARITY | Parity error |
| **0x1** | NETWORK_ERR_PROTOCOL | Protocol violation |
| **0x2** | NETWORK_ERR_OVERFLOW | Buffer/Credit overflow |
| **0x3** | NETWORK_ERR_UNDERFLOW | Buffer/Credit underflow |
| **0x4** | NETWORK_ERR_ORPHAN | Orphaned packet/ACK |
| **0x5** | NETWORK_ERR_INVALID | Invalid type/channel/payload |
| **0x6** | NETWORK_ERR_HEADER_CRC | Header CRC error |
| **0x7** | NETWORK_ERR_PAYLOAD_CRC | Payload CRC error |
| **0x8** | NETWORK_ERR_SEQUENCE | Sequence number error |
| **0x9** | NETWORK_ERR_ROUTE | Routing error |
| **0xA** | NETWORK_ERR_DEADLOCK | Deadlock detected |
| **0xB-0xE** | Reserved | Future expansion |
| **0xF** | NETWORK_ERR_USER_DEFINED | User-defined error |

#### Credit Events (PktTypeCredit + PROTOCOL_MNOC)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | NETWORK_CREDIT_ALLOCATED | Credits allocated |
| **0x1** | NETWORK_CREDIT_CONSUMED | Credits consumed |
| **0x2** | NETWORK_CREDIT_RETURNED | Credits returned |
| **0x3** | NETWORK_CREDIT_OVERFLOW | Credit overflow detected |
| **0x4** | NETWORK_CREDIT_UNDERFLOW | Credit underflow detected |
| **0x5** | NETWORK_CREDIT_EXHAUSTED | All credits exhausted |
| **0x6** | NETWORK_CREDIT_RESTORED | Credits restored |
| **0x7** | NETWORK_CREDIT_EFFICIENCY | Credit efficiency metric |
| **0x8** | NETWORK_CREDIT_LEAK | Credit leak detected |
| **0x9-0xE** | Reserved | Future expansion |
| **0xF** | NETWORK_CREDIT_USER_DEFINED | User-defined credit event |

#### Channel Events (PktTypeChannel + PROTOCOL_MNOC)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | NETWORK_CHANNEL_OPEN | Channel opened |
| **0x1** | NETWORK_CHANNEL_CLOSE | Channel closed |
| **0x2** | NETWORK_CHANNEL_STALL | Channel stalled |
| **0x3** | NETWORK_CHANNEL_RESUME | Channel resumed |
| **0x4** | NETWORK_CHANNEL_CONGESTION | Channel congestion detected |
| **0x5** | NETWORK_CHANNEL_PRIORITY | Channel priority change |
| **0x6-0xE** | Reserved | Future expansion |
| **0xF** | NETWORK_CHANNEL_USER_DEFINED | User-defined channel event |

#### Stream Events (PktTypeStream + PROTOCOL_MNOC)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | NETWORK_STREAM_START | Stream started |
| **0x1** | NETWORK_STREAM_END | Stream ended (EOS) |
| **0x2** | NETWORK_STREAM_PAUSE | Stream paused |
| **0x3** | NETWORK_STREAM_RESUME | Stream resumed |
| **0x4** | NETWORK_STREAM_OVERFLOW | Stream buffer overflow |
| **0x5** | NETWORK_STREAM_UNDERFLOW | Stream buffer underflow |
| **0x6-0xE** | Reserved | Future expansion |
| **0xF** | NETWORK_STREAM_USER_DEFINED | User-defined stream event |

### ARB Protocol Events

#### Error Events (PktTypeError + PROTOCOL_ARB)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | ARB_ERR_STARVATION | Client request starvation |
| **0x1** | ARB_ERR_ACK_TIMEOUT | Grant ACK timeout |
| **0x2** | ARB_ERR_PROTOCOL_VIOLATION | ACK protocol violation |
| **0x3** | ARB_ERR_CREDIT_VIOLATION | Credit system violation |
| **0x4** | ARB_ERR_FAIRNESS_VIOLATION | Weighted fairness violation |
| **0x5** | ARB_ERR_WEIGHT_UNDERFLOW | Weight credit underflow |
| **0x6** | ARB_ERR_CONCURRENT_GRANTS | Multiple simultaneous grants |
| **0x7** | ARB_ERR_INVALID_GRANT_ID | Invalid grant ID detected |
| **0x8** | ARB_ERR_ORPHAN_ACK | ACK without pending grant |
| **0x9** | ARB_ERR_GRANT_OVERLAP | Overlapping grant periods |
| **0xA** | ARB_ERR_MASK_ERROR | Round-robin mask error |
| **0xB** | ARB_ERR_STATE_MACHINE | FSM state error |
| **0xC** | ARB_ERR_CONFIGURATION | Invalid configuration |
| **0xD-0xE** | Reserved | Future expansion |
| **0xF** | ARB_ERR_USER_DEFINED | User-defined error |

#### Timeout Events (PktTypeTimeout + PROTOCOL_ARB)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | ARB_TIMEOUT_GRANT_ACK | Grant ACK timeout |
| **0x1** | ARB_TIMEOUT_REQUEST_HOLD | Request held too long |
| **0x2** | ARB_TIMEOUT_WEIGHT_UPDATE | Weight update timeout |
| **0x3** | ARB_TIMEOUT_BLOCK_RELEASE | Block release timeout |
| **0x4** | ARB_TIMEOUT_CREDIT_UPDATE | Credit update timeout |
| **0x5** | ARB_TIMEOUT_STATE_CHANGE | State machine timeout |
| **0x6-0xE** | Reserved | Future expansion |
| **0xF** | ARB_TIMEOUT_USER_DEFINED | User-defined timeout |

#### Completion Events (PktTypeCompletion + PROTOCOL_ARB)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | ARB_COMPL_GRANT_ISSUED | Grant successfully issued |
| **0x1** | ARB_COMPL_ACK_RECEIVED | ACK successfully received |
| **0x2** | ARB_COMPL_TRANSACTION | Complete transaction (grant+ack) |
| **0x3** | ARB_COMPL_WEIGHT_UPDATE | Weight update completed |
| **0x4** | ARB_COMPL_CREDIT_CYCLE | Credit cycle completed |
| **0x5** | ARB_COMPL_FAIRNESS_PERIOD | Fairness analysis period |
| **0x6** | ARB_COMPL_BLOCK_PERIOD | Block period completed |
| **0x7-0xE** | Reserved | Future expansion |
| **0xF** | ARB_COMPL_USER_DEFINED | User-defined completion |

#### Threshold Events (PktTypeThreshold + PROTOCOL_ARB)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | ARB_THRESH_REQUEST_LATENCY | Request-to-grant latency threshold |
| **0x1** | ARB_THRESH_ACK_LATENCY | Grant-to-ACK latency threshold |
| **0x2** | ARB_THRESH_FAIRNESS_DEV | Fairness deviation threshold |
| **0x3** | ARB_THRESH_ACTIVE_REQUESTS | Active request count threshold |
| **0x4** | ARB_THRESH_GRANT_RATE | Grant rate threshold |
| **0x5** | ARB_THRESH_EFFICIENCY | Grant efficiency threshold |
| **0x6** | ARB_THRESH_CREDIT_LOW | Low credit threshold |
| **0x7** | ARB_THRESH_WEIGHT_IMBALANCE | Weight imbalance threshold |
| **0x8** | ARB_THRESH_STARVATION_TIME | Starvation time threshold |
| **0x9-0xE** | Reserved | Future expansion |
| **0xF** | ARB_THRESH_USER_DEFINED | User-defined threshold |

#### Performance Events (PktTypePerf + PROTOCOL_ARB)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | ARB_PERF_GRANT_ISSUED | Grant issued event |
| **0x1** | ARB_PERF_ACK_RECEIVED | ACK received event |
| **0x2** | ARB_PERF_GRANT_EFFICIENCY | Grant completion efficiency |
| **0x3** | ARB_PERF_FAIRNESS_METRIC | Fairness compliance metric |
| **0x4** | ARB_PERF_THROUGHPUT | Arbitration throughput |
| **0x5** | ARB_PERF_LATENCY_AVG | Average latency measurement |
| **0x6** | ARB_PERF_WEIGHT_COMPLIANCE | Weight compliance metric |
| **0x7** | ARB_PERF_CREDIT_UTILIZATION | Credit utilization efficiency |
| **0x8** | ARB_PERF_CLIENT_ACTIVITY | Per-client activity metric |
| **0x9** | ARB_PERF_STARVATION_COUNT | Starvation event count |
| **0xA** | ARB_PERF_BLOCK_EFFICIENCY | Block/unblock efficiency |
| **0xB-0xE** | Reserved | Future expansion |
| **0xF** | ARB_PERF_USER_DEFINED | User-defined performance |

#### Debug Events (PktTypeDebug + PROTOCOL_ARB)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | ARB_DEBUG_STATE_CHANGE | Arbiter state machine change |
| **0x1** | ARB_DEBUG_MASK_UPDATE | Round-robin mask update |
| **0x2** | ARB_DEBUG_WEIGHT_CHANGE | Weight configuration change |
| **0x3** | ARB_DEBUG_CREDIT_UPDATE | Credit level update |
| **0x4** | ARB_DEBUG_CLIENT_MASK | Client enable/disable mask |
| **0x5** | ARB_DEBUG_PRIORITY_CHANGE | Priority level change |
| **0x6** | ARB_DEBUG_BLOCK_EVENT | Block/unblock event |
| **0x7** | ARB_DEBUG_QUEUE_STATUS | Request queue status |
| **0x8** | ARB_DEBUG_COUNTER_SNAPSHOT | Counter values snapshot |
| **0x9** | ARB_DEBUG_FIFO_STATUS | FIFO status change |
| **0xA** | ARB_DEBUG_FAIRNESS_STATE | Fairness tracking state |
| **0xB** | ARB_DEBUG_ACK_STATE | ACK protocol state |
| **0xC-0xE** | Reserved | Future expansion |
| **0xF** | ARB_DEBUG_USER_DEFINED | User-defined debug |

### CORE Protocol Events

#### Error Events (PktTypeError + PROTOCOL_CORE)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | CORE_ERR_DESCRIPTOR_MALFORMED | Missing magic number (0x900dc0de) |
| **0x1** | CORE_ERR_DESCRIPTOR_BAD_ADDR | Invalid descriptor address |
| **0x2** | CORE_ERR_DATA_BAD_ADDR | Invalid data address (fetch or runtime) |
| **0x3** | CORE_ERR_FLAG_COMPARISON | Flag mask/compare mismatch |
| **0x4** | CORE_ERR_CREDIT_UNDERFLOW | Credit system violation |
| **0x5** | CORE_ERR_STATE_MACHINE | Invalid FSM state transition |
| **0x6** | CORE_ERR_DESCRIPTOR_ENGINE | Descriptor engine FSM error |
| **0x7** | CORE_ERR_FLAG_ENGINE | Flag engine FSM error |
| **0x8** | CORE_ERR_PROGRAM_ENGINE | Program engine FSM error |
| **0x9** | CORE_ERR_DATA_ENGINE | Data engine error |
| **0xA** | CORE_ERR_CHANNEL_INVALID | Invalid channel ID |
| **0xB** | CORE_ERR_CONTROL_VIOLATION | Control register violation |
| **0xC-0xE** | Reserved | Future expansion |
| **0xF** | CORE_ERR_USER_DEFINED | User-defined error |

#### Timeout Events (PktTypeTimeout + PROTOCOL_CORE)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | CORE_TIMEOUT_DESCRIPTOR_FETCH | Descriptor fetch timeout |
| **0x1** | CORE_TIMEOUT_FLAG_RETRY | Flag comparison retry timeout |
| **0x2** | CORE_TIMEOUT_PROGRAM_WRITE | Program write timeout |
| **0x3** | CORE_TIMEOUT_DATA_TRANSFER | Data transfer timeout |
| **0x4** | CORE_TIMEOUT_CREDIT_WAIT | Credit wait timeout |
| **0x5** | CORE_TIMEOUT_CONTROL_WAIT | Control enable wait timeout |
| **0x6** | CORE_TIMEOUT_ENGINE_RESPONSE | Sub-engine response timeout |
| **0x7** | CORE_TIMEOUT_STATE_TRANSITION | FSM state transition timeout |
| **0x8-0xE** | Reserved | Future expansion |
| **0xF** | CORE_TIMEOUT_USER_DEFINED | User-defined timeout |

#### Completion Events (PktTypeCompletion + PROTOCOL_CORE)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | CORE_COMPL_DESCRIPTOR_LOADED | Descriptor successfully loaded |
| **0x1** | CORE_COMPL_DESCRIPTOR_CHAIN | Descriptor chain completed |
| **0x2** | CORE_COMPL_FLAG_MATCHED | Flag comparison successful |
| **0x3** | CORE_COMPL_PROGRAM_COMPLETED | Post-programming completed |
| **0x4** | CORE_COMPL_DATA_TRANSFER | Data transfer completed |
| **0x5** | CORE_COMPL_CREDIT_CYCLE | Credit cycle completed |
| **0x6** | CORE_COMPL_CHANNEL_COMPLETE | Channel processing complete |
| **0x7** | CORE_COMPL_ENGINE_READY | Sub-engine ready |
| **0x8-0xE** | Reserved | Future expansion |
| **0xF** | CORE_COMPL_USER_DEFINED | User-defined completion |

#### Threshold Events (PktTypeThreshold + PROTOCOL_CORE)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | CORE_THRESH_DESCRIPTOR_QUEUE | Descriptor queue depth threshold |
| **0x1** | CORE_THRESH_CREDIT_LOW | Credit low threshold |
| **0x2** | CORE_THRESH_FLAG_RETRY_COUNT | Flag retry count threshold |
| **0x3** | CORE_THRESH_LATENCY | Processing latency threshold |
| **0x4** | CORE_THRESH_ERROR_RATE | Error rate threshold |
| **0x5** | CORE_THRESH_THROUGHPUT | Throughput threshold |
| **0x6** | CORE_THRESH_ACTIVE_CHANNELS | Active channel count threshold |
| **0x7** | CORE_THRESH_PROGRAM_LATENCY | Program write latency threshold |
| **0x8** | CORE_THRESH_DATA_RATE | Data transfer rate threshold |
| **0x9-0xE** | Reserved | Future expansion |
| **0xF** | CORE_THRESH_USER_DEFINED | User-defined threshold |

#### Performance Events (PktTypePerf + PROTOCOL_CORE)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | CORE_PERF_END_OF_DATA | Stream continuation signal |
| **0x1** | CORE_PERF_END_OF_STREAM | Stream termination signal |
| **0x2** | CORE_PERF_ENTERING_IDLE | FSM returning to idle |
| **0x3** | CORE_PERF_CREDIT_INCREMENTED | Credit added by software |
| **0x4** | CORE_PERF_CREDIT_EXHAUSTED | Credit blocking execution |
| **0x5** | CORE_PERF_STATE_TRANSITION | FSM state change |
| **0x6** | CORE_PERF_DESCRIPTOR_ACTIVE | Data processing started |
| **0x7** | CORE_PERF_FLAG_RETRY | Flag comparison retry |
| **0x8** | CORE_PERF_CHANNEL_ENABLE | Channel enabled by software |
| **0x9** | CORE_PERF_CHANNEL_DISABLE | Channel disabled by software |
| **0xA** | CORE_PERF_CREDIT_UTILIZATION | Credit utilization metric |
| **0xB** | CORE_PERF_PROCESSING_LATENCY | Total processing latency |
| **0xC** | CORE_PERF_QUEUE_DEPTH | Current queue depth |
| **0xD-0xE** | Reserved | Future expansion |
| **0xF** | CORE_PERF_USER_DEFINED | User-defined performance |

#### Debug Events (PktTypeDebug + PROTOCOL_CORE)

| Code | Event Name | Description |
|------|------------|-------------|
| **0x0** | CORE_DEBUG_FSM_STATE_CHANGE | Descriptor FSM state change |
| **0x1** | CORE_DEBUG_DESCRIPTOR_CONTENT | Descriptor content trace |
| **0x2** | CORE_DEBUG_FLAG_ENGINE_STATE | Flag engine state trace |
| **0x3** | CORE_DEBUG_PROGRAM_ENGINE_STATE | Program engine state trace |
| **0x4** | CORE_DEBUG_CREDIT_OPERATION | Credit system operation |
| **0x5** | CORE_DEBUG_CONTROL_REGISTER | Control register access |
| **0x6** | CORE_DEBUG_ENGINE_HANDSHAKE | Engine handshake trace |
| **0x7** | CORE_DEBUG_QUEUE_STATUS | Queue status change |
| **0x8** | CORE_DEBUG_COUNTER_SNAPSHOT | Counter values snapshot |
| **0x9** | CORE_DEBUG_ADDRESS_TRACE | Address progression trace |
| **0xA** | CORE_DEBUG_PAYLOAD_TRACE | Payload content trace |
| **0xB-0xE** | Reserved | Future expansion |
| **0xF** | CORE_DEBUG_USER_DEFINED | User-defined debug |

## Memory Architecture and Packet Routing

### Two-Tier Memory Architecture

#### Local Error/Interrupt Memory

| Characteristic | Description |
|----------------|-------------|
| **Storage Types** | Error Packets (Type 0x0) and Timeout Packets (Type 0x3) |
| **Access Method** | Immediate CPU access without memory subsystem delays |
| **Capacity** | Large enough to prevent overflow during error bursts |
| **Priority** | Critical events requiring immediate attention |
| **Indexing** | Fast search and retrieval mechanisms |

#### Configurable External Memory

| Characteristic | Description |
|----------------|-------------|
| **Storage Types** | Performance, Completion, Threshold, Debug packets |
| **Access Method** | Base and limit registers define memory regions |
| **Capacity** | Bulk storage for non-critical events |
| **DMA Support** | Can be accessed via DMA for efficient transfer |
| **Time Stamping** | 32-bit timestamp appended when routing externally |

### Routing Configuration

#### Base and Limit Registers

| Register Set | Purpose | Configuration |
|-------------|---------|---------------|
| **Completion Config** | Type 0x1 routing | base_addr, limit_addr, enable, priority |
| **Threshold Config** | Type 0x2 routing | base_addr, limit_addr, enable, priority |
| **Performance Config** | Type 0x4 routing | base_addr, limit_addr, enable, priority |
| **Debug Config** | Type 0xF routing | base_addr, limit_addr, enable, priority |

#### Routing Decision Logic

| Packet Type | Destination | Address Calculation |
|-------------|-------------|-------------------|
| **Error (0x0)** | Local Memory | local_error_write_pointer |
| **Timeout (0x3)** | Local Memory | local_error_write_pointer |
| **Completion (0x1)** | External Memory | completion_config.base_addr + offset |
| **Performance (0x4)** | External Memory | performance_config.base_addr + offset |
| **Debug (0xF)** | External Memory | debug_config.base_addr + offset |

### Address Space Management

#### Memory Layout Example

| Address Range | Usage | Description |
|---------------|-------|-------------|
| **0x1000_0000 - 0x1000_FFFF** | Local Error Memory | Immediate access storage |
| **0x2000_0000 - 0x2001_FFFF** | Performance Packets | External bulk storage |
| **0x2010_0000 - 0x2011_FFFF** | Completion Packets | External bulk storage |
| **0x2020_0000 - 0x202F_FFFF** | Debug Packets | External bulk storage |

### Transaction State and Bus Transaction Structure

#### Transaction State Enumeration

| State | Value | Description | Usage |
|-------|-------|-------------|-------|
| **TRANS_EMPTY** | 3'b000 | Unused entry | Available slot |
| **TRANS_ADDR_PHASE** | 3'b001 | Address phase active (AXI) / Packet sent (Network) / Setup phase (APB) | Initial phase |
| **TRANS_DATA_PHASE** | 3'b010 | Data phase active (AXI) / Waiting for ACK (Network) / Access phase (APB) | Data transfer |
| **TRANS_RESP_PHASE** | 3'b011 | Response phase active (AXI) / ACK received (Network) / Enable phase (APB) | Response handling |
| **TRANS_COMPLETE** | 3'b100 | Transaction complete | Successful completion |
| **TRANS_ERROR** | 3'b101 | Transaction has error | Error condition |
| **TRANS_ORPHANED** | 3'b110 | Orphaned transaction | Missing components |
| **TRANS_CREDIT_STALL** | 3'b111 | Credit stall (Network only) | Network-specific stall |

#### Enhanced Transaction Structure

| Field | Width | Description | Protocol Usage |
|-------|-------|-------------|----------------|
| **valid** | 1 | Entry is valid | All protocol's |
| **protocol** | 3 | Protocol type (AXI/Network/APB/ARB/CORE) | All protocols |
| **state** | 3 | Transaction state | All protocols |
| **id** | 32 | Transaction ID (AXI) / Sequence (Network) / PSEL encoding (APB) | All protocols |
| **addr** | 64 | Transaction address / Channel addr / PADDR | All protocols |
| **len** | 8 | Burst length (AXI) / Packet count (Network) / Always 0 (APB) | AXI, Network |
| **size** | 3 | Access size (AXI) / Reserved (Network) / Transfer size (APB) | AXI, APB |
| **burst** | 2 | Burst type (AXI) / Payload type (Network) / PPROT[1:0] (APB) | All protocols |

#### Phase Completion Flags

| Flag | Description | Protocol Usage |
|------|-------------|----------------|
| **cmd_received** | Address phase received / Packet sent / Setup phase | All protocols |
| **data_started** | Data phase started / ACK expected / Access phase | All protocols |
| **data_completed** | Data phase completed / ACK received / Enable phase | All protocols |
| **resp_received** | Response received / Final ACK / PREADY asserted | All protocols |

#### Protocol-Specific Tracking Fields

| Field | Width | Description | Protocol |
|-------|-------|-------------|----------|
| **channel** | 6 | Channel ID (AXI ID / Network channel / PSEL bit position) | All protocols |
| **eos_seen** | 1 | EOS marker seen | Network only |
| **parity_error** | 1 | Parity error detected | Network only |
| **credit_at_start** | 8 | Credits available at start | Network only |
| **retry_count** | 3 | Number of retries | Network only |
| **desc_addr_match** | 1 | Descriptor address match detected | AXI only |
| **data_addr_match** | 1 | Data address match detected | AXI only |
| **apb_phase** | 2 | Current APB phase | APB only |
| **pslverr_seen** | 1 | PSLVERR detected | APB only |
| **pprot_value** | 3 | PPROT value | APB only |
| **pstrb_value** | 4 | PSTRB value for writes | APB only |
| **arb_grant_id** | 8 | Current grant ID | ARB only |
| **arb_weight** | 8 | Current weight value | ARB only |
| **core_fsm_state** | 3 | Current CORE FSM state | CORE only |
| **core_channel_id** | 6 | CORE channel identifier | CORE only |

### APB Transaction Phases

| Phase | Value | Description |
|-------|-------|-------------|
| **APB_PHASE_IDLE** | 2'b00 | Bus idle |
| **APB_PHASE_SETUP** | 2'b01 | Setup phase (PSEL asserted) |
| **APB_PHASE_ACCESS** | 2'b10 | Access phase (PENABLE asserted) |
| **APB_PHASE_ENABLE** | 2'b11 | Enable phase (waiting for PREADY) |

### APB Protection Types

| Protection | Value | Description |
|------------|-------|-------------|
| **APB_PROT_NORMAL** | 3'b000 | Normal access |
| **APB_PROT_PRIVILEGED** | 3'b001 | Privileged access |
| **APB_PROT_SECURE** | 3'b010 | Secure access |
| **APB_PROT_INSTRUCTION** | 3'b100 | Instruction access |

### Network Payload Types

| Payload | Value | Description |
|---------|-------|-------------|
| **NETWORK_PAYLOAD_CONFIG** | 2'b00 | CONFIG_PKT |
| **NETWORK_PAYLOAD_TS** | 2'b01 | TS_PKT |
| **NETWORK_PAYLOAD_RDA** | 2'b10 | RDA_PKT |
| **NETWORK_PAYLOAD_RAW** | 2'b11 | RAW_PKT |

### Network ACK Types

| ACK Type | Value | Description |
|----------|-------|-------------|
| **NETWORK_ACK_STOP** | 2'b00 | MSAP_STOP |
| **NETWORK_ACK_START** | 2'b01 | MSAP_START |
| **NETWORK_ACK_CREDIT_ON** | 2'b10 | MSAP_CREDIT_ON |
| **NETWORK_ACK_STOP_AT_EOS** | 2'b11 | MSAP_STOP_AT_EOS |

### ARB State Types

| State | Value | Description |
|-------|-------|-------------|
| **ARB_STATE_IDLE** | 3'b000 | Idle state |
| **ARB_STATE_ARBITRATE** | 3'b001 | Performing arbitration |
| **ARB_STATE_GRANT** | 3'b010 | Grant issued, waiting for ACK |
| **ARB_STATE_BLOCKED** | 3'b011 | Arbitration blocked |
| **ARB_STATE_WEIGHT_UPD** | 3'b100 | Weight update in progress |
| **ARB_STATE_ERROR** | 3'b101 | Error state |

### CORE State Types

| State | Value | Description |
|-------|-------|-------------|
| **CORE_STATE_IDLE** | 3'b000 | Idle state |
| **CORE_STATE_DESC_FETCH** | 3'b001 | Fetching descriptor |
| **CORE_STATE_FLAG_CHECK** | 3'b010 | Checking flag condition |
| **CORE_STATE_PROGRAM_WRITE** | 3'b011 | Writing program |
| **CORE_STATE_DATA_TRANSFER** | 3'b100 | Transferring data |
| **CORE_STATE_CREDIT_WAIT** | 3'b101 | Waiting for credits |
| **CORE_STATE_ERROR** | 3'b110 | Error state |

## Configuration and Control

### Monitor Configuration Registers

#### Global Configuration

| Field | Width | Description |
|-------|-------|-------------|
| **monitor_enable** | 1 | Global monitor enable |
| **error_local_enable** | 1 | Enable local error storage |
| **external_route_enable** | 1 | Enable external routing |
| **unit_id** | 4 | Unit identifier |
| **agent_id** | 8 | Agent identifier |
| **packet_type_enables** | 16 | Per-type enable bits |

#### Packet Type Enable Mapping

| Bit | Enable | Description |
|-----|--------|-------------|
| **0** | PKT_ENABLE_ERROR | Enable error packets |
| **1** | PKT_ENABLE_COMPLETION | Enable completion packets |
| **2** | PKT_ENABLE_THRESHOLD | Enable threshold packets |
| **3** | PKT_ENABLE_TIMEOUT | Enable timeout packets |
| **4** | PKT_ENABLE_PERF | Enable performance packets |
| **5** | PKT_ENABLE_CREDIT | Enable credit packets (Network) |
| **6** | PKT_ENABLE_CHANNEL | Enable channel packets (Network) |
| **7** | PKT_ENABLE_STREAM | Enable stream packets (Network) |
| **8** | PKT_ENABLE_ADDR_MATCH | Enable address match (AXI) |
| **9** | PKT_ENABLE_APB | Enable APB packets |
| **15** | PKT_ENABLE_DEBUG | Enable debug packets |

### Protocol-Specific Configuration

#### AXI Monitor Configuration

| Field | Width | Description |
|-------|-------|-------------|
| **active_trans_threshold** | 16 | Active transaction threshold |
| **latency_threshold** | 32 | Latency threshold (cycles) |
| **addr_timeout_cnt** | 4 | Address timeout count |
| **data_timeout_cnt** | 4 | Data timeout count |
| **resp_timeout_cnt** | 4 | Response timeout count |
| **burst_boundary_check** | 1 | Enable burst boundary checking |
| **address_match_enable** | 1 | Enable address matching |
| **desc_addr_match_base** | 64 | Descriptor address match base |
| **desc_addr_match_mask** | 64 | Descriptor address match mask |
| **data_addr_match_base** | 64 | Data address match base |
| **data_addr_match_mask** | 64 | Data address match mask |

#### Network Monitor Configuration

| Field | Width | Description |
|-------|-------|-------------|
| **credit_low_threshold** | 8 | Credit low threshold |
| **packet_rate_threshold** | 16 | Packet rate threshold |
| **max_route_hops** | 8 | Maximum routing hops |
| **enable_credit_tracking** | 1 | Enable credit tracking |
| **enable_deadlock_detect** | 1 | Enable deadlock detection |
| **deadlock_timeout** | 4 | Deadlock detection timeout |

#### ARB Monitor Configuration

| Field | Width | Description |
|-------|-------|-------------|
| **grant_timeout_cnt** | 16 | Grant ACK timeout count |
| **fairness_window** | 32 | Fairness analysis window |
| **weight_update_enable** | 1 | Enable weight tracking |
| **starvation_threshold** | 16 | Starvation detection threshold |
| **efficiency_threshold** | 8 | Grant efficiency threshold |

#### CORE Monitor Configuration

| Field | Width | Description |
|-------|-------|-------------|
| **descriptor_timeout_cnt** | 16 | Descriptor fetch timeout count |
| **flag_retry_limit** | 8 | Maximum flag retry count |
| **credit_low_threshold** | 8 | Credit low threshold |
| **processing_timeout_cnt** | 32 | Processing timeout count |
| **enable_descriptor_trace** | 1 | Enable descriptor content tracing |
| **enable_fsm_trace** | 1 | Enable FSM state tracing |

## Validation Requirements

### Functional Validation

| Validation Area | Requirements |
|----------------|-------------|
| **Packet Format** | Verify 64-bit packet structure and field encoding |
| **Event Organization** | Verify hierarchical event code organization |
| **Protocol Isolation** | Verify independent protocol event spaces |
| **Routing Logic** | Verify packet routing based on type and configuration |
| **Memory Management** | Verify local and external memory operations |
| **Configuration** | Verify register configuration and enable controls |

### Performance Validation

| Validation Area | Requirements |
|----------------|-------------|
| **Throughput** | Verify monitor bus can handle peak event rates |
| **Latency** | Verify low-latency path for critical events |
| **Memory Efficiency** | Verify efficient memory usage patterns |
| **Power Consumption** | Verify power-efficient operation |

### Error Handling Validation

| Validation Area | Requirements |
|----------------|-------------|
| **Error Injection** | Verify error detection and reporting |
| **Overflow Handling** | Verify behavior when memories fill |
| **Configuration Errors** | Verify invalid configuration detection |
| **Recovery Mechanisms** | Verify error recovery procedures |

## Usage Examples

### Creating Monitor Packets

| Packet Type | Example Usage |
|-------------|---------------|
| **AXI Error** | Protocol=AXI, Type=Error, Code=AXI_ERR_RESP_SLVERR |
| **Network Credit** | Protocol=Network, Type=Credit, Code=NETWORK_CREDIT_EXHAUSTED |
| **APB Performance** | Protocol=APB, Type=Performance, Code=APB_PERF_TOTAL_LATENCY |
| **ARB Threshold** | Protocol=ARB, Type=Threshold, Code=ARB_THRESH_FAIRNESS_DEV |
| **CORE Completion** | Protocol=CORE, Type=Completion, Code=CORE_COMPL_DESCRIPTOR_LOADED |

### Packet Decoding

| Decoding Step | Method |
|---------------|---------|
| **Extract Type** | packet[63:60] |
| **Extract Protocol** | packet[59:57] |
| **Extract Event Code** | packet[56:53] |
| **Extract Channel ID** | packet[52:47] |
| **Extract Event Data** | packet[34:0] |

### Monitor Bus Packet Helper Functions

#### Packet Field Extraction

| Function | Return Type | Description |
|----------|-------------|-------------|
| **get_packet_type(pkt)** | logic [3:0] | Extract packet type [63:60] |
| **get_protocol_type(pkt)** | protocol_type_t | Extract protocol [59:57] |
| **get_event_code(pkt)** | logic [3:0] | Extract event code [56:53] |
| **get_channel_id(pkt)** | logic [5:0] | Extract channel ID [52:47] |
| **get_unit_id(pkt)** | logic [3:0] | Extract unit ID [46:43] |
| **get_agent_id(pkt)** | logic [7:0] | Extract agent ID [42:35] |
| **get_event_data(pkt)** | logic [34:0] | Extract event data [34:0] |

#### Packet Creation Function

| Function | Parameters | Description |
|----------|------------|-------------|
| **create_monitor_packet()** | packet_type, protocol, event_code, channel_id, unit_id, agent_id, event_data | Create complete 64-bit packet |

#### Event Code Creation Functions

| Function | Parameter | Description |
|----------|-----------|-------------|
| **create_axi_error_event()** | axi_error_code_t | Create AXI error event code |
| **create_axi_timeout_event()** | axi_timeout_code_t | Create AXI timeout event code |
| **create_axi_completion_event()** | axi_completion_code_t | Create AXI completion event code |
| **create_axi_threshold_event()** | axi_threshold_code_t | Create AXI threshold event code |
| **create_axi_performance_event()** | axi_performance_code_t | Create AXI performance event code |
| **create_axi_addr_match_event()** | axi_addr_match_code_t | Create AXI address match event code |
| **create_axi_debug_event()** | axi_debug_code_t | Create AXI debug event code |
| **create_apb_error_event()** | apb_error_code_t | Create APB error event code |
| **create_apb_timeout_event()** | apb_timeout_code_t | Create APB timeout event code |
| **create_apb_completion_event()** | apb_completion_code_t | Create APB completion event code |
| **create_network_error_event()** | network_error_code_t | Create Network error event code |
| **create_network_timeout_event()** | network_timeout_code_t | Create Network timeout event code |
| **create_network_completion_event()** | network_completion_code_t | Create Network completion event code |
| **create_network_credit_event()** | network_credit_code_t | Create Network credit event code |
| **create_network_channel_event()** | network_channel_code_t | Create Network channel event code |
| **create_network_stream_event()** | network_stream_code_t | Create Network stream event code |
| **create_arb_error_event()** | arb_error_code_t | Create ARB error event code |
| **create_arb_timeout_event()** | arb_timeout_code_t | Create ARB timeout event code |
| **create_arb_completion_event()** | arb_completion_code_t | Create ARB completion event code |
| **create_arb_threshold_event()** | arb_threshold_code_t | Create ARB threshold event code |
| **create_arb_performance_event()** | arb_performance_code_t | Create ARB performance event code |
| **create_arb_debug_event()** | arb_debug_code_t | Create ARB debug event code |
| **create_core_error_event()** | core_error_code_t | Create CORE error event code |
| **create_core_timeout_event()** | core_timeout_code_t | Create CORE timeout event code |
| **create_core_completion_event()** | core_completion_code_t | Create CORE completion event code |
| **create_core_threshold_event()** | core_threshold_code_t | Create CORE threshold event code |
| **create_core_performance_event()** | core_performance_code_t | Create CORE performance event code |
| **create_core_debug_event()** | core_debug_code_t | Create CORE debug event code |

#### Validation Functions

| Function | Parameters | Description |
|----------|------------|-------------|
| **is_valid_event_for_packet_type()** | packet_type, protocol, event_code | Validate event code for packet type and protocol |

#### String Functions for Debugging

| Function | Parameter | Description |
|----------|-----------|-------------|
| **get_axi_error_name()** | axi_error_code_t | Get human-readable AXI error name |
| **get_arb_error_name()** | arb_error_code_t | Get human-readable ARB error name |
| **get_core_error_name()** | core_error_code_t | Get human-readable CORE error name |
| **get_packet_type_name()** | logic [3:0] | Get packet type name string |
| **get_protocol_name()** | protocol_type_t | Get protocol name string |
| **get_event_name()** | packet_type, protocol, event_code | Get comprehensive event name |

## Debug and Monitoring Signals

### Essential Debug Signals

| Signal | Width | Purpose |
|--------|-------|---------|
| **debug_packet_counts** | 32 x 16 | Packet count per type |
| **debug_protocol_counts** | 32 x 5 | Packet count per protocol |
| **debug_error_counts** | 32 | Total error packet count |
| **debug_local_memory_level** | 16 | Local memory usage level |
| **debug_external_memory_level** | 16 | External memory usage level |

### Performance Counters

| Counter | Width | Purpose |
|---------|-------|---------|
| **total_packets_processed** | 32 | Total packets processed |
| **packets_dropped** | 32 | Packets dropped due to overflow |
| **routing_errors** | 32 | Routing configuration errors |
| **memory_full_events** | 32 | Memory full occurrences |

## Protocol Coverage Summary

### Complete Protocol Event Matrix

| Protocol | Error | Timeout | Completion | Threshold | Performance | Debug | Protocol-Specific |
|----------|-------|---------|------------|-----------|-------------|-------|------------------|
| **AXI** | [PASS] 16 | [PASS] 16 | [PASS] 16 | [PASS] 16 | [PASS] 16 | [PASS] 16 | AddrMatch [PASS] 16 |
| **Network** | [PASS] 16 | [PASS] 16 | [PASS] 16 | [FAIL] 0 | [FAIL] 0 | [FAIL] 0 | Credit/Channel/Stream [PASS] 48 |
| **APB** | [PASS] 16 | [PASS] 16 | [PASS] 16 | [PASS] 16 | [PASS] 16 | [PASS] 16 | None |
| **ARB** | [PASS] 16 | [PASS] 16 | [PASS] 16 | [PASS] 16 | [PASS] 16 | [PASS] 16 | None |
| **CORE** | [PASS] 16 | [PASS] 16 | [PASS] 16 | [PASS] 16 | [PASS] 16 | [PASS] 16 | None |

**Total Event Codes**: 544 defined across all protocols and packet types.
