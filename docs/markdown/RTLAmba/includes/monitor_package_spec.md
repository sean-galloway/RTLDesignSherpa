# Monitor Package Specification

## Overview

The `monitor_pkg` package provides a comprehensive monitoring and error detection framework for multi-protocol bus systems. It defines standardized data structures, event codes, and packet formats for real-time monitoring, error detection, performance analysis, and debug capabilities across heterogeneous bus architectures including AXI, Network (Multi-Node On-Chip), APB, and custom protocols.

## Package Declaration

```systemverilog
package monitor_pkg;
    // Type definitions and enumerations
end

// APB state transition
always_ff @(posedge clk) begin
    if (apb_trans.protocol == PROTOCOL_APB) begin
        case (apb_trans.state)
            TRANS_ADDR_PHASE: begin  // Setup phase
                if (psel && !penable) begin
                    apb_trans.state <= TRANS_DATA_PHASE;
                    apb_trans.cmd_received <= 1'b1;
                    apb_trans.addr_timestamp <= timestamp_counter;
                end
            end
            TRANS_DATA_PHASE: begin  // Access phase
                if (psel && penable) begin
                    apb_trans.state <= TRANS_RESP_PHASE;
                    apb_trans.data_started <= 1'b1;
                    apb_trans.data_timestamp <= timestamp_counter;
                end
            end
            TRANS_RESP_PHASE: begin  // Enable phase
                if (pready) begin
                    if (pslverr) begin
                        apb_trans.state <= TRANS_ERROR;
                        apb_trans.event_code.apb_code <= APB_EVT_PSLVERR;
                    end else begin
                        apb_trans.state <= TRANS_COMPLETE;
                        apb_trans.event_code.apb_code <= APB_EVT_TRANS_COMPLETE;
                    end
                    apb_trans.resp_received <= 1'b1;
                    apb_trans.resp_timestamp <= timestamp_counter;
                end
            end
            // ... other states
        endcase
    end
endpackage : monitor_pkg
```

## Protocol Support

### Protocol Type System

The package supports multiple bus protocols through a unified monitoring framework:

```systemverilog
typedef enum logic [1:0] {
    PROTOCOL_AXI    = 2'b00,
    PROTOCOL_MNOC   = 2'b01,
    PROTOCOL_APB    = 2'b10,
    PROTOCOL_CUSTOM = 2'b11
} protocol_type_t;
```

| Protocol | Value | Description | Primary Use |
|----------|-------|-------------|-------------|
| `PROTOCOL_AXI` | 2'b00 | AMBA AXI/AXI4 protocols | High-performance interconnects |
| `PROTOCOL_MNOC` | 2'b01 | Multi-Node On-Chip protocol | Network-on-chip communication |
| `PROTOCOL_APB` | 2'b10 | AMBA APB protocol | Low-power peripheral access |
| `PROTOCOL_CUSTOM` | 2'b11 | Custom/proprietary protocols | Application-specific buses |

## Event Code Systems

### AXI Event Code Enumeration

AXI event codes for high-performance bus monitoring:

```systemverilog
typedef enum logic [3:0] {
    EVT_NONE            = 4'h0,  // No event
    
    // Generic timeout events
    EVT_CMD_TIMEOUT     = 4'h1,  // Command/Address timeout
    EVT_DATA_TIMEOUT    = 4'h2,  // Data timeout
    EVT_RESP_TIMEOUT    = 4'h3,  // Response timeout
    
    // Generic response errors
    EVT_RESP_ERROR      = 4'h4,  // Generic error response
    EVT_RESP_SLVERR     = 4'h5,  // Slave error (AXI/AHB)
    EVT_RESP_DECERR     = 4'h6,  // Decode error (AXI/AHB)
    
    // Generic protocol violations
    EVT_DATA_ORPHAN     = 4'h7,  // Data without command
    EVT_RESP_ORPHAN     = 4'h8,  // Response without transaction
    EVT_PROTOCOL        = 4'h9,  // Protocol violation
    EVT_TRANS_COMPLETE  = 4'hA,  // Transaction completed
    
    // Address miss events
    EVT_ADDR_MISS_T0    = 4'hB,  // Address missed address map (Type 0)
    EVT_ADDR_MISS_T1    = 4'hC,  // Address missed address map (Type 1)
    
    // Address match events
    EVT_DESC_ADDR_MATCH = 4'hD,  // Descriptor address match detected
    EVT_DATA_ADDR_MATCH = 4'hE,  // Data address match detected
    EVT_USER_DEFINED    = 4'hF   // User-defined event
} axi_event_code_t;
```

### APB Event Code Enumeration

APB-specific event codes for Advanced Peripheral Bus monitoring:

```systemverilog
typedef enum logic [3:0] {
    APB_EVT_NONE            = 4'h0,  // No event
    APB_EVT_SETUP_TIMEOUT   = 4'h1,  // Setup phase timeout
    APB_EVT_ACCESS_TIMEOUT  = 4'h2,  // Access phase timeout
    APB_EVT_ENABLE_TIMEOUT  = 4'h3,  // Enable phase timeout
    APB_EVT_PSLVERR         = 4'h4,  // Peripheral slave error
    APB_EVT_SETUP_VIOLATION = 4'h5,  // Setup phase protocol violation
    APB_EVT_ACCESS_VIOLATION = 4'h6, // Access phase protocol violation
    APB_EVT_STROBE_ERROR    = 4'h7,  // Write strobe error
    APB_EVT_PREADY_STUCK    = 4'h8,  // PREADY stuck low
    APB_EVT_ADDR_DECODE_ERR = 4'h9,  // Address decode error
    APB_EVT_TRANS_COMPLETE  = 4'hA,  // Transaction completed
    APB_EVT_PROT_VIOLATION  = 4'hB,  // Protection violation
    APB_EVT_RESERVED_C      = 4'hC,  // Reserved
    APB_EVT_RESERVED_D      = 4'hD,  // Reserved
    APB_EVT_RESERVED_E      = 4'hE,  // Reserved
    APB_EVT_USER_DEFINED    = 4'hF   // User-defined event
} apb_event_code_t;
```

### Network Event Code Enumeration

Specialized event codes for Multi-Node On-Chip protocol monitoring:

```systemverilog
typedef enum logic [3:0] {
    NETWORK_EVT_NONE           = 4'h0,  // No event
    NETWORK_EVT_COMPLETE       = 4'h1,  // Transaction/packet completed successfully
    NETWORK_EVT_TIMEOUT        = 4'h2,  // Timeout occurred (ACK/Credit/Packet)
    NETWORK_EVT_PARITY_ERR     = 4'h3,  // Parity error (Header/Payload/ACK)
    NETWORK_EVT_PROTOCOL_ERR   = 4'h4,  // Protocol violation
    NETWORK_EVT_OVERFLOW       = 4'h5,  // Buffer/Credit overflow
    NETWORK_EVT_UNDERFLOW      = 4'h6,  // Buffer/Credit underflow
    NETWORK_EVT_THRESHOLD      = 4'h7,  // Threshold crossed
    NETWORK_EVT_STALL          = 4'h8,  // Channel/Credit stall
    NETWORK_EVT_ORPHAN         = 4'h9,  // Orphaned packet/ACK
    NETWORK_EVT_INVALID        = 4'hA,  // Invalid type/channel/payload
    NETWORK_EVT_STREAM         = 4'hB,  // Stream event (start/end/abort)
    NETWORK_EVT_EFFICIENCY     = 4'hC,  // Efficiency/utilization metric
    NETWORK_EVT_COUNT          = 4'hD,  // Count milestone
    NETWORK_EVT_STATE          = 4'hE,  // State change
    NETWORK_EVT_USER           = 4'hF   // User defined
} network_event_code_t;
```

### Unified Event Code System

```systemverilog
typedef union packed {
    axi_event_code_t  axi_code;   // 4-bit AXI event code
    apb_event_code_t  apb_code;   // 4-bit APB event code
    network_event_code_t network_code;  // 4-bit Network event code
    logic [3:0]       raw_code;   // Raw 4-bit code
} unified_event_code_t;
```

## APB Protocol-Specific Types

### APB Transaction Phases

```systemverilog
typedef enum logic [1:0] {
    APB_PHASE_IDLE    = 2'b00,  // Bus idle
    APB_PHASE_SETUP   = 2'b01,  // Setup phase (PSEL asserted)
    APB_PHASE_ACCESS  = 2'b10,  // Access phase (PENABLE asserted)
    APB_PHASE_ENABLE  = 2'b11   // Enable phase (waiting for PREADY)
} apb_phase_t;
```

### APB Protection Types

```systemverilog
typedef enum logic [2:0] {
    APB_PROT_NORMAL     = 3'b000,  // Normal access
    APB_PROT_PRIVILEGED = 3'b001,  // Privileged access
    APB_PROT_SECURE     = 3'b010,  // Secure access
    APB_PROT_INSTRUCTION = 3'b100  // Instruction access
} apb_prot_t;
```

## Network Protocol-Specific Types

### Network Payload Types

```systemverilog
typedef enum logic [1:0] {
    NETWORK_PAYLOAD_CONFIG = 2'b00,  // CONFIG_PKT
    NETWORK_PAYLOAD_TS     = 2'b01,  // TS_PKT (Timestamp)
    NETWORK_PAYLOAD_RDA    = 2'b10,  // RDA_PKT (Remote Direct Access)
    NETWORK_PAYLOAD_RAW    = 2'b11   // RAW_PKT
} network_payload_type_t;
```

### Network ACK Types

```systemverilog
typedef enum logic [1:0] {
    NETWORK_ACK_STOP       = 2'b00,  // MSAP_STOP
    NETWORK_ACK_START      = 2'b01,  // MSAP_START
    NETWORK_ACK_CREDIT_ON  = 2'b10,  // MSAP_CREDIT_ON
    NETWORK_ACK_STOP_AT_EOS = 2'b11  // MSAP_STOP_AT_EOS
} network_ack_type_t;
```

## Transaction State Management

### Enhanced Transaction State Enumeration

```systemverilog
typedef enum logic [2:0] {
    TRANS_EMPTY          = 3'b000,  // Unused entry
    TRANS_ADDR_PHASE     = 3'b001,  // Address phase active (AXI) / Packet sent (Network)
    TRANS_DATA_PHASE     = 3'b010,  // Data phase active (AXI) / Waiting for ACK (Network)
    TRANS_RESP_PHASE     = 3'b011,  // Response phase active (AXI) / ACK received (Network)
    TRANS_COMPLETE       = 3'b100,  // Transaction complete
    TRANS_ERROR          = 3'b101,  // Transaction has error
    TRANS_ORPHANED       = 3'b110,  // Orphaned transaction
    TRANS_CREDIT_STALL   = 3'b111   // Credit stall (Network only)
} trans_state_t;
```

### State Mapping by Protocol

| State | AXI Meaning | Network Meaning | APB Meaning | Common Usage |
|-------|-------------|--------------|-------------|--------------|
| `TRANS_EMPTY` | Unused table entry | Unused table entry | Unused table entry | Initial/recycled state |
| `TRANS_ADDR_PHASE` | Address phase active | Packet sent | Setup phase (PSEL) | Command/request phase |
| `TRANS_DATA_PHASE` | Data phase active | Waiting for ACK | Access phase (PENABLE) | Data transfer phase |
| `TRANS_RESP_PHASE` | Response phase active | ACK received | Enable phase (PREADY wait) | Response/acknowledgment phase |
| `TRANS_COMPLETE` | Transaction finished | Stream/transaction complete | Transaction complete | Successful completion |
| `TRANS_ERROR` | Error detected | Protocol/parity error | PSLVERR or timeout | Error condition |
| `TRANS_ORPHANED` | Lost transaction | Orphaned packet/ACK | Invalid PSEL state | Invalid/lost transaction |
| `TRANS_CREDIT_STALL` | N/A | Credit exhaustion | N/A | Network-specific stall |

## Enhanced Transaction Tracking Structure

### Multi-Protocol Transaction Entry

```systemverilog
typedef struct packed {
    logic                   valid;           // Entry is valid
    protocol_type_t         protocol;        // Protocol type (AXI/Network/APB/Custom)
    trans_state_t           state;           // Transaction state
    logic [31:0]            id;              // Transaction ID (AXI) / Sequence (Network)
    logic [63:0]            addr;            // Transaction address / Channel addr
    logic [7:0]             len;             // Burst length (AXI) / Packet count (Network)
    logic [2:0]             size;            // Access size (AXI) / Reserved (Network)
    logic [1:0]             burst;           // Burst type (AXI) / Payload type (Network)

    // Phase completion flags
    logic                   cmd_received;    // Address phase received / Packet sent
    logic                   data_started;    // Data phase started / ACK expected
    logic                   data_completed;  // Data phase completed / ACK received
    logic                   resp_received;   // Response received / Final ACK

    // Error detection and reporting
    unified_event_code_t    event_code;      // Error code if any
    logic                   event_reported;  // Error or event has been reported

    // Timeout counters
    logic [15:0]            addr_timer;      // Address phase timer / Packet timer
    logic [15:0]            data_timer;      // Data phase timer / ACK timer
    logic [15:0]            resp_timer;      // Response phase timer / Credit timer

    // Timestamps for performance monitoring
    logic [31:0]            addr_timestamp;  // When address/packet phase completed
    logic [31:0]            data_timestamp;  // When data/ack phase completed
    logic [31:0]            resp_timestamp;  // When response/final phase completed

    // Beat counters
    logic [7:0]             data_beat_count; // Data beats received / Packets sent
    logic [7:0]             expected_beats;  // Expected beats / Expected packets

    // Enhanced tracking for Network
    logic [5:0]             channel;         // Channel ID (AXI ID / Network channel)
    logic                   eos_seen;        // EOS marker seen (Network only)
    logic                   parity_error;    // Parity error detected (Network only)
    logic [7:0]             credit_at_start; // Credits available at start (Network only)
    logic [2:0]             retry_count;     // Number of retries (Network only)
} bus_transaction_t;
```

### Field Usage by Protocol

#### Core Fields
| Field | AXI Usage | Network Usage | APB Usage |
|-------|-----------|------------|-----------|
| `protocol` | `PROTOCOL_AXI` | `PROTOCOL_MNOC` | `PROTOCOL_APB` |
| `id` | AWID/ARID | Sequence number | PSEL encoding |
| `addr` | AWADDR/ARADDR | Channel address | PADDR |
| `len` | AWLEN/ARLEN | Packet count | Always 0 |
| `size` | AWSIZE/ARSIZE | Reserved | Transfer size |
| `burst` | AWBURST/ARBURST | Payload type | PPROT encoding |

#### APB-Specific Field Usage
| Field | Purpose | Usage |
|-------|---------|-------|
| `id` | PSEL encoding | Which peripheral selected (bit position) |
| `burst` | PPROT value | Protection attribute encoding |
| `size` | Transfer size | PSTRB width indicator |
| `len` | Always 0 | Single transfer only |

#### Network-Specific Fields
| Field | Purpose | Usage |
|-------|---------|-------|
| `eos_seen` | End-of-stream detection | Track stream completion |
| `parity_error` | Parity error flag | Header/payload parity errors |
| `credit_at_start` | Initial credit count | Credit leak detection |
| `retry_count` | Retry attempts | Reliability tracking |

## Monitor Packet Format

### 64-Bit Packet Structure

Enhanced packet format supporting multi-protocol monitoring:

```systemverilog
typedef logic [63:0] monitor_packet_t;
```

### Packet Field Layout

```
Bit Range | Field Name    | Width | Description
----------|---------------|-------|------------------------------------------
[63:60]   | packet_type   | 4     | Type of packet (error, completion, etc.)
[59:58]   | protocol      | 2     | Protocol type (AXI/Network/APB/Custom)
[57:54]   | event_code    | 4     | Specific event or error code
[53:48]   | channel_id    | 6     | Channel and transaction ID identifier
[47:44]   | unit_id       | 4     | Subsystem identifier
[43:36]   | agent_id      | 8     | Module/agent identifier
[35:0]    | event_data    | 36    | Event-specific data
```

### Packet Helper Functions

```systemverilog
function automatic logic [3:0] get_packet_type(monitor_packet_t pkt);
    return pkt[63:60];
endfunction

function automatic protocol_type_t get_protocol_type(monitor_packet_t pkt);
    return protocol_type_t'(pkt[59:58]);
endfunction

function automatic logic [3:0] get_event_code(monitor_packet_t pkt);
    return pkt[57:54];
endfunction

function automatic logic [5:0] get_channel_id(monitor_packet_t pkt);
    return pkt[53:48];
endfunction

function automatic logic [3:0] get_unit_id(monitor_packet_t pkt);
    return pkt[47:44];
endfunction

function automatic logic [7:0] get_agent_id(monitor_packet_t pkt);
    return pkt[43:36];
endfunction

function automatic logic [35:0] get_event_data(monitor_packet_t pkt);
    return pkt[35:0];
endfunction

function automatic monitor_packet_t create_monitor_packet(
    logic [3:0]     packet_type,
    protocol_type_t protocol,
    logic [3:0]     event_code,
    logic [5:0]     channel_id,
    logic [3:0]     unit_id,
    logic [7:0]     agent_id,
    logic [35:0]    event_data
);
    return {packet_type, protocol, event_code, channel_id, unit_id, agent_id, event_data};
endfunction
```

## Enhanced Packet Type System

### Core Packet Types

```systemverilog
localparam logic [3:0] PktTypeError      = 4'h0;  // Error event
localparam logic [3:0] PktTypeCompletion = 4'h1;  // Transaction completion
localparam logic [3:0] PktTypeThreshold  = 4'h2;  // Threshold crossed
localparam logic [3:0] PktTypeTimeout    = 4'h3;  // Timeout event
localparam logic [3:0] PktTypePerf       = 4'h4;  // Performance metric event
localparam logic [3:0] PktTypeCredit     = 4'h5;  // Credit status (Network)
localparam logic [3:0] PktTypeChannel    = 4'h6;  // Channel status (Network)
localparam logic [3:0] PktTypeStream     = 4'h7;  // Stream event (Network)
localparam logic [3:0] PktTypeDebug      = 4'hF;  // Debug/trace event
```

### Packet Type Usage Matrix

| Packet Type | AXI Support | Network Support | APB Support | Primary Use Case |
|-------------|-------------|--------------|-------------|------------------|
| `PktTypeError` | ✓ | ✓ | ✓ | Protocol violations, decode errors |
| `PktTypeCompletion` | ✓ | ✓ | ✓ | Successful transaction completion |
| `PktTypeThreshold` | ✓ | ✓ | ✓ | Configurable threshold monitoring |
| `PktTypeTimeout` | ✓ | ✓ | ✓ | Timeout detection |
| `PktTypePerf` | ✓ | ✓ | ✓ | Performance metrics |
| `PktTypeCredit` | - | ✓ | - | Network credit management |
| `PktTypeChannel` | - | ✓ | - | Network channel status |
| `PktTypeStream` | - | ✓ | - | Network stream events |
| `PktTypeDebug` | ✓ | ✓ | ✓ | Debug and trace |

## Performance Monitoring

### Enhanced Performance Metric Types

```systemverilog
typedef enum logic [3:0] {
    PERF_ADDR_LATENCY      = 4'h0,  // Address phase latency
    PERF_DATA_LATENCY      = 4'h1,  // Data phase latency
    PERF_RESP_LATENCY      = 4'h2,  // Response phase latency
    PERF_TOTAL_LATENCY     = 4'h3,  // Total transaction latency
    PERF_THROUGHPUT        = 4'h4,  // Transaction throughput
    PERF_ERROR_RATE        = 4'h5,  // Error rate
    PERF_ACTIVE_COUNT      = 4'h6,  // Current active transaction count
    PERF_COMPLETED_COUNT   = 4'h7,  // Total completed transaction count
    PERF_ERROR_COUNT       = 4'h8,  // Total error transaction count
    PERF_CREDIT_EFFICIENCY = 4'h9,  // Credit utilization (Network)
    PERF_CHANNEL_UTIL      = 4'hA,  // Channel utilization (Network)
    PERF_PACKET_RATE       = 4'hB,  // Packet rate (Network)
    PERF_CUSTOM            = 4'hF   // Custom performance metric
} perf_metric_t;
```

### Protocol-Specific Performance Metrics

#### AXI Performance Metrics
| Metric | Calculation | Purpose |
|--------|-------------|---------|
| `PERF_ADDR_LATENCY` | AWREADY assertion time | Address channel efficiency |
| `PERF_DATA_LATENCY` | Data transfer duration | Write data performance |
| `PERF_RESP_LATENCY` | Response time | Read data/write response speed |
| `PERF_TOTAL_LATENCY` | End-to-end transaction time | Overall performance |

#### APB Performance Metrics
| Metric | Calculation | Purpose |
|--------|-------------|---------|
| `PERF_ADDR_LATENCY` | Setup phase duration | Setup timing efficiency |
| `PERF_DATA_LATENCY` | Access phase duration | Access phase performance |
| `PERF_RESP_LATENCY` | PREADY wait time | Peripheral response speed |
| `PERF_TOTAL_LATENCY` | Complete transaction time | Overall APB performance |
| Metric | Calculation | Purpose |
|--------|-------------|---------|
| `PERF_CREDIT_EFFICIENCY` | Credits used / Credits available | Credit utilization |
| `PERF_CHANNEL_UTIL` | Active time / Total time | Channel efficiency |
| `PERF_PACKET_RATE` | Packets per time window | Network throughput |

## Debug Event System

### Enhanced Debug Event Types

```systemverilog
typedef enum logic [3:0] {
    DEBUG_STATE_CHANGE  = 4'h0,  // Transaction state changed
    DEBUG_ADDR_PHASE    = 4'h1,  // Address phase event
    DEBUG_DATA_PHASE    = 4'h2,  // Data phase event
    DEBUG_RESP_PHASE    = 4'h3,  // Response phase event
    DEBUG_TIMEOUT       = 4'h4,  // Timeout event detail
    DEBUG_ERROR         = 4'h5,  // Error event detail
    DEBUG_TRANS_CREATE  = 4'h6,  // Transaction created
    DEBUG_TRANS_REMOVE  = 4'h7,  // Transaction removed
    DEBUG_COUNTER       = 4'h8,  // Counter event
    DEBUG_CREDIT_CHANGE = 4'h9,  // Credit change (Network)
    DEBUG_PACKET_TRACE  = 4'hA,  // Packet trace (Network)
    DEBUG_ACK_TRACE     = 4'hB,  // ACK trace (Network)
    DEBUG_CUSTOM        = 4'hF   // Custom debug event
} debug_event_t;
```

## Threshold Monitoring

### Enhanced Threshold Event Types

```systemverilog
typedef enum logic [3:0] {
    THRESH_ACTIVE_COUNT   = 4'h0,  // Active transaction count threshold
    THRESH_LATENCY        = 4'h1,  // Latency threshold
    THRESH_ERROR_RATE     = 4'h2,  // Error rate threshold
    THRESH_BUFFER_LEVEL   = 4'h3,  // Buffer fill level threshold
    THRESH_CREDIT_LOW     = 4'h4,  // Credit low threshold (Network)
    THRESH_PACKET_RATE    = 4'h5,  // Packet rate threshold (Network)
    THRESH_CHANNEL_STALL  = 4'h6,  // Channel stall threshold (Network)
    THRESH_CUSTOM         = 4'hF   // Custom threshold
} threshold_event_t;
```

## Network-Specific Event Types

### Credit Event Types

```systemverilog
typedef enum logic [3:0] {
    CREDIT_ALLOCATED     = 4'h0,  // Credits allocated
    CREDIT_CONSUMED      = 4'h1,  // Credits consumed
    CREDIT_RETURNED      = 4'h2,  // Credits returned
    CREDIT_OVERFLOW      = 4'h3,  // Credit overflow detected
    CREDIT_UNDERFLOW     = 4'h4,  // Credit underflow detected
    CREDIT_EXHAUSTED     = 4'h5,  // All credits exhausted
    CREDIT_RESTORED      = 4'h6,  // Credits restored
    CREDIT_EFFICIENCY    = 4'h7,  // Credit efficiency metric
    CREDIT_LEAK          = 4'h8,  // Credit leak detected
    CREDIT_CUSTOM        = 4'hF   // Custom credit event
} credit_event_t;
```

### Channel Event Types

```systemverilog
typedef enum logic [3:0] {
    CHANNEL_ACTIVE       = 4'h0,  // Channel became active
    CHANNEL_IDLE         = 4'h1,  // Channel became idle
    CHANNEL_STALLED      = 4'h2,  // Channel stalled
    CHANNEL_RESET        = 4'h3,  // Channel reset
    CHANNEL_ERROR        = 4'h4,  // Channel error
    CHANNEL_OVERFLOW     = 4'h5,  // Channel buffer overflow
    CHANNEL_UNDERFLOW    = 4'h6,  // Channel buffer underflow
    CHANNEL_THRESHOLD    = 4'h7,  // Channel threshold crossed
    CHANNEL_CUSTOM       = 4'hF   // Custom channel event
} channel_event_t;
```

### Stream Event Types

```systemverilog
typedef enum logic [3:0] {
    STREAM_START         = 4'h0,  // Stream started
    STREAM_END           = 4'h1,  // Stream ended (EOS)
    STREAM_ABORT         = 4'h2,  // Stream aborted
    STREAM_PAUSE         = 4'h3,  // Stream paused
    STREAM_RESUME        = 4'h4,  // Stream resumed
    STREAM_ERROR         = 4'h5,  // Stream error
    STREAM_OVERFLOW      = 4'h6,  // Stream buffer overflow
    STREAM_UNDERFLOW     = 4'h7,  // Stream buffer underflow
    STREAM_CUSTOM        = 4'hF   // Custom stream event
} stream_event_t;
```

## Implementation Examples

### Multi-Protocol Monitor Packet Creation

```systemverilog
// AXI error packet
monitor_packet_t axi_error_packet = create_monitor_packet(
    PktTypeError,           // packet_type
    PROTOCOL_AXI,           // protocol
    EVT_RESP_SLVERR,        // event_code
    6'h12,                  // channel_id (AXI ID)
    4'h3,                   // unit_id
    8'hA5,                  // agent_id
    36'h1000_1234           // event_data (address)
);

// AXI address match packet for descriptor
monitor_packet_t axi_desc_match_packet = create_monitor_packet(
    PktTypeCompletion,      // packet_type (or PktTypeDebug for watchpoints)
    PROTOCOL_AXI,           // protocol
    EVT_DESC_ADDR_MATCH,    // event_code
    6'h12,                  // channel_id (AXI ID)
    4'h3,                   // unit_id
    8'hA5,                  // agent_id
    36'h1000_1234           // event_data (matched descriptor address)
);

// AXI data address match packet
monitor_packet_t axi_data_match_packet = create_monitor_packet(
    PktTypeCompletion,      // packet_type (or PktTypeDebug for watchpoints)
    PROTOCOL_AXI,           // protocol
    EVT_DATA_ADDR_MATCH,    // event_code
    6'h05,                  // channel_id (AXI ID)
    4'h2,                   // unit_id
    8'hB2,                  // agent_id
    36'h2000_5678           // event_data (matched data address)
);

// APB setup timeout packet
monitor_packet_t apb_timeout_packet = create_monitor_packet(
    PktTypeTimeout,         // packet_type
    PROTOCOL_APB,           // protocol
    APB_EVT_SETUP_TIMEOUT,  // event_code
    6'h04,                  // channel_id (PSEL encoding)
    4'h1,                   // unit_id
    8'hD4,                  // agent_id
    36'h3000_9ABC           // event_data (APB address)
);

// APB slave error packet
monitor_packet_t apb_error_packet = create_monitor_packet(
    PktTypeError,           // packet_type
    PROTOCOL_APB,           // protocol
    APB_EVT_PSLVERR,        // event_code
    6'h02,                  // channel_id (PSEL encoding)
    4'h1,                   // unit_id
    8'hD4,                  // agent_id
    36'h4000_DEF0           // event_data (APB address)
);

// Network credit exhausted packet
monitor_packet_t network_credit_packet = create_monitor_packet(
    PktTypeCredit,          // packet_type
    PROTOCOL_MNOC,          // protocol
    CREDIT_EXHAUSTED,       // event_code
    6'h05,                  // channel_id
    4'h2,                   // unit_id
    8'hB2,                  // agent_id
    {28'h0, 8'h10}         // event_data (credit count)
);

// Network stream end packet
monitor_packet_t network_stream_packet = create_monitor_packet(
    PktTypeStream,          // packet_type
    PROTOCOL_MNOC,          // protocol
    STREAM_END,             // event_code
    6'h08,                  // channel_id
    4'h1,                   // unit_id
    8'hC3,                  // agent_id
    36'h2000_5678          // event_data (stream address)
);
```

### Multi-Protocol Transaction Tracking

```systemverilog
// Initialize AXI transaction entry
bus_transaction_t axi_transaction;
axi_transaction.valid = 1'b1;
axi_transaction.protocol = PROTOCOL_AXI;
axi_transaction.state = TRANS_ADDR_PHASE;
axi_transaction.id = {28'b0, awid};
axi_transaction.addr = {32'b0, awaddr};
axi_transaction.len = awlen;
axi_transaction.size = awsize;
axi_transaction.burst = awburst;
axi_transaction.expected_beats = awlen + 1;
axi_transaction.event_code.axi_code = EVT_NONE;

// Initialize APB transaction entry
bus_transaction_t apb_transaction;
apb_transaction.valid = 1'b1;
apb_transaction.protocol = PROTOCOL_APB;
apb_transaction.state = TRANS_ADDR_PHASE;  // Setup phase
apb_transaction.id = psel_encoding;        // Which PSEL bit is active
apb_transaction.addr = {32'b0, paddr};
apb_transaction.len = 8'h0;                // Always single transfer
apb_transaction.size = pstrb_width;        // Based on PSTRB
apb_transaction.burst = pprot;             // Protection attributes
apb_transaction.expected_beats = 8'h1;     // Always 1 for APB
apb_transaction.event_code.apb_code = APB_EVT_NONE;
// Initialize Network transaction entry
bus_transaction_t network_transaction;
network_transaction.valid = 1'b1;
network_transaction.protocol = PROTOCOL_MNOC;
network_transaction.state = TRANS_ADDR_PHASE;
network_transaction.id = packet_sequence;
network_transaction.addr = channel_address;
network_transaction.len = packet_count;
network_transaction.burst = network_payload_type;
network_transaction.event_code.network_code = NETWORK_EVT_NONE;
network_transaction.credit_at_start = current_credits;
network_transaction.eos_seen = 1'b0;
```

### Protocol-Specific State Transitions

```systemverilog
// AXI state transition
always_ff @(posedge clk) begin
    if (axi_trans.protocol == PROTOCOL_AXI) begin
        case (axi_trans.state)
            TRANS_ADDR_PHASE: begin
                if (awready && awvalid) begin
                    axi_trans.state <= TRANS_DATA_PHASE;
                    axi_trans.cmd_received <= 1'b1;
                    axi_trans.addr_timestamp <= timestamp_counter;
                end
            end
            TRANS_DATA_PHASE: begin
                if (wready && wvalid && wlast) begin
                    axi_trans.state <= TRANS_RESP_PHASE;
                    axi_trans.data_completed <= 1'b1;
                    axi_trans.data_timestamp <= timestamp_counter;
                end
            end
            // ... other states
        endcase
    end
end

// Network state transition
always_ff @(posedge clk) begin
    if (network_trans.protocol == PROTOCOL_MNOC) begin
        case (network_trans.state)
            TRANS_ADDR_PHASE: begin
                if (packet_sent) begin
                    network_trans.state <= TRANS_DATA_PHASE;
                    network_trans.cmd_received <= 1'b1;
                    network_trans.addr_timestamp <= timestamp_counter;
                end
            end
            TRANS_DATA_PHASE: begin
                if (ack_received) begin
                    network_trans.state <= TRANS_RESP_PHASE;
                    network_trans.data_completed <= 1'b1;
                    network_trans.data_timestamp <= timestamp_counter;
                end
            end
            // ... other states
        endcase
    end
end
```

## Integration Guidelines

### Multi-Protocol Monitor Instance

```systemverilog
module universal_bus_monitor #(
    parameter UNIT_ID = 4'h0,
    parameter AGENT_ID = 8'h00,
    parameter PROTOCOL_TYPE = PROTOCOL_AXI
) (
    input  logic clk,
    input  logic rst_n,
    
    // Generic bus interface
    input  logic        cmd_valid,
    input  logic        cmd_ready,
    input  logic [63:0] cmd_addr,
    input  logic [31:0] cmd_data,
    
    // Protocol-specific signals
    input  logic [7:0]  axi_id,
    input  logic [7:0]  network_credits,
    input  logic        network_eos,
    
    // Monitor packet output
    output logic                monitor_packet_valid,
    output monitor_packet_t     monitor_packet_data,
    input  logic                monitor_packet_ready
);

import monitor_pkg::*;

// Protocol-aware transaction tracking
bus_transaction_t transaction_table [0:15];

// Protocol selection logic
always_comb begin
    case (PROTOCOL_TYPE)
        PROTOCOL_AXI: begin
            // AXI-specific monitoring logic
        end
        PROTOCOL_MNOC: begin
            // Network-specific monitoring logic
        end
        PROTOCOL_APB: begin
            // APB-specific monitoring logic
        end
        default: begin
            // Custom protocol monitoring
        end
    endcase
end

endmodule
```

### System-Level Multi-Protocol Monitoring

```systemverilog
module system_monitor_hub (
    input logic clk,
    input logic rst_n,
    
    // AXI monitor inputs
    input logic                 axi_packet_valid,
    input monitor_packet_t      axi_packet_data,
    
    // Network monitor inputs
    input logic                 network_packet_valid,
    input monitor_packet_t      network_packet_data,
    
    // APB monitor inputs
    input logic                 apb_packet_valid,
    input monitor_packet_t      apb_packet_data,
    
    // Aggregated output
    output logic               system_packet_valid,
    output monitor_packet_t    system_packet_data,
    
    // Protocol-specific interrupts
    output logic               axi_error_interrupt,
    output logic               network_credit_interrupt,
    output logic               apb_timeout_interrupt,
    output logic               system_threshold_interrupt
);

import monitor_pkg::*;

// Protocol-aware packet routing and analysis
always_comb begin
    case (get_protocol_type(input_packet))
        PROTOCOL_AXI: begin
            // AXI-specific interrupt logic
            if (get_packet_type(input_packet) == PktTypeError) begin
                axi_error_interrupt = 1'b1;
            end
        end
        PROTOCOL_MNOC: begin
            // Network-specific interrupt logic
            if (get_packet_type(input_packet) == PktTypeCredit) begin
                network_credit_interrupt = 1'b1;
            end
        end
        // ... other protocols
    endcase
end

endmodule
```

## Best Practices

### Multi-Protocol Design Principles
1. **Use protocol field** for conditional monitoring logic
2. **Implement protocol-specific state machines** within unified framework
3. **Share common timeout and error detection** logic across protocols
4. **Use unified event reporting** with protocol-specific event codes

### Performance Considerations
1. **Separate transaction tables** for different protocols if needed
2. **Protocol-aware packet filtering** to reduce monitoring overhead
3. **Configurable monitoring depth** per protocol type
4. **Efficient credit tracking** for Network protocols

### Verification and Debug
1. **Protocol-specific checkers** for packet format validation
2. **Cross-protocol correlation** for system-level analysis
3. **Protocol-aware debug events** for detailed trace analysis
4. **Unified logging format** supporting all protocol types

This enhanced monitoring framework provides comprehensive multi-protocol support while maintaining backward compatibility with existing AXI monitoring infrastructure, enabling robust system-wide monitoring across heterogeneous bus architectures.