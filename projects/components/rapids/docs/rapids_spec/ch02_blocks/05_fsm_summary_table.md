### RAPIDS RTL FSM Summary Table

#### Complete List of State Machines in RAPIDS RTL

| FSM Name | Module File | States | PlantUML Status | Purpose |
|----------|-------------|--------|-----------------|---------|
| **Scheduler FSM** | `scheduler.sv` | 6 states | CURRENT | Descriptor execution, credit management, program sequencing |
| **Address Alignment FSM** | `scheduler.sv` | 7 states | CURRENT | Address alignment calculation and transfer planning |
| **Descriptor Engine FSM** | `descriptor_engine.sv` | 6 states | CURRENT | APB/RDA descriptor processing, AXI read operations |
| **Program Write Engine FSM** | `program_engine.sv` | 4 states | CURRENT | Post-processing program writes, AXI write operations |
| **Sink AXI Write Engine FSM** | `sink_axi_write_engine.sv` | 7 states | CURRENT | Multi-channel AXI write arbitration and data transfer |
| **Source SRAM Control** | `source_sram_control.sv` | Resource Mgmt | CURRENT | Multi-channel SRAM resource management and EOS handling |
| **Sink SRAM Control FSM** | `sink_sram_control.sv` | 8 states | CURRENT | Single-write/multi-read SRAM control with stream boundaries |
| **Network Master FSM** | `network_master.sv` | Pipeline stages | CURRENT | Credit-based Network packet transmission |
| **Network Slave ACK FSM** | `network_slave.sv` | 6 states | CURRENT | ACK generation and priority arbitration |
| **Monitor Bus Write FSM** | `monbus_axil_group.sv` | 5 states | CURRENT | AXI4-Lite master write for monitor events |

#### State Machine Details

##### 1. Scheduler FSM (scheduler.sv)
**States:** `SCHED_IDLE`, `SCHED_WAIT_FOR_CONTROL`, `SCHED_DESCRIPTOR_ACTIVE`, `SCHED_ISSUE_PROGRAM0`, `SCHED_ISSUE_PROGRAM1`, `SCHED_ERROR`

**Key Features:**
- Dual EOS handling (packet-level + descriptor-level)
- Credit management with early warning
- Timeout detection and recovery
- Sequential program engine coordination
- Channel reset support with graceful shutdown
- Stream boundary processing (EOS support)
- Generic RDA completion interface
- Sticky error flags for comprehensive tracking
- Monitor bus integration with standardized packets

---

##### 2. Address Alignment FSM (scheduler.sv)
**States:** `ALIGN_IDLE`, `ANALYZE_ADDRESS`, `CALC_FIRST_TRANSFER`, `CALC_STREAMING`, `CALC_FINAL_TRANSFER`, `ALIGNMENT_COMPLETE`, `ALIGNMENT_ERROR`

**Key Features:**
- **Parallel Operation**: Runs in parallel with main scheduler FSM during `SCHED_DESCRIPTOR_ACTIVE`
- **Pre-Calculated Alignment**: Complete address alignment analysis before AXI transactions
- **Alignment Information Bus**: Provides comprehensive alignment data to AXI engines
- **Hidden Latency**: Alignment calculation during non-critical descriptor processing
- **Optimal Performance**: Eliminates alignment overhead from AXI critical timing paths

**Architecture Benefits:**
- Single alignment calculation unit (resource efficient)
- Pre-calculated chunk enables and burst parameters
- Complete transfer sequence planning
- Clean AXI engine interfaces without alignment logic

---

##### 3. Descriptor Engine FSM (descriptor_engine.sv)
**States:** `DESC_IDLE`, `DESC_APB_READ`, `DESC_AXI_ADDR`, `DESC_AXI_DATA`, `DESC_PROCESS`, `DESC_ERROR`

**Key Features:**
- APB interface for descriptor reads
- AXI4 master for RDA descriptor fetching
- Descriptor validation and parsing
- Stream boundary detection
- Error handling and recovery
- Monitor bus integration

---

##### 4. Program Write Engine FSM (program_engine.sv)
**States:** `PROG_IDLE`, `PROG_AXI_ADDR`, `PROG_AXI_DATA`, `PROG_RESPONSE`

**Key Features:**
- Post-processing program execution
- AXI4 master write operations
- Error handling and recovery
- Completion signaling to scheduler

---

##### 5. Sink AXI Write Engine FSM (sink_axi_write_engine.sv)
**States:** `WRITE_IDLE`, `WRITE_ADDR`, `WRITE_DATA`, `WRITE_RESP`, `WRITE_ERROR`, `WRITE_FLUSH`, `WRITE_BARRIER`

**Key Features:**
- Multi-channel arbitration (round-robin with priorities)
- Stream boundary handling (EOS barriers)
- Error recovery and reporting
- Backpressure management
- Channel reset coordination

---

##### 6. Source SRAM Control (source_sram_control.sv)
**Control Patterns:** `MONITOR`, `WRITE_VALIDATE`, `WRITE_EXECUTE`, `READ_SERVE`, `CONSUMPTION_UPDATE`, `PREALLOC_MANAGE`, `ERROR_HANDLE`

**Key Features:**
- **Multi-Channel Resource Management**: Up to 32 concurrent channels
- **EOS-Only Format**: 531-bit SRAM entries (reduced from 533-bit)
- **Preallocation System**: Credit-based write authorization
- **Channel Availability Interface**: Real-time space tracking
- **Loaded Lines Generation**: Network Master channel selection assistance
- **Deadlock Prevention**: Safety margins and threshold monitoring
- **Performance Optimization**: Concurrent multi-channel operations

**Architecture Benefits:**
- Dynamic resource allocation prevents waste
- High throughput with scalable channel count
- Comprehensive error recovery and monitoring
- Clean separation of resource management from data flow

---

##### 7. Sink SRAM Control FSM (sink_sram_control.sv)
**States:** `IDLE`, `WRITE_READY`, `WRITE_EXECUTE`, `READ_ARBITRATE`, `READ_EXECUTE`, `CONSUMPTION_NOTIFY`, `ERROR`, `BARRIER_MGMT`

**Key Features:**
- **Single Write Interface**: From Network Slave (533-bit format)
- **Multi-Channel Read Interface**: To AXI Write Engine
- **RDA Packet Bypass**: Direct routing to Descriptor Engine
- **Stream Boundary Management**: EOS barrier handling
- **Round-Robin Arbitration**: Fair channel selection with priorities
- **Threshold-Based Flow Control**: Optimal buffer utilization

**Architecture Benefits:**
- Clean write/read interface separation
- Efficient metadata handling (4.1% overhead)
- High buffer efficiency (95%+)
- Robust boundary processing

---

##### 8. Network Master FSM (network_master.sv)
**Pipeline Stages:** Credit-based transmission pipeline

**Key Features:**
- Credit-based flow control
- Packet generation and transmission
- Channel arbitration and selection
- Network interface management

---

##### 9. Network Slave ACK FSM (network_slave.sv)
**States:** `ACK_IDLE`, `ACK_PRIORITY`, `ACK_GENERATE`, `ACK_SEND`, `ACK_COMPLETE`, `ACK_ERROR`

**Key Features:**
- Priority-based ACK generation
- Multiple ACK types support
- Error handling and recovery
- Network coordination

---

##### 10. Monitor Bus Write FSM (monbus_axil_group.sv)
**States:** `WRITE_IDLE`, `WRITE_ADDR`, `WRITE_DATA_LOW`, `WRITE_DATA_HIGH`, `WRITE_RESP`

**Key Features:**
- AXI4-Lite master write transactions
- 64-bit monitor packet to 32-bit bus adaptation
- Address increment management
- Error handling and reporting
- Two-phase write for 32-bit buses (low/high words)
- Single-phase write for 64-bit buses
- Configurable base address for monitor logging
- FIFO-based packet queuing

#### FSM Interactions and Dependencies

##### Primary Data Flow FSMs
1. **Descriptor Engine** -> **Scheduler** -> **Program Write Engine**
2. **Network Slave** -> **Sink SRAM Control** -> **Sink AXI Write Engine**
3. **Source AXI Read Engine** -> **Source SRAM Control** -> **Network Master**
4. **Scheduler** -> **Address Alignment FSM** (parallel operation)

##### Support/Infrastructure FSMs
1. **Network Slave ACK FSM** - Supports packet reception
2. **Monitor Bus Write FSM** - Supports event logging
3. **Address Alignment FSM** - Supports optimal AXI performance

##### SRAM Control Comparison

| Feature | Source SRAM Control | Sink SRAM Control |
|---------|-------------------|------------------|
| **Architecture** | Resource Management | Traditional FSM |
| **Write Interface** | Multi-Channel (up to 32) | Single Channel |
| **Read Interface** | Single Channel | Multi-Channel |
| **SRAM Format** | 531 bits (EOS only) | 533 bits (EOS + Type) |
| **Overhead** | 3.3% | 4.1% |
| **Primary Feature** | Preallocation Credits | Stream Barriers |
| **Channel Selection** | Dynamic Availability | Round-Robin + Priority |

##### Reset and Error Coordination
- All FSMs support channel reset with graceful shutdown
- Error states propagate through data flow chain
- Monitor FSMs provide observability for all operations
- Source/Sink SRAM controls coordinate resource availability

#### Address Alignment FSM Integration

The Address Alignment FSM is a critical component that:

##### **Parallel Operation Model**
- Runs concurrently with main scheduler FSM during `SCHED_DESCRIPTOR_ACTIVE`
- Provides alignment information before AXI engines begin transactions
- Hidden latency calculation during descriptor processing phase

##### **Alignment Information Bus**
```systemverilog
typedef struct packed {
    logic                    is_aligned;           // Pre-calculated
    logic [5:0]              addr_offset;         // Address alignment offset
    logic [7:0]              first_burst_len;     // Optimized first burst
    logic [7:0]              optimal_burst_len;   // Streaming burst length
    logic [7:0]              final_burst_len;     // Final transfer burst
    logic [NUM_CHUNKS-1:0]   first_chunk_enables; // First transfer chunks
    logic [NUM_CHUNKS-1:0]   final_chunk_enables; // Final transfer chunks
} alignment_info_t;
```

##### **Performance Benefits**
1. **Zero AXI Latency**: No alignment calculation in critical path
2. **Optimal Burst Planning**: Pre-calculated lengths maximize efficiency
3. **Precise Resource Usage**: Exact chunk enable prediction
4. **Enhanced Throughput**: Parallel operation eliminates alignment overhead

This comprehensive FSM architecture provides robust, high-performance data processing with optimal resource utilization and comprehensive error handling across the entire RAPIDS pipeline.
