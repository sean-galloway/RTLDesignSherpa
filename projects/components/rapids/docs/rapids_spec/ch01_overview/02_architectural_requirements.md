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

# Chapter 1.2: Architectural Requirements

## 1.2.1 System Requirements

### SR-1: Delta Network Integration
RAPIDS **shall** integrate with the Delta Network as Virtual Tile 16, accepting CDA packets from HIVE-C and routing PKT_DATA packets to/from compute tiles.

### SR-2: HIVE-C Control Interface
RAPIDS **shall** provide an AXI4-Lite slave interface for control/status register access by HIVE-C.

### SR-3: Memory Interface
RAPIDS **shall** provide an AXI4 master interface supporting burst transactions to DDR2/DDR3/DDR4 memory controllers.

### SR-4: Packet Type Enforcement
RAPIDS **shall** enforce strict packet type filtering on all AXIS interfaces, rejecting invalid packet types with error indication.

## 1.2.2 Descriptor Requirements

### DR-1: Inband Descriptor Reception
RAPIDS **shall** accept descriptor injection via CDA packets from HIVE-C through the Delta Network (no memory polling required).

### DR-2: Descriptor Queue Depth
RAPIDS **shall** support a minimum of 8 pending descriptors in the descriptor FIFO.

### DR-3: Priority Scheduling
RAPIDS **shall** support priority-based descriptor scheduling with 16 priority levels (0=highest, 15=lowest).

### DR-4: Scatter-Gather Support
RAPIDS **shall** support linked descriptor chains via next descriptor pointer field.

### DR-5: Descriptor Format
RAPIDS **shall** accept 256-bit descriptors conforming to the format specified in Chapter 2.

## 1.2.3 Data Transfer Requirements

### DT-1: Memory-to-Stream (MM2S) Engine
RAPIDS **shall** support reading data from DDR memory and transmitting as PKT_DATA packets to the Delta Network.

### DT-2: Stream-to-Memory (S2MM) Multi-Channel Architecture
RAPIDS **shall** implement 16 independent S2MM channels, one per compute tile in a 4×4 mesh, with direct TID-to-channel mapping.

### DT-3: Concurrent Channel Operation
S2MM channels **shall** operate independently, allowing multiple compute tiles to write to memory simultaneously.

### DT-4: Burst Support
RAPIDS **shall** support AXI4 burst transactions with lengths up to 256 beats.

### DT-5: Data Buffering
RAPIDS **shall** provide internal FIFOs to decouple memory timing from Delta Network timing:
- MM2S data FIFO: Minimum 512 entries × 128 bits
- S2MM per-channel FIFO: Minimum 32 entries × 128 bits

## 1.2.4 Performance Requirements

### PR-1: Throughput
RAPIDS **shall** sustain a minimum of 1.3 GB/s for large (>1 KB) transfers under ideal conditions.

### PR-2: Latency - Descriptor Injection
RAPIDS **shall** process CDA packet descriptors within 20 cycles of reception (from HIVE-C via Delta Network).

### PR-3: Latency - First Data
RAPIDS **shall** deliver first data beat within 65 cycles of descriptor execution start (MM2S mode, DDR3 target).

### PR-4: Burst Efficiency
RAPIDS **shall** achieve >90% burst efficiency for transfers >1 KB.

## 1.2.5 Interface Requirements

### IF-1: AXIS CDA Input
RAPIDS **shall** provide an AXIS slave interface accepting only CDA packets (TUSER = 2'b01) from the Delta Network.

**Signals:**
- TDATA: 128 bits
- TUSER: 2 bits (must be 2'b01)
- TID: 4 bits (descriptor priority)
- TDEST: 4 bits (always 0 for RAPIDS routing)
- TLAST: 1 bit
- TVALID/TREADY: Handshake

### IF-2: AXIS Data Output (MM2S)
RAPIDS **shall** provide an AXIS master interface transmitting only PKT_DATA packets (TUSER = 2'b00) to the Delta Network.

**Signals:**
- TDATA: 128 bits
- TUSER: 2 bits (always 2'b00)
- TID: 4 bits (descriptor priority)
- TDEST: 4 bits (target tile ID 0-15)
- TLAST: 1 bit
- TKEEP: 16 bits
- TVALID/TREADY: Handshake

### IF-3: AXIS Data Input (S2MM)
RAPIDS **shall** provide an AXIS slave interface accepting only PKT_DATA packets (TUSER = 2'b00) from Delta Network compute tiles.

**Signals:**
- TDATA: 128 bits
- TUSER: 2 bits (must be 2'b00)
- TID: 4 bits (source tile ID 0-15) <- **Used for channel routing**
- TDEST: 4 bits (must be 16 for RAPIDS)
- TLAST: 1 bit
- TKEEP: 16 bits
- TVALID/TREADY: Handshake

### IF-4: AXI4 Memory Interface
RAPIDS **shall** provide an AXI4 master interface with:
- Address width: 32 bits (supports up to 4 GB)
- Data width: 128 bits (configurable 64/128/256)
- Burst types: INCR, FIXED, WRAP
- Max burst length: 256 beats
- Outstanding transactions: 16 (configurable)

### IF-5: AXI4-Lite Control Interface
RAPIDS **shall** provide an AXI4-Lite slave interface for control/status registers with:
- Address width: 12 bits (4 KB register space)
- Data width: 32 bits
- Single outstanding transaction

## 1.2.6 Error Handling Requirements

### EH-1: Packet Type Validation
RAPIDS **shall** reject packets with invalid TUSER values by:
- Asserting TREADY = 0 (not accepting packet)
- Setting appropriate error flag in status register
- Generating interrupt (if enabled)

### EH-2: AXI4 Error Response
RAPIDS **shall** handle AXI4 SLVERR and DECERR responses by:
- Setting error flag in status register
- Optionally skipping to next descriptor
- Generating interrupt (if enabled)

### EH-3: Descriptor FIFO Overflow
RAPIDS **shall** prevent descriptor loss on FIFO full by:
- Asserting backpressure (TREADY = 0) on CDA input
- Setting FIFO full flag in status register

### EH-4: Malformed Descriptor
RAPIDS **shall** handle malformed descriptors by:
- Setting error flag
- Skipping to next descriptor (if scatter-gather enabled)
- Generating interrupt (if enabled)

## 1.2.7 Monitoring and Debug Requirements

### MD-1: Performance Counters
RAPIDS **shall** provide read-only counters for:
- Bytes read from memory
- Bytes written to memory
- Packets transmitted (AXIS out)
- Packets received (AXIS in)
- AXI4 read/write cycle counts

### MD-2: Status Visibility
RAPIDS **shall** provide status indicators for:
- Descriptor FIFO occupancy
- Data FIFO status (full/empty flags)
- Current priority being processed
- Engine busy indicators (MM2S, S2MM per-channel)
- Scatter-gather chain active

### MD-3: Interrupt Generation
RAPIDS **shall** generate interrupts for:
- Descriptor completion (configurable per-descriptor)
- FIFO full conditions
- AXI4 errors
- Invalid packet type reception
- Descriptor parse errors

## 1.2.8 Configuration Requirements

### CF-1: Compile-Time Parameters
RAPIDS **shall** support compile-time configuration of:
- AXI4 data width (64/128/256 bits)
- AXI4 address width (32/64 bits)
- Descriptor FIFO depth (8-256 entries)
- Data FIFO depths (MM2S and S2MM)
- Number of S2MM channels (4/8/16 for 2×2/3×3/4×4 meshes)
- Outstanding AXI4 transaction limit

### CF-2: Runtime Configuration
RAPIDS **shall** support runtime configuration via registers:
- Engine enable/disable (MM2S, S2MM)
- Interrupt mask
- Error handling policy
- Statistics counter enable

## 1.2.9 Reset and Initialization Requirements

### RI-1: Synchronous Reset
RAPIDS **shall** support synchronous active-low reset (aresetn) for all internal state.

### RI-2: Graceful Reset
RAPIDS **shall** complete in-flight AXI4 transactions before asserting internal reset (when possible).

### RI-3: FIFO Flush
RAPIDS **shall** support selective FIFO flushing via control register:
- Descriptor FIFO flush
- Data FIFO flush (MM2S and S2MM)

### RI-4: Initialization State
After reset deassertion, RAPIDS **shall**:
- Clear all FIFOs
- Disable all engines (MM2S, S2MM channels)
- Clear all error flags
- Reset performance counters

---

**Next:** [Clocks and Reset](03_clocks_and_reset.md)

**Previous:** [Overview](01_overview.md)

**Back to:** [Index](../rapids_index.md)
