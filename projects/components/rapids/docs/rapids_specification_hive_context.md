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

# RAPIDS DMA Specification
**Reconfigurable Accelerator Protocol for Intelligent Data Streaming**  
Version 0.3 - Early Proof of Concept (Draft)

---

## 1. Executive Summary

RAPIDS is a high-performance DMA engine designed to bridge AXI4 memory-mapped interfaces with the DELTA AXIS compute network. It operates under control of the HIVE master controller (VexRiscv HIVE-C) which provides inband descriptor injection through the DELTA network. RAPIDS intelligently routes data between external DDR memory and compute tiles while filtering packet types to prevent protocol violations.

**Key Features:**
- Scatter-gather DMA with linked descriptor chains
- 2D transfer support with configurable strides
- Inband descriptor reception via AXIS (no memory polling)
- Multi-priority descriptor scheduling
- Packet type filtering on all AXIS interfaces
- Completion interrupt generation
- Performance monitoring and statistics

---

## 2. System Integration

### 2.1 Position in Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                         HIVE-C                              │
│                    (VexRiscv Master)                        │
│                                                             │
│  Generates descriptors, injects via AXIS with PKT_DESC     │
└──────────────────────┬──────────────────────────────────────┘
                       │ AXIS TX (PKT_DESC only)
                       ▼
              ┌────────────────────┐
              │   DELTA Network    │
              │   Routes packets   │
              │   based on TUSER   │
              └────────┬───────────┘
                       │ PKT_DESC → RAPIDS
                       │ PKT_DATA → Compute Tiles
                       ▼
┌──────────────────────────────────────────────────────────────┐
│                      RAPIDS DMA Engine                       │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  AXIS Descriptor Input (Slave)                      │    │
│  │  - Accepts: PKT_DESC only                           │    │
│  │  - Rejects: PKT_DATA, PKT_CONFIG, PKT_STATUS        │    │
│  │  - Routes to: Descriptor FIFO                       │    │
│  └──────────────────┬──────────────────────────────────┘    │
│                     ▼                                        │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  Descriptor Processing Engine                       │    │
│  │  - Parses 256-bit descriptors                       │    │
│  │  - Schedules by priority                            │    │
│  │  - Generates AXI4 transactions                      │    │
│  └──────────────────┬──────────────────────────────────┘    │
│                     ▼                                        │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  AXI4 Memory Interface (Master)                     │    │
│  │  - Reads from DDR (activations, weights)            │    │
│  │  - Writes to DDR (results)                          │    │
│  └──────────────────┬──────────────────────────────────┘    │
│                     ▼                                        │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  AXIS Data Output (Master)                          │    │
│  │  - Sends: PKT_DATA only                             │    │
│  │  - Never sends: PKT_DESC, PKT_CONFIG, PKT_STATUS    │    │
│  │  - Routes to: DELTA network → Compute Tiles         │    │
│  └──────────────────┬──────────────────────────────────┘    │
└────────────────────┼────────────────────────────────────────┘
                     │
                     ▼
            ┌─────────────────┐
            │ DELTA Network   │
            │ (PKT_DATA only) │
            └─────────┬───────┘
                      ▼
              Compute Tiles

Memory: DDR2/DDR3 ◄──AXI4 Read/Write──┤ RAPIDS ├──AXIS──► DELTA
```

### 2.2 Packet Type Handling

RAPIDS enforces strict packet type filtering on all AXIS interfaces:

| Interface | Direction | Accepts | Sends | Rejects |
|-----------|-----------|---------|-------|---------|
| **AXIS Descriptor** | Slave (Input) | PKT_DESC | - | PKT_DATA, PKT_CONFIG, PKT_STATUS |
| **AXIS Data Out** | Master (Output) | - | PKT_DATA | PKT_DESC, PKT_CONFIG, PKT_STATUS |
| **AXIS Data In** | Slave (Input) | PKT_DATA | - | PKT_DESC, PKT_CONFIG, PKT_STATUS |

**Rejection Behavior:**
- Invalid packet type detected on input: Assert TREADY=0, set error flag, generate interrupt
- Prevent transmission of invalid types: Hardware enforces TUSER encoding in transmission logic

---

## 3. AXIS Packet Encoding

### 3.1 Descriptor Packets (PKT_DESC)

**Source:** HIVE-C controller via DELTA network  
**Destination:** RAPIDS descriptor FIFO  
**Format:** 256 bits (2 AXIS beats at 128-bit width)

```
TUSER[1:0] = 2'b01  // PKT_DESC
TDATA[255:0] = Descriptor fields (see Section 4.2)
TLAST = 1 on final beat
TID[3:0] = Priority level (0=highest, 15=lowest)
TDEST[3:0] = 4'h0 (always RAPIDS)
```

**Routing in DELTA:**
- DELTA network examines TUSER[1:0]
- PKT_DESC packets routed to RAPIDS descriptor input
- All other traffic continues to compute tiles

### 3.2 Data Packets (PKT_DATA)

**Source (Memory→Network):** RAPIDS Data Out (AXIS Master)  
**Destination:** DELTA network → Compute Tiles  
**Source (Network→Memory):** Compute Tiles → RAPIDS Data In (AXIS Slave)  
**Destination:** DDR memory via AXI4

```
TUSER[1:0] = 2'b00  // PKT_DATA
TDATA[127:0] = Payload (activations, weights, results)
TLAST = 1 on final beat of transfer
TID[3:0] = Source tile ID (0-15) - CRITICAL for S2MM channel mapping
TDEST[3:0] = Destination tile ID (0-15)
TKEEP[15:0] = Byte enables (all 1's for full beats)
```

**CRITICAL: Source Tracking for S2MM**

When compute tiles send results back to RAPIDS:
- Tile must set TID = its own tile ID (0-15)
- RAPIDS uses TID to determine which S2MM channel to route data
- **Direct mapping: TID[3:0] → S2MM Channel[3:0]**
- Each channel has independent descriptor queue and write engine

**RAPIDS Never Generates:**
- PKT_DESC (only HIVE-C generates these)
- PKT_CONFIG (only HIVE-C or SERV monitors generate)
- PKT_STATUS (only SERV monitors generate)

**RAPIDS Always Validates:**
- Input AXIS packets must have TUSER=PKT_DESC or PKT_DATA
- Any other TUSER value triggers error condition

---

## 4. Descriptor Format and Processing

### 4.1 Descriptor Structure (256 bits)

```
Bits [255:192]: Source Address (64-bit)
  - DDR byte address for read operations
  - Must be aligned to burst boundary (cache line)
  
Bits [191:128]: Destination Address (64-bit)
  - DDR byte address for write operations (results)
  - Must be aligned to burst boundary
  
Bits [127:96]: Transfer Length (32-bit bytes)
  - Total data to transfer (not including descriptor overhead)
  - Maximum: 16 MB per descriptor
  
Bits [95:64]: 2D Stride Configuration (32-bit)
  - [31:16] Y-stride (bytes between rows)
  - [15:0]  X-length (bytes per row)
  - Used when Control Flags[7] = 1
  
Bits [63:32]: Control Flags (32-bit)
  [31:28] - Burst Size: AXI beats (1-16)
  [27:24] - Burst Type: 0=FIXED, 1=INCR, 2=WRAP
  [23:20] - Priority Level: 0 (high) to 15 (low)
  [19:16] - Destination Tile ID: 0-15 for 4×4 mesh
  [15:12] - Source Tile ID: 0-15 (for S2MM descriptors only)
  [11:8]  - Interrupt Vector: 0-15
  [7]     - Enable 2D Transfer Mode
  [6]     - Enable Scatter-Gather (follow next_ptr)
  [5]     - Generate Completion Interrupt
  [4]     - Cache Coherent Access (future)
  [3:0]   - Descriptor Type:
            0 = MM2S (Memory→Network, read DDR, send to tile)
            1 = S2MM (Network→Memory, receive from tile, write DDR)
            2-15 = Reserved
  
Bits [31:0]: Next Descriptor Pointer (32-bit)
  - Physical address of next descriptor in chain
  - Valid only if Control Flags[6] = 1
  - Set to 0x0000_0000 for single-shot
```

### 4.2 Descriptor Reception Flow

```
1. HIVE-C generates descriptor(s) in firmware
2. HIVE-C writes descriptor to AXIS TX FIFO
3. HIVE-C sets TUSER = PKT_DESC (2'b01)
4. DELTA network routes to RAPIDS based on TUSER
5. RAPIDS descriptor input validates TUSER == PKT_DESC
6. Descriptor written to internal FIFO (depth: 8 entries)
7. Scheduler prioritizes based on TID[3:0] field
8. Descriptor engine fetches from FIFO when ready
```

**Error Conditions:**
- TUSER != PKT_DESC: Reject packet, set ERROR_INVALID_TYPE register
- Descriptor FIFO full: Assert backpressure (TREADY=0)
- Malformed descriptor: Set ERROR_MALFORMED register, skip to next

---

## 5. Data Transfer Engines

### 5.1 Memory-to-Stream (MM2S) Engine

**Purpose:** Read data from DDR, send to DELTA network as PKT_DATA

**Operation:**
1. Fetch descriptor from scheduler
2. Parse source address and length
3. Generate AXI4 read transactions (bursts of up to 256 beats)
4. Buffer read data in internal FIFO (512 entries × 128 bits)
5. Format AXIS packets:
   - TUSER = PKT_DATA (2'b00)
   - TID = descriptor priority
   - TDEST = destination tile from descriptor[19:16]
6. Transmit to DELTA network with backpressure handling
7. On completion:
   - Update statistics counters
   - Generate interrupt if descriptor[5] == 1
   - Fetch next descriptor if scatter-gather enabled

**Performance:**
- DDR read bandwidth: 4-5 GB/s (NexysA7), 10-12 GB/s (Genesys2)
- AXIS output: 128 bits @ 100 MHz = 1.6 GB/s
- Bottleneck: AXIS network (by design, multiple sources share)

### 5.2 Stream-to-Memory (S2MM) Engine

**Purpose:** Receive PKT_DATA from compute tiles, write to DDR

**CRITICAL Architecture: Multi-Channel S2MM**

RAPIDS implements **16 independent S2MM channels**, one per compute tile:
- Channel 0 receives data from Tile 0 (TID=0)
- Channel 1 receives data from Tile 1 (TID=1)
- ...
- Channel 15 receives data from Tile 15 (TID=15)

**Direct Source-to-Channel Mapping:**
```verilog
// Incoming packet from DELTA network
logic [3:0] source_tile_id = axis_in_tid[3:0];

// Route to appropriate S2MM channel
logic [15:0] channel_select = 16'b1 << source_tile_id;

assign s2mm_channel[0].axis_tvalid  = axis_in_tvalid && (source_tile_id == 4'd0);
assign s2mm_channel[1].axis_tvalid  = axis_in_tvalid && (source_tile_id == 4'd1);
// ... (repeated for all 16 channels)
assign s2mm_channel[15].axis_tvalid = axis_in_tvalid && (source_tile_id == 4'd15);
```

**Per-Channel Operation:**
1. Receive AXIS packets from DELTA (TUSER must be PKT_DATA)
2. Validate TUSER == PKT_DATA, reject others
3. Validate TID[3:0] matches channel ID
4. Buffer in per-channel FIFO (32 entries × 128 bits per channel)
5. Fetch descriptor from per-channel queue
6. Descriptor specifies destination DDR address for this tile's results
7. Generate AXI4 write transactions (bursts of up to 256 beats)
8. On completion:
   - Update per-channel statistics counters
   - Generate interrupt if descriptor[5] == 1

**Packet Validation:**
```verilog
// Channel N validation logic
always_comb begin
  // Must be PKT_DATA type
  if (axis_in_tvalid && axis_in_tuser != PKT_DATA) begin
    axis_in_tready = 1'b0;  // Reject
    error_invalid_input = 1'b1;
  end
  
  // TID must match channel (source tile)
  if (axis_in_tvalid && axis_in_tid != MY_CHANNEL_ID) begin
    axis_in_tready = 1'b0;  // Not for this channel
  end
  
  // TDEST must be 16 (RAPIDS virtual tile)
  if (axis_in_tvalid && axis_in_tdest != 4'd16) begin
    axis_in_tready = 1'b0;  // Wrong destination
    error_invalid_dest = 1'b1;
  end
end
```

**Why Multi-Channel Architecture?**

1. **Concurrent writes:** Multiple tiles can send results simultaneously
2. **Independent addressing:** Each tile's data goes to different DDR region
3. **Per-tile flow control:** Backpressure on one tile doesn't affect others
4. **Simplified descriptor management:** One descriptor queue per tile

---

## 6. AXI4 Memory Interface

### 6.1 Interface Configuration

**Address Width:** 32 bits (supports up to 4 GB)  
**Data Width:** 128 bits (configurable 64/128/256)  
**Burst Support:** INCR (incrementing), FIXED, WRAP  
**Max Burst Length:** 256 beats (AXI4 maximum)  
**Outstanding Transactions:** 16 (configurable)

### 6.2 Read Channel (Memory → Network)

```
// AXI4 Read Address Channel
output [31:0]  m_axi_araddr;   // Read address
output [7:0]   m_axi_arlen;    // Burst length - 1
output [2:0]   m_axi_arsize;   // Bytes per beat (4 = 128 bits)
output [1:0]   m_axi_arburst;  // 01=INCR
output         m_axi_arvalid;
input          m_axi_arready;

// AXI4 Read Data Channel
input [127:0]  m_axi_rdata;
input [1:0]    m_axi_rresp;   // 00=OKAY
input          m_axi_rlast;
input          m_axi_rvalid;
output         m_axi_rready;
```

**Optimization:**
- Early burst termination on RLAST
- Out-of-order completion support via transaction IDs
- Automatic address alignment to cache line boundaries

### 6.3 Write Channel (Network → Memory)

```
// AXI4 Write Address Channel
output [31:0]  m_axi_awaddr;
output [7:0]   m_axi_awlen;
output [2:0]   m_axi_awsize;
output [1:0]   m_axi_awburst;
output         m_axi_awvalid;
input          m_axi_awready;

// AXI4 Write Data Channel
output [127:0] m_axi_wdata;
output [15:0]  m_axi_wstrb;   // Byte strobes
output         m_axi_wlast;
output         m_axi_wvalid;
input          m_axi_wready;

// AXI4 Write Response Channel
input [1:0]    m_axi_bresp;
input          m_axi_bvalid;
output         m_axi_bready;
```

---

## 7. Control and Status Registers

### 7.1 Register Map (AXI4-Lite Slave)

HIVE-C accesses these registers via AXI4-Lite:

```
Base + 0x000: CONTROL         (RW) - Global enable, reset
Base + 0x004: STATUS          (RO) - Busy, error flags
Base + 0x008: DESC_FIFO_COUNT (RO) - Pending descriptors
Base + 0x00C: DESC_PROCESSED  (RO) - Completed count
Base + 0x010: IRQ_ENABLE      (RW) - Interrupt mask
Base + 0x014: IRQ_STATUS      (RW1C) - Interrupt flags
Base + 0x018: ERROR_FLAGS     (RW1C) - Error conditions

// Statistics (read-only)
Base + 0x100: BYTES_READ      (RO) - Total bytes from DDR
Base + 0x104: BYTES_WRITTEN   (RO) - Total bytes to DDR
Base + 0x108: PACKETS_TX      (RO) - AXIS packets sent
Base + 0x10C: PACKETS_RX      (RO) - AXIS packets received
Base + 0x110: AXI_READ_CYCLES (RO) - DDR read latency sum
Base + 0x114: AXI_WRITE_CYCLES (RO) - DDR write latency sum

// Performance counters
Base + 0x200: CYCLE_COUNTER   (RO) - Free-running clock cycles
Base + 0x204: ACTIVE_CYCLES   (RO) - Cycles with active transfer
```

### 7.2 Control Register (0x000)

```
[31:8]  - Reserved
[7]     - Soft Reset (write 1 to reset, auto-clears)
[6]     - Flush Descriptor FIFO
[5]     - Flush Data FIFOs
[4]     - Enable Statistics Counters
[3:2]   - Reserved
[1]     - Enable S2MM Engine
[0]     - Enable MM2S Engine
```

### 7.3 Status Register (0x004)

```
[31:16] - Reserved
[15]    - Descriptor FIFO Full
[14]    - Descriptor FIFO Empty
[13]    - MM2S Data FIFO Full
[12]    - S2MM Data FIFO Full
[11]    - AXI Read Error
[10]    - AXI Write Error
[9]     - Invalid Descriptor Error
[8]     - Invalid Packet Type Error
[7:4]   - Current Priority Processing
[3]     - S2MM Engine Busy
[2]     - MM2S Engine Busy
[1]     - Scatter-Gather Active
[0]     - Any Engine Active
```

---

## 8. Interrupt System

### 8.1 Interrupt Sources

RAPIDS generates interrupts to notify HIVE-C of events:

```
IRQ[7:0] - Completion interrupts (per descriptor vector)
IRQ[8]   - Descriptor FIFO full
IRQ[9]   - AXI error (read or write)
IRQ[10]  - Invalid packet type received
IRQ[11]  - Descriptor parse error
IRQ[15]  - Statistics overflow
```

### 8.2 Interrupt Handling

HIVE-C firmware interrupt handler:

```c
void rapids_irq_handler(void) {
    uint32_t irq_status = RAPIDS_IRQ_STATUS;
    
    if (irq_status & IRQ_COMPLETION_MASK) {
        // Descriptor(s) completed
        update_completion_count();
        schedule_next_batch();
    }
    
    if (irq_status & IRQ_AXI_ERROR) {
        // Memory access fault
        log_error();
        retry_or_abort();
    }
    
    if (irq_status & IRQ_INVALID_PACKET) {
        // Protocol violation - someone sent wrong packet type
        dump_debug_info();
    }
    
    // Clear handled interrupts
    RAPIDS_IRQ_STATUS = irq_status;
}
```

---

## 9. Data Flow Examples

### 9.1 Typical Transfer: Load Activations

```
1. HIVE-C generates descriptor:
   - src_addr = 0x1000_0000 (DDR activation buffer)
   - dst_addr = 0 (unused for MM2S)
   - length = 0x1000 (4 KB)
   - tile_id = 5 (destination tile)
   - type = 0 (Memory→Network)

2. HIVE-C injects descriptor:
   AXIS_TX_TDATA = descriptor[127:0]  (beat 0)
   AXIS_TX_TDATA = descriptor[255:128] (beat 1)
   AXIS_TX_TUSER = PKT_DESC (2'b01)
   AXIS_TX_TLAST = 1

3. DELTA routes to RAPIDS (based on TUSER)

4. RAPIDS receives descriptor:
   - Validates TUSER == PKT_DESC ✓
   - Queues in descriptor FIFO
   - Scheduler selects based on priority

5. MM2S engine executes:
   - Issues AXI4 reads: addr=0x1000_0000, len=32 beats
   - Receives data from DDR
   - Formats AXIS packets with TUSER=PKT_DATA
   - Sets TDEST=5 (tile ID from descriptor)
   - Transmits to DELTA network

6. DELTA routes PKT_DATA to tile 5

7. Tile 5 receives and processes

8. On completion:
   - RAPIDS asserts IRQ[vector]
   - HIVE-C fetches next descriptor
```

### 9.2 Invalid Packet Rejection

```
Scenario: Compute tile accidentally sends PKT_CONFIG to RAPIDS

1. Tile sends packet with TUSER=PKT_CONFIG (2'b10)

2. RAPIDS S2MM input receives:
   if (axis_in_tuser != PKT_DATA) {
     axis_in_tready = 0;  // Reject
     error_flags[INVALID_PKT] = 1;
     irq_pending[INVALID_PKT] = 1;
   }

3. HIVE-C receives interrupt:
   - Reads error flags
   - Identifies source tile (from debug trace)
   - Logs error event
   - Continues operation (non-fatal)
```

### 9.3 Multi-Channel S2MM Example

```
Scenario: Three tiles (3, 7, 12) compute in parallel, all send results

1. HIVE-C pre-programs S2MM descriptors:
   
   Channel 3 descriptor:
   - dst_addr = 0x2000_0000
   - source_tile_id = 3
   - length = 0x800
   
   Channel 7 descriptor:
   - dst_addr = 0x2000_1000
   - source_tile_id = 7
   - length = 0x800
   
   Channel 12 descriptor:
   - dst_addr = 0x2000_2000
   - source_tile_id = 12
   - length = 0x800

2. All three tiles send results simultaneously:
   
   Tile 3 → RAPIDS: TID=3, TDEST=16
   Tile 7 → RAPIDS: TID=7, TDEST=16
   Tile 12 → RAPIDS: TID=12, TDEST=16

3. RAPIDS S2MM channel router:
   
   if (axis_in_tuser == PKT_DATA && axis_in_tdest == 16) {
     channel_id = axis_in_tid[3:0];
     route_to_channel(channel_id);
   }
   
   Result:
   - TID=3 packet → Channel 3 → writes to 0x2000_0000
   - TID=7 packet → Channel 7 → writes to 0x2000_1000
   - TID=12 packet → Channel 12 → writes to 0x2000_2000

4. All three AXI4 writes proceed concurrently (arbiter handles conflicts)

5. Three completion interrupts generated (IRQ[3], IRQ[7], IRQ[12])

6. HIVE-C receives all three interrupts, verifies completions
```

**Benefits of Multi-Channel Architecture:**
- **Parallelism:** Multiple tiles writing simultaneously
- **Isolation:** Each tile's data cannot interfere with others
- **Simplicity:** Direct TID→Channel mapping (no lookup table)
- **Performance:** No head-of-line blocking between tiles

---

## 10. Performance Characteristics

### 10.1 Throughput Analysis

**Theoretical Maximum:**
- 128-bit AXIS @ 100 MHz = 1.6 GB/s
- 128-bit AXI4 @ 100 MHz = 1.6 GB/s
- Matched for zero buffering overhead

**Practical Sustained:**
- DDR latency reduces efficiency: ~80-85%
- Sustained: 1.3-1.4 GB/s
- Burst efficiency: 90%+ for large transfers (>1 KB)

### 10.2 Latency Breakdown

**Descriptor Injection:**
- HIVE-C to RAPIDS: 10-20 cycles (via DELTA)
- Descriptor parsing: 2 cycles
- Scheduling decision: 1 cycle
- **Total: 13-23 cycles (vs 100+ for memory-mapped polling)**

**Data Transfer:**
- AXI4 read latency: 40-60 cycles (DDR2), 20-30 cycles (DDR3)
- FIFO buffering: 2-4 cycles
- AXIS transmission: 1 cycle per beat
- **End-to-end: 43-65 cycles for first data**

### 10.3 Resource Utilization (Artix-7 100T)

| Component | LUTs | FFs | BRAM | DSPs |
|-----------|------|-----|------|------|
| Descriptor Engine | 2,000 | 1,200 | 8 | 0 |
| MM2S Engine (single channel) | 2,400 | 1,600 | 16 | 0 |
| S2MM Engine (16 channels) | 12,800 | 9,600 | 64 | 0 |
| AXI4 Master Interface | 2,200 | 1,400 | 0 | 0 |
| AXIS Interfaces (desc + data) | 1,200 | 800 | 16 | 0 |
| Control/Status Registers | 800 | 500 | 4 | 0 |
| Channel Router & Arbitration | 1,600 | 900 | 0 | 0 |
| **Total RAPIDS** | **23,000** | **16,000** | **108** | **0** |

**Note:** S2MM multi-channel is the dominant resource consumer:
- 16 channels × ~800 LUTs/channel = 12,800 LUTs
- Each channel has independent FIFO (32 entries × 128 bits = 4 BRAM)
- Shared AXI4 write arbiter across channels

**Optimization Options:**
1. Reduce channels for smaller meshes (e.g., 4 channels for 2×2 mesh)
2. Share FIFOs with time-multiplexing (trades latency for area)
3. Reduce per-channel FIFO depth (32 → 16 entries saves 2 BRAM/channel)

---

## 11. Integration with DELTA and HIVE

### 11.1 Packet Flow Summary

```
HIVE-C (generates)         → PKT_DESC  → RAPIDS (receives)
RAPIDS (generates)         → PKT_DATA  → Compute Tiles (receive)
Compute Tiles (generate)   → PKT_DATA  → RAPIDS (receives)
SERV Monitors (generate)   → PKT_CONFIG → Tile Routers (receive)
SERV Monitors (generate)   → PKT_STATUS → HIVE-C (receives)

RAPIDS NEVER generates: PKT_DESC, PKT_CONFIG, PKT_STATUS
RAPIDS NEVER accepts:   PKT_CONFIG, PKT_STATUS on data inputs
```

### 11.2 System-Level View

```
          HIVE Control Plane
          ┌─────────────────┐
          │    HIVE-C       │
          │  (VexRiscv)     │
          └────┬────────┬───┘
               │        │
          PKT_DESC   AXI4-Lite
               │     (status)
               ▼        ▼
          ┌────────────────┐
     ┌───►│    RAPIDS      │◄───┐ AXI4 (DDR)
     │    │    DMA         │    │
     │    └────┬──────┬────┘    │
     │         │      │         │
     │    PKT_DATA  PKT_DATA    │
     │         │      │         │
     │         ▼      ▼         │
     │    ┌────────────────┐    │
     └────┤ DELTA Network  ├────┘
          │  (4×4 Mesh)    │
          └────────────────┘
                  │
            PKT_DATA only
                  ▼
          [Compute Tiles 0-15]
```

---

## 12. Educational Value

### 12.1 Learning Objectives

Students working with RAPIDS learn:

1. **DMA Architecture:** Descriptor-based vs. register-programmed
2. **Packet Filtering:** Hardware enforcement of protocol rules
3. **Flow Control:** Backpressure propagation across interfaces
4. **Scheduling:** Priority-based resource allocation
5. **Performance:** Latency vs. throughput tradeoffs

### 12.2 Experimentation Opportunities

**Modify descriptor scheduler:**
```systemverilog
// Change from priority-based to round-robin
// File: rapids_scheduler.sv
parameter SCHEDULER_TYPE = "PRIORITY"; // or "ROUND_ROBIN", "EDF"
```

**Adjust FIFO depths:**
```systemverilog
// Trade area for performance
parameter DESC_FIFO_DEPTH = 8;   // Increase for more buffering
parameter DATA_FIFO_DEPTH = 512; // Decrease to save BRAM
```

**Add custom packet types:**
```systemverilog
// Extend TUSER encoding (educational only)
typedef enum logic [2:0] {
  PKT_DATA = 3'b000,
  PKT_DESC = 3'b001,
  PKT_CONFIG = 3'b010,
  PKT_STATUS = 3'b011,
  PKT_CUSTOM1 = 3'b100  // Student addition
} pkt_type_t;
```

---

## 13. Verification and Testing

### 13.1 Unit Tests (Cocotb)

```python
@cocotb.test()
async def test_descriptor_rejection(dut):
    """Verify RAPIDS rejects non-DESC packets on descriptor input"""
    
    # Send packet with wrong TUSER
    dut.s_axis_desc_tdata.value = 0xDEADBEEF
    dut.s_axis_desc_tuser.value = 0b00  # PKT_DATA (wrong!)
    dut.s_axis_desc_tvalid.value = 1
    
    await RisingEdge(dut.clk)
    
    # Should reject
    assert dut.s_axis_desc_tready.value == 0
    assert dut.error_invalid_type.value == 1
```

### 13.2 System Tests

```python
@cocotb.test()
async def test_end_to_end_transfer(dut):
    """Full flow: HIVE-C descriptor → RAPIDS → DDR → DELTA"""
    
    # 1. Inject descriptor from HIVE-C
    await inject_descriptor(dut, src=0x1000, len=256, tile=5)
    
    # 2. Verify AXI4 read transactions
    axi_monitor = AxiReadMonitor(dut.m_axi)
    reads = await axi_monitor.wait_for_burst()
    assert reads.addr == 0x1000
    
    # 3. Verify AXIS output with correct packet type
    axis_monitor = AxisMonitor(dut.m_axis_data)
    packets = await axis_monitor.receive_packet()
    assert packets.tuser == 0b00  # PKT_DATA
    assert packets.tdest == 5
```

---

## Appendix A: Error Codes

| Code | Name | Description | Recovery |
|------|------|-------------|----------|
| 0x01 | ERR_INVALID_DESC_TYPE | Received non-DESC packet on descriptor input | Ignore packet |
| 0x02 | ERR_INVALID_DATA_TYPE | Received non-DATA packet on data input | Ignore packet |
| 0x04 | ERR_DESC_FIFO_FULL | Descriptor queue overflow | Backpressure source |
| 0x08 | ERR_AXI_READ | AXI4 read transaction error | Retry or skip |
| 0x10 | ERR_AXI_WRITE | AXI4 write transaction error | Retry or skip |
| 0x20 | ERR_MALFORMED_DESC | Descriptor parsing failed | Skip descriptor |
| 0x40 | ERR_ALIGNMENT | Address not cache-line aligned | Auto-align or error |

---

**Document Version:** 0.3 (Early Draft - Proof of Concept)  
**Last Updated:** 2025-10-18  
**Status:** Preliminary specification, subject to significant change  
**Maintained By:** RAPIDS Development Team