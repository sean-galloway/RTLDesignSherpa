# 3.4 Read Address Channel (AR)

The Read Address channel carries all information required to describe a read transaction. It is similar to the Write Address channel but initiates read operations instead of writes.

## 3.4.1 Overview

**Key Characteristics:**
- Travels from master to slave (request path)
- Independent of write channels (AW/W/B)
- Can be issued before, during, or after write operations
- Supports bursts (1-256 beats)
- Uses valid/ready handshake

## 3.4.2 Channel Signals

```systemverilog
// Read Address Channel (Master → Slave)
output logic                     arvalid;   // Read address valid
input  logic                     arready;   // Read address ready
output logic [ID_WIDTH-1:0]      arid;      // Read address ID
output logic [ADDR_WIDTH-1:0]    araddr;    // Read address
output logic [7:0]               arlen;     // Burst length (0-255)
output logic [2:0]               arsize;    // Burst size (2^arsize bytes per beat)
output logic [1:0]               arburst;   // Burst type
output logic                     arlock;    // Lock type
output logic [3:0]               arcache;   // Cache attributes
output logic [2:0]               arprot;    // Protection attributes
output logic [3:0]               arqos;     // Quality of Service
output logic [3:0]               arregion;  // Region identifier
output logic [USER_WIDTH-1:0]    aruser;    // User-defined sideband (optional)
```

## 3.4.3 Signal Descriptions

### arvalid
- **Direction:** Master → Slave
- **Width:** 1 bit
- **Description:** Indicates read address channel signals are valid
- **Protocol Rules:**
  - Master asserts when address phase information is valid
  - Must remain asserted until `arready` is HIGH on rising edge
  - Once asserted, cannot be deasserted until handshake completes
  - Must be LOW during reset

### arready
- **Direction:** Slave → Master
- **Width:** 1 bit
- **Description:** Indicates slave is ready to accept address
- **Protocol Rules:**
  - Slave asserts when ready to accept address information
  - Can be asserted before, during, or after `arvalid` is asserted
  - Recommended to assert before `arvalid` for zero-wait-state transfers
  - Can toggle freely (no requirement to wait for `arvalid`)

### arid
- **Direction:** Master → Slave
- **Width:** ID_WIDTH bits (typically 1-16)
- **Description:** Read transaction identifier
- **Protocol Rules:**
  - Uniquely identifies read transactions from a master
  - Transactions with different IDs can complete out-of-order
  - Transactions with same ID must complete in order
  - Bridge may append additional bits for multi-master routing
  - Must remain stable while `arvalid` is asserted
  - R response will carry matching `rid`

**Out-of-Order Reads:**
```
Master issues:
  AR: arid=3, araddr=0x1000
  AR: arid=5, araddr=0x2000

Slave can respond in ANY order:
  R: rid=5 (all beats)  ← Can complete first
  R: rid=3 (all beats)  ← Even though issued first

This allows fast/cached reads to overtake slow reads.
```

### araddr
- **Direction:** Master → Slave
- **Width:** ADDR_WIDTH bits (typically 32 or 64)
- **Description:** Starting address of read burst
- **Protocol Rules:**
  - Byte address of the first beat in the burst
  - Must be aligned to `arsize` (araddr[arsize-1:0] == 0)
  - Subsequent beat addresses calculated using `arburst` type
  - Must remain stable while `arvalid` is asserted
  - Bridge router uses bits to select target slave

**Addressing Examples:**
```
Single word read (32-bit):
  araddr = 0x0000_1000, arsize = 2 (4 bytes), arlen = 0 (1 beat)
  Reads bytes at 0x1000-0x1003

Cache line read (64-byte, 64-bit bus):
  araddr = 0x0000_2000, arsize = 3 (8 bytes), arlen = 7 (8 beats)
  Beat 0: 0x2000-0x2007
  Beat 1: 0x2008-0x200F
  ...
  Beat 7: 0x2038-0x203F
```

### arlen
- **Direction:** Master → Slave
- **Width:** 8 bits
- **Description:** Number of data beats in burst (actual beats = arlen + 1)
- **Protocol Rules:**
  - Valid range: 0 to 255 (1 to 256 beats)
  - arlen = 0 → 1 beat (single transfer)
  - arlen = 15 → 16 beats (common for cache line fill)
  - arlen = 255 → 256 beats (maximum)
  - Must remain stable while `arvalid` is asserted

**Read Burst Lengths:**
```
arlen = 0   → 1 beat   (single read)
arlen = 3   → 4 beats  (small burst)
arlen = 7   → 8 beats  (common)
arlen = 15  → 16 beats (cache line - 64B on 32-bit bus)
arlen = 255 → 256 beats (max, rarely used)
```

### arsize
- **Direction:** Master → Slave
- **Width:** 3 bits
- **Description:** Size of each beat in bytes (2^arsize)
- **Protocol Rules:**
  - Valid range: 0 to log2(DATA_WIDTH/8)
  - Cannot exceed data bus width
  - All beats in burst use same size
  - Must remain stable while `arvalid` is asserted

**Size Encoding:**
```
arsize = 3'b000 → 1 byte     (2^0) - Byte read
arsize = 3'b001 → 2 bytes    (2^1) - Halfword read
arsize = 3'b010 → 4 bytes    (2^2) - Word read
arsize = 3'b011 → 8 bytes    (2^3) - Doubleword read
arsize = 3'b100 → 16 bytes   (2^4)
arsize = 3'b101 → 32 bytes   (2^5)
arsize = 3'b110 → 64 bytes   (2^6)
arsize = 3'b111 → 128 bytes  (2^7)
```

**Bus Width Constraints:**
```
32-bit bus (4 bytes):  arsize ≤ 3'b010 (max 4 bytes)
64-bit bus (8 bytes):  arsize ≤ 3'b011 (max 8 bytes)
128-bit bus (16 bytes): arsize ≤ 3'b100 (max 16 bytes)
256-bit bus (32 bytes): arsize ≤ 3'b101 (max 32 bytes)

Narrow reads (arsize < bus width) are legal and common.
```

### arburst
- **Direction:** Master → Slave
- **Width:** 2 bits
- **Description:** Burst type - how addresses increment
- **Protocol Rules:**
  - Controls address calculation for multi-beat bursts
  - Must remain stable while `arvalid` is asserted

**Burst Type Encoding:**
```
arburst = 2'b00 (FIXED):      Address stays constant for all beats
                              Used for FIFO reads
                              All beats read from same address
                              
arburst = 2'b01 (INCR):       Address increments by arsize each beat
                              Most common burst type for memory
                              No boundary restrictions
                              
arburst = 2'b10 (WRAP):       Address increments then wraps at boundary
                              Boundary = arsize × (arlen+1)
                              Used for cache line wrapping
                              Burst length must be 2, 4, 8, or 16
                              
arburst = 2'b11 (RESERVED):   Not used in AXI4
```

**Read Burst Address Examples:**

*INCR Burst:*
```
araddr = 0x1000, arsize = 2 (4 bytes), arlen = 3, arburst = INCR
Beat 0: Read 0x1000-0x1003
Beat 1: Read 0x1004-0x1007
Beat 2: Read 0x1008-0x100B
Beat 3: Read 0x100C-0x100F
```

*WRAP Burst:*
```
araddr = 0x100C, arsize = 2 (4 bytes), arlen = 3, arburst = WRAP
Wrap boundary = 4 × 4 = 16 bytes (0x1000-0x100F)
Beat 0: Read 0x100C-0x100F
Beat 1: Read 0x1000-0x1003 (wrapped)
Beat 2: Read 0x1004-0x1007
Beat 3: Read 0x1008-0x100B

Useful for circular buffers and cache line wrapping.
```

*FIXED Burst (FIFO):*
```
araddr = 0x2000, arsize = 2 (4 bytes), arlen = 3, arburst = FIXED
Beat 0: Read 0x2000-0x2003
Beat 1: Read 0x2000-0x2003 (same address)
Beat 2: Read 0x2000-0x2003 (same address)
Beat 3: Read 0x2000-0x2003 (same address)

Used for reading from FIFO or stream interface.
```

### arlock, arcache, arprot, arqos, arregion
These signals have identical encoding and behavior to their write channel equivalents (awlock, awcache, etc.). See Section 3.1 for detailed descriptions.

**Quick Reference:**
- **arlock:** Atomic/exclusive access (1 bit)
- **arcache:** Cache attributes (4 bits)
- **arprot:** Protection/privilege attributes (3 bits)
- **arqos:** Quality of Service priority (4 bits)
- **arregion:** Region identifier (4 bits)

### aruser
- **Direction:** Master → Slave
- **Width:** USER_WIDTH bits (optional, configurable)
- **Description:** User-defined sideband signaling
- **Protocol Rules:**
  - User-defined extension to protocol
  - Must remain stable while `arvalid` is asserted
  - Not all designs include this signal

## 3.4.4 Handshake Timing

**Single-Cycle Transfer:**
```
        ___     ___     ___     ___
aclk   |   |___|   |___|   |___|   |___
           ___________
arvalid ___|           |_______________
           ___________
arready ___|           |_______________
           ___________
araddr  XXX| 0x1000   |XXXXXXXXXXXXX
```

**Master Wait States:**
```
        ___     ___     ___     ___     ___
aclk   |   |___|   |___|   |___|   |___|   |___
           _______________________________
arvalid ___|                               |___
                   ___________
arready ___________|           |_______________
           _______________________________
araddr  XXX| 0x1000                       |XXX
```
Master waits 2 cycles for slave to become ready.

**Slave Wait States:**
```
        ___     ___     ___     ___     ___
aclk   |   |___|   |___|   |___|   |___|   |___
                   _______________________
arvalid ___________|                       |___
           ___________
arready ___|           |_______________________
           ___________
araddr  XXXXXXXXXXXXX| 0x1000              |XXX
```
Slave ready early, waits for master to assert arvalid.

## 3.4.5 Read vs Write Channel Differences

### Key Differences from AW Channel

```
                AR Channel              AW Channel
                
Data Beat:      R (from slave)          W (from master)
Response:       R channel carries       Separate B channel
                data AND status         carries only status
                
Completion:     All (arlen+1) R beats   All W beats + 1 B response
                
Interleaving:   R channel CAN           W channel CANNOT
                interleave by ID        interleave
                
Data Flow:      Slave → Master          Master → Slave
```

### Independence from Write Channels

```
AR and AW channels are COMPLETELY independent:
  - Can issue AR and AW in any order
  - Can issue AR while writes are outstanding
  - Can issue AW while reads are outstanding
  - No required ordering between read and write

Example valid sequence:
  Cycle 0: AW (write to 0x1000)
  Cycle 1: AR (read from 0x2000)
  Cycle 2: W (write data)
  Cycle 3: AR (another read)
  Cycle 4: R (read data response)
  Cycle 5: B (write response)
  
  All legal! Reads and writes are independent.
```

## 3.4.6 4KB Boundary Rule

**Critical AXI4 Rule:** A read burst must NOT cross a 4KB address boundary.

**Rationale:**
- Same as writes: prevents crossing page boundaries
- Critical for MMU/virtual memory systems
- 4KB = standard page size

**Checking for Violation:**
```systemverilog
// Calculate whether burst crosses 4KB boundary
logic [ADDR_WIDTH-1:0] start_addr;
logic [ADDR_WIDTH-1:0] end_addr;
logic [ADDR_WIDTH-1:0] burst_bytes;
logic boundary_crossed;

assign start_addr = araddr;
assign burst_bytes = (arlen + 1) << arsize;
assign end_addr = start_addr + burst_bytes - 1;

// Check if upper bits change (crossed 4KB boundary)
assign boundary_crossed = (start_addr[ADDR_WIDTH-1:12] != end_addr[ADDR_WIDTH-1:12]);

// Assert error if boundary crossed
assert property (@(posedge aclk) 
    arvalid && arready |-> !boundary_crossed
) else $error("AR burst crosses 4KB boundary!");
```

**Valid vs Invalid Examples:**
```
VALID:
araddr = 0x1FF0, arlen = 3 (4 beats), arsize = 2 (4 bytes)
End = 0x1FF0 + 16 - 1 = 0x1FFF
Page bits: 0x1 (start) == 0x1 (end) ✓

INVALID:
araddr = 0x1FF0, arlen = 7 (8 beats), arsize = 2 (4 bytes)
End = 0x1FF0 + 32 - 1 = 0x200F
Page bits: 0x1 (start) != 0x2 (end) ✗
```

## 3.4.7 Out-of-Order Read Completion

### Why Out-of-Order?

```
Different arid values can complete out of order:
  - Slave can prioritize cached reads over uncached
  - Fast memories respond before slow memories
  - Improves average latency
  - Increases throughput

Example:
  Cycle 0: AR (arid=1, addr in slow memory)
  Cycle 1: AR (arid=2, addr in fast cache)
  Cycle 5: R (rid=2) - cache hit, responds first
  Cycle 20: R (rid=1) - slow memory, responds later
```

### Same ID Ordering Requirement

```
Same arid MUST complete in order:
  
LEGAL:
  AR: arid=5, addr=0x1000
  AR: arid=5, addr=0x2000
  R:  rid=5 (for 0x1000) ← First
  R:  rid=5 (for 0x2000) ← Second, in order

ILLEGAL:
  AR: arid=5, addr=0x1000 (transaction A)
  AR: arid=5, addr=0x2000 (transaction B)
  R:  rid=5 (for 0x2000) ← Transaction B first
  R:  rid=5 (for 0x1000) ← Transaction A second
  ^^^
  VIOLATION! Same ID reordered
```

### Master ID Management Strategy

```
Strategy: Use different arid for independent reads
  - Read A doesn't depend on Read B → use different IDs
  - Read B depends on Read A result → use same ID
  
Example - Independent:
  Read configuration register: arid=0
  Read data buffer: arid=1
  → Can complete out of order

Example - Dependent:
  Read pointer: arid=5
  Read data at pointer: arid=5
  → Must complete in order
```

## 3.4.8 Bridge-Specific AR Channel Behavior

### Address Decoding

```
Bridge router examines araddr to select slave:

if (araddr >= SLAVE0_BASE && araddr < SLAVE0_END)
    route to Slave 0
else if (araddr >= SLAVE1_BASE && araddr < SLAVE1_END)
    route to Slave 1
...
else
    generate DECERR response (out of range)
```

### ID Extension

```
Bridge extends arid for response routing:

Master sends:
  arid = [ID_WIDTH-1:0] = 4'b0101

Bridge extends to:
  arid_extended = {bridge_id, master_id}
  arid_extended = {2'b00, 4'b0101} = 6'b00_0101
                   ^^^^ ^^^^
                   Bridge Master
                   
This allows R responses to route back to correct master.
```

### AR Channel Arbitration

```
Multiple masters request same slave simultaneously:

Step 1: Bridge arbiter selects one master
        - Round-robin, fixed priority, or QoS-based
        - Uses arqos for priority hints
        
Step 2: Winning master's AR connects to slave
        
Step 3: Losing masters see arready=0 (backpressure)
        
Step 4: After AR transfer completes, arbitrate again
```

### Outstanding Read Tracking

```
Bridge tracks outstanding reads per master:
  - Increment when AR transfers
  - Decrement when R completes (rlast seen)
  - Limit to prevent resource exhaustion
  
If outstanding limit reached:
  - arready = 0 to that master
  - Wait for R responses to complete
  - Then allow more AR
```

## 3.4.9 Common Issues and Debug

### Issue 1: arvalid Dropped Before Handshake

```
Symptom: AR transaction lost
Cause: Master deasserts arvalid before arready seen
Check:
  - arvalid must stay HIGH until (arvalid && arready)
  - Master FSM must hold arvalid
  - Protocol violation if dropped early
```

### Issue 2: Unaligned Address

```
Symptom: Unexpected rresp=SLVERR or DECERR
Cause: araddr not aligned to arsize
Check:
  - araddr[arsize-1:0] must == 0
  - Example: arsize=2 (4 bytes) → araddr[1:0] must be 00
  - Slave may return error for unaligned reads
```

### Issue 3: arsize Exceeds Bus Width

```
Symptom: Protocol violation, undefined behavior
Cause: arsize > log2(DATA_WIDTH/8)
Check:
  - 32-bit bus: arsize ≤ 2
  - 64-bit bus: arsize ≤ 3
  - 128-bit bus: arsize ≤ 4
  - Master configuration error
```

### Issue 4: 4KB Boundary Violation

```
Symptom: Slave returns error or hangs
Cause: Burst crosses page boundary
Check:
  - Calculate: end_addr = araddr + (arlen+1)×(2^arsize) - 1
  - Check: araddr[ADDR_WIDTH-1:12] == end_addr[ADDR_WIDTH-1:12]
  - If different, burst crosses 4KB boundary
```

### Issue 5: No R Response

```
Symptom: AR transfers but R never comes
Cause:
  - Slave hung or stuck
  - R channel disconnected
  - Bridge routing error
  - Out-of-range address (should get DECERR)
  
Debug:
  - Check slave status
  - Check bridge ID routing
  - Verify address is in valid range
  - Implement timeout mechanism
```

## 3.4.10 Performance Considerations

### Latency

```
Read Latency = Time from AR to first R beat

Components:
  1. AR to slave (bridge routing delay)
  2. Slave memory access
  3. R back to master (bridge routing delay)
  
Typical values:
  - On-chip SRAM: 2-5 cycles
  - On-chip register: 1-2 cycles
  - Off-chip DDR: 20-100+ cycles
  - Cache hit: 1-3 cycles
  - Cache miss: 20-50+ cycles
```

### Throughput

```
Maximum read throughput:
  - Issue AR every cycle
  - Slave returns R data every cycle
  - Use different arid for each to allow out-of-order
  - Limited by:
    * Outstanding transaction limit
    * Slave bandwidth
    * Bridge arbitration
```

### Speculative Reads

```
Masters can speculatively issue AR:
  - Issue AR before knowing if data needed
  - Cancel by not accepting R data (rready=0 forever)
  - Or discard R data when received
  
Prefetching:
  - Issue AR for next cache line before current done
  - Reduces average latency
  - Requires sufficient outstanding capacity
```

---

**Related Sections:**
- Section 3.1: Write Address Channel (AW)
- Section 3.5: Read Data Channel (R)
- Section 2.2: Slave Router (address decoding)
- Section 2.4: Arbitration
- Section 2.5: ID Management

**Next:** [3.5 Read Data and Response Channel (R)](05_read_data.md)
