# 3.1 AXI4 Signal Reference

This chapter provides a comprehensive reference for all AXI4 signals used in the bridge crossbar, including timing requirements, protocol rules, and common issues.

## 3.1.1 Overview

The AXI4 protocol consists of five independent channels:
- **Write Address (AW)** - Master initiates write transaction
- **Write Data (W)** - Master provides write data
- **Write Response (B)** - Slave acknowledges write completion
- **Read Address (AR)** - Master initiates read transaction
- **Read Data (R)** - Slave returns read data

Each channel uses a **valid/ready** handshake mechanism for flow control.

## 3.1.2 Clock and Reset

### Global Signals

```systemverilog
input  logic aclk;      // AXI4 clock - all signals sampled on rising edge
input  logic aresetn;   // AXI4 reset - active low, asynchronous assert, synchronous deassert
```

**Reset Behavior:**
- When `aresetn` is LOW, all interfaces are held in reset
- All `VALID` signals must be driven LOW during reset
- `READY` signals may be driven LOW or held at any value during reset
- After `aresetn` goes HIGH, normal operation begins on the next rising clock edge

**Timing Requirements:**
- Setup time: All AXI4 signals must be stable before rising edge of `aclk`
- Hold time: All AXI4 signals must remain stable after rising edge of `aclk`
- Reset assertion: `aresetn` can be asserted asynchronously
- Reset deassertion: `aresetn` must be deasserted synchronously (stable before rising edge)

## 3.1.3 Write Address Channel (AW)

### Purpose
The Write Address channel carries all information required to describe a write transaction, except the data itself.

### Signals

```systemverilog
// Write Address Channel (Master → Slave)
output logic                     awvalid;   // Write address valid
input  logic                     awready;   // Write address ready
output logic [ID_WIDTH-1:0]      awid;      // Write address ID
output logic [ADDR_WIDTH-1:0]    awaddr;    // Write address
output logic [7:0]               awlen;     // Burst length (0-255)
output logic [2:0]               awsize;    // Burst size (2^awsize bytes per beat)
output logic [1:0]               awburst;   // Burst type
output logic                     awlock;    // Lock type
output logic [3:0]               awcache;   // Cache attributes
output logic [2:0]               awprot;    // Protection attributes
output logic [3:0]               awqos;     // Quality of Service
output logic [3:0]               awregion;  // Region identifier
output logic [USER_WIDTH-1:0]    awuser;    // User-defined sideband (optional)
```

### Signal Descriptions

#### awvalid
- **Direction:** Master → Slave
- **Width:** 1 bit
- **Description:** Indicates write address channel signals are valid
- **Protocol Rules:**
  - Master asserts when address phase information is valid
  - Must remain asserted until `awready` is HIGH on rising edge
  - Once asserted, cannot be deasserted until handshake completes
  - Must be LOW during reset

#### awready
- **Direction:** Slave → Master
- **Width:** 1 bit
- **Description:** Indicates slave is ready to accept address
- **Protocol Rules:**
  - Slave asserts when ready to accept address information
  - Can be asserted before, during, or after `awvalid` is asserted
  - Recommended to assert before `awvalid` for zero-wait-state transfers
  - Can toggle freely (no requirement to wait for `awvalid`)

#### awid
- **Direction:** Master → Slave
- **Width:** ID_WIDTH bits (typically 1-16)
- **Description:** Write transaction identifier
- **Protocol Rules:**
  - Uniquely identifies write transactions from a master
  - Transactions with different IDs can complete out-of-order
  - Transactions with same ID must complete in order
  - Bridge may append additional bits for multi-master routing
  - Must remain stable while `awvalid` is asserted

#### awaddr
- **Direction:** Master → Slave
- **Width:** ADDR_WIDTH bits (typically 32 or 64)
- **Description:** Starting address of write burst
- **Protocol Rules:**
  - Byte address of the first beat in the burst
  - Must be aligned to `awsize` (awaddr[awsize-1:0] == 0)
  - Subsequent beat addresses calculated using `awburst` type
  - Must remain stable while `awvalid` is asserted
  - Bridge router uses bits to select target slave

**Alignment Examples:**
```
awsize = 3'b000 (1 byte):  awaddr[  0:0] must be 0 (always aligned)
awsize = 3'b001 (2 bytes): awaddr[  1:0] must be 0
awsize = 3'b010 (4 bytes): awaddr[  2:0] must be 0
awsize = 3'b011 (8 bytes): awaddr[  3:0] must be 0
awsize = 3'b100 (16 bytes): awaddr[  4:0] must be 0
```

#### awlen
- **Direction:** Master → Slave
- **Width:** 8 bits
- **Description:** Number of data beats in burst (actual beats = awlen + 1)
- **Protocol Rules:**
  - Valid range: 0 to 255 (1 to 256 beats)
  - awlen = 0 → 1 beat (single transfer)
  - awlen = 1 → 2 beats
  - awlen = 255 → 256 beats (maximum)
  - Must remain stable while `awvalid` is asserted

**Common Burst Lengths:**
```
awlen = 0   → 1 beat   (single access)
awlen = 1   → 2 beats
awlen = 3   → 4 beats  (common for line fill)
awlen = 7   → 8 beats
awlen = 15  → 16 beats (common for cache line)
```

#### awsize
- **Direction:** Master → Slave
- **Width:** 3 bits
- **Description:** Size of each beat in bytes (2^awsize)
- **Protocol Rules:**
  - Valid range: 0 to log2(DATA_WIDTH/8)
  - Cannot exceed data bus width
  - All beats in burst use same size
  - Must remain stable while `awvalid` is asserted

**Size Encoding:**
```
awsize = 3'b000 → 1 byte     (2^0)
awsize = 3'b001 → 2 bytes    (2^1)
awsize = 3'b010 → 4 bytes    (2^2)
awsize = 3'b011 → 8 bytes    (2^3)
awsize = 3'b100 → 16 bytes   (2^4)
awsize = 3'b101 → 32 bytes   (2^5)
awsize = 3'b110 → 64 bytes   (2^6)
awsize = 3'b111 → 128 bytes  (2^7)
```

**Data Width Constraints:**
```
32-bit bus:  awsize ≤ 3'b010 (max 4 bytes)
64-bit bus:  awsize ≤ 3'b011 (max 8 bytes)
128-bit bus: awsize ≤ 3'b100 (max 16 bytes)
256-bit bus: awsize ≤ 3'b101 (max 32 bytes)
```

#### awburst
- **Direction:** Master → Slave
- **Width:** 2 bits
- **Description:** Burst type - how addresses increment
- **Protocol Rules:**
  - Controls address calculation for multi-beat bursts
  - Must remain stable while `awvalid` is asserted

**Burst Type Encoding:**
```
awburst = 2'b00 (FIXED):      Address stays constant for all beats
                              Used for FIFO access
                              
awburst = 2'b01 (INCR):       Address increments by awsize each beat
                              Most common burst type
                              No boundary restrictions
                              
awburst = 2'b10 (WRAP):       Address increments then wraps at boundary
                              Boundary = awsize × (awlen+1)
                              Used for cache line access
                              Burst length must be 2, 4, 8, or 16
                              
awburst = 2'b11 (RESERVED):   Not used in AXI4
```

**Address Calculation Examples:**

*INCR Burst (awburst=01):*
```
awaddr = 0x1000, awsize = 2 (4 bytes), awlen = 3 (4 beats)
Beat 0: 0x1000
Beat 1: 0x1004
Beat 2: 0x1008
Beat 3: 0x100C
```

*WRAP Burst (awburst=10):*
```
awaddr = 0x100C, awsize = 2 (4 bytes), awlen = 3 (4 beats)
Boundary = 4 × 4 = 16 bytes (wraps at 0x1010)
Beat 0: 0x100C
Beat 1: 0x1010 → wraps to 0x1000
Beat 2: 0x1004
Beat 3: 0x1008
```

#### awlock
- **Direction:** Master → Slave
- **Width:** 1 bit
- **Description:** Atomic access (lock) indicator
- **Protocol Rules:**
  - 0 = Normal access
  - 1 = Exclusive access (atomic operation)
  - Bridge typically does NOT implement lock support (passes through)
  - Must remain stable while `awvalid` is asserted

#### awcache
- **Direction:** Master → Slave
- **Width:** 4 bits
- **Description:** Memory type and cacheable attributes
- **Protocol Rules:**
  - Provides hints about caching behavior
  - Bridge typically passes through unchanged
  - Must remain stable while `awvalid` is asserted

**Cache Encoding (Common Values):**
```
awcache[0] - Bufferable:     Can delay/combine with other writes
awcache[1] - Cacheable:      Can be cached
awcache[2] - Read Allocate:  Read miss allocates cache line
awcache[3] - Write Allocate: Write miss allocates cache line

Common combinations:
4'b0000 - Device Non-bufferable (strict ordering, no caching)
4'b0001 - Device Bufferable (can buffer, no caching)
4'b0011 - Normal Non-cacheable Bufferable
4'b1111 - Write-back Read and Write allocate (full caching)
```

#### awprot
- **Direction:** Master → Slave
- **Width:** 3 bits
- **Description:** Protection attributes
- **Protocol Rules:**
  - Used for security and privilege checking
  - Bridge typically passes through unchanged
  - Must remain stable while `awvalid` is asserted

**Protection Encoding:**
```
awprot[0] - Privileged:  0 = Unprivileged, 1 = Privileged access
awprot[1] - Secure:      0 = Secure, 1 = Non-secure access
awprot[2] - Instruction: 0 = Data access, 1 = Instruction access

Examples:
3'b000 - Unprivileged, Secure, Data
3'b001 - Privileged, Secure, Data
3'b010 - Unprivileged, Non-secure, Data
3'b110 - Unprivileged, Non-secure, Instruction
```

#### awqos
- **Direction:** Master → Slave
- **Width:** 4 bits
- **Description:** Quality of Service identifier
- **Protocol Rules:**
  - Higher value = higher priority (typically)
  - 0 = default/no QoS requirements
  - Bridge arbiter MAY use for priority decisions
  - Must remain stable while `awvalid` is asserted

#### awregion
- **Direction:** Master → Slave
- **Width:** 4 bits
- **Description:** Region identifier (up to 16 regions)
- **Protocol Rules:**
  - Used to access multiple logical address spaces
  - Bridge typically ignores (uses only `awaddr`)
  - Must remain stable while `awvalid` is asserted

#### awuser
- **Direction:** Master → Slave
- **Width:** USER_WIDTH bits (optional, configurable)
- **Description:** User-defined sideband signaling
- **Protocol Rules:**
  - User-defined extension to protocol
  - Bridge may pass through or use for custom features
  - Must remain stable while `awvalid` is asserted
  - Not all designs include this signal

### Handshake Timing

**Single-Cycle Transfer:**
```
        ___     ___     ___     ___
aclk   |   |___|   |___|   |___|   |___
           ___________
awvalid ___|           |_______________
           ___________
awready ___|           |_______________
           ___________
awaddr  XXX| 0x1000   |XXXXXXXXXXXXX
```
Transfer completes when `awvalid && awready` on rising edge.

**Wait States (Master):**
```
        ___     ___     ___     ___     ___
aclk   |   |___|   |___|   |___|   |___|   |___
           _______________________________
awvalid ___|                               |___
                   ___________
awready ___________|           |_______________
           _______________________________
awaddr  XXX| 0x1000                       |XXX
```
Master asserts `awvalid` and waits 2 cycles for `awready`.

**Wait States (Slave):**
```
        ___     ___     ___     ___     ___
aclk   |   |___|   |___|   |___|   |___|   |___
                   _______________________
awvalid ___________|                       |___
           ___________
awready ___|           |_______________________
           ___________
awaddr  XXXXXXXXXXXXX| 0x1000              |XXX
```
Slave asserts `awready` and waits 2 cycles for `awvalid`.

### 4KB Boundary Rule

**Critical AXI4 Rule:** A burst must NOT cross a 4KB address boundary.

**Why 4KB?**
- Page size in most memory management units
- Prevents single burst from spanning multiple pages
- Critical for virtual memory systems

**Checking for Violation:**
```systemverilog
// Calculate burst span
logic [ADDR_WIDTH-1:0] burst_span;
logic [11:0] upper_addr_bits;
logic [11:0] end_addr_bits;

burst_span = (awlen + 1) << awsize;  // Total bytes in burst
upper_addr_bits = awaddr[ADDR_WIDTH-1:12];
end_addr_bits = (awaddr + burst_span - 1) >> 12;

// Violation if page boundary crossed
logic boundary_violation;
assign boundary_violation = (upper_addr_bits != end_addr_bits);
```

**Example Violations:**
```
VALID:
awaddr = 0x0000_0FF0, awlen = 3 (4 beats), awsize = 2 (4 bytes)
End = 0x0000_0FF0 + 16 - 1 = 0x0000_0FFF
Both in page 0x0000_0xxx ✓

INVALID:
awaddr = 0x0000_0FF0, awlen = 7 (8 beats), awsize = 2 (4 bytes)
End = 0x0000_0FF0 + 32 - 1 = 0x0000_100F
Spans pages 0x0000_0xxx and 0x0000_1xxx ✗
```

### Common Issues and Debug

**Issue 1: awvalid dropped before handshake**
```
Symptom: Master deasserts awvalid before awready seen
Check:
- awvalid must stay asserted until awready HIGH
- Master FSM logic
```

**Issue 2: Unaligned address**
```
Symptom: awaddr not aligned to awsize
Check:
- awaddr[awsize-1:0] must be zero
- Master address generation logic
```

**Issue 3: awsize exceeds bus width**
```
Symptom: awsize = 4 (16 bytes) on 64-bit (8-byte) bus
Check:
- awsize must be ≤ log2(DATA_WIDTH/8)
- Master configuration
```

**Issue 4: 4KB boundary violation**
```
Symptom: Burst crosses page boundary
Check:
- Calculate end address: start + (len+1)×size
- Check if upper address bits change
```

**Issue 5: Invalid WRAP burst**
```
Symptom: awburst=WRAP with illegal length
Check:
- WRAP bursts must have len ∈ {1, 3, 7, 15} (2/4/8/16 beats)
- awaddr must be aligned to burst span
```

### Bridge-Specific Behavior

**ID Width Extension:**
```
Bridge may append bits to awid for routing:
  Master awid:  [ID_WIDTH-1:0]
  Bridge awid:  [TOTAL_ID_WIDTH-1:0] = {bridge_id, master_awid}
  
  This allows bridge to route responses back to correct master.
```

**Address Decoding:**
```
Bridge router examines awaddr to select slave:
  if (awaddr >= SLAVE_BASE[i] && awaddr < SLAVE_END[i])
    route to slave i
  else
    generate DECERR response (address decode error)
```

**Arbitration:**
```
When multiple masters request same slave:
  - Bridge arbiter selects one master (round-robin, priority, etc.)
  - Winning master's AW channel connects to slave
  - Losing masters see awready = 0 (backpressure)
```

---

**Related Sections:**
- Section 3.2: Write Data Channel (W)
- Section 3.3: Write Response Channel (B)
- Section 2.1: Master Adapter (ID generation)
- Section 2.2: Slave Router (address decoding)
- Section 2.4: Arbitration

**Next:** [3.2 Write Data Channel (W)](02_write_data.md)
