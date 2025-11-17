# 3.2 Write Data Channel (W)

The Write Data channel carries the actual write data from master to slave. Unlike the Write Address channel, the W channel does NOT carry an ID, so the bridge must maintain ordering between AW and W channels.

## 3.2.1 Overview

**Key Characteristics:**
- Carries write data beats for a write transaction
- No ID field (unlike other channels)
- Must follow AW channel in order for same transaction
- Can be interleaved with W beats from other transactions (different AWIDs)
- Uses valid/ready handshake per beat

## 3.2.2 Channel Signals

```systemverilog
// Write Data Channel (Master → Slave)
output logic                     wvalid;    // Write data valid
input  logic                     wready;    // Write data ready
output logic [DATA_WIDTH-1:0]    wdata;     // Write data
output logic [STRB_WIDTH-1:0]    wstrb;     // Write strobes (byte enables)
output logic                     wlast;     // Last beat of burst
output logic [USER_WIDTH-1:0]    wuser;     // User-defined sideband (optional)
```

Where:
```
STRB_WIDTH = DATA_WIDTH / 8  (one strobe bit per byte)
```

## 3.2.3 Signal Descriptions

### wvalid
- **Direction:** Master → Slave
- **Width:** 1 bit
- **Description:** Indicates write data and strobes are valid
- **Protocol Rules:**
  - Master asserts when W channel information is valid
  - Must remain asserted until `wready` is HIGH on rising edge
  - Once asserted, cannot be deasserted until handshake completes
  - Must be LOW during reset
  - Multiple W beats can be pipelined (different transactions)

### wready
- **Direction:** Slave → Master
- **Width:** 1 bit
- **Description:** Indicates slave is ready to accept write data
- **Protocol Rules:**
  - Slave asserts when ready to accept data
  - Can toggle freely (no dependency on `wvalid`)
  - Recommended to assert early for throughput
  - Can be LOW during reset or backpressure

### wdata
- **Direction:** Master → Slave
- **Width:** DATA_WIDTH bits (typically 32, 64, 128, 256, 512, or 1024)
- **Description:** Write data for current beat
- **Protocol Rules:**
  - Contains data to be written for this beat
  - Only bytes with corresponding `wstrb` bit set are written
  - Bytes with `wstrb=0` can be any value (don't care)
  - Must remain stable while `wvalid` is asserted
  - Byte order: Little-endian within the bus width

**Data Bus Layout (64-bit example):**
```
wdata[63:56] - Byte 7  (highest address)
wdata[55:48] - Byte 6
wdata[47:40] - Byte 5
wdata[39:32] - Byte 4
wdata[31:24] - Byte 3
wdata[23:16] - Byte 2
wdata[15: 8] - Byte 1
wdata[ 7: 0] - Byte 0  (lowest address)
```

### wstrb
- **Direction:** Master → Slave
- **Width:** STRB_WIDTH bits = DATA_WIDTH/8 (one bit per data byte)
- **Description:** Byte-level write enables
- **Protocol Rules:**
  - Each bit enables writing of corresponding data byte
  - `wstrb[n] = 1`: Write `wdata[8n+7:8n]`
  - `wstrb[n] = 0`: Do NOT write `wdata[8n+7:8n]` (leave memory unchanged)
  - Must remain stable while `wvalid` is asserted
  - For narrow transfers (awsize < bus width), only relevant strobes are set

**Strobe Examples (64-bit bus):**
```
wstrb = 8'b1111_1111  - Write all 8 bytes (full 64-bit write)
wstrb = 8'b0000_1111  - Write bytes 0-3 only (lower 32 bits)
wstrb = 8'b1111_0000  - Write bytes 4-7 only (upper 32 bits)
wstrb = 8'b0000_0001  - Write byte 0 only (8-bit write to lowest address)
wstrb = 8'b1010_1010  - Write alternating bytes (0, 2, 4, 6)
```

**Strobe Patterns Based on awsize:**

For a 64-bit bus (8 bytes), different `awsize` values generate different strobe patterns:

```
awsize = 3'b000 (1 byte):
  awaddr[2:0] = 0 → wstrb = 8'b0000_0001
  awaddr[2:0] = 1 → wstrb = 8'b0000_0010
  awaddr[2:0] = 2 → wstrb = 8'b0000_0100
  ...
  awaddr[2:0] = 7 → wstrb = 8'b1000_0000

awsize = 3'b001 (2 bytes):
  awaddr[2:1] = 0 → wstrb = 8'b0000_0011
  awaddr[2:1] = 1 → wstrb = 8'b0000_1100
  awaddr[2:1] = 2 → wstrb = 8'b0011_0000
  awaddr[2:1] = 3 → wstrb = 8'b1100_0000

awsize = 3'b010 (4 bytes):
  awaddr[2] = 0 → wstrb = 8'b0000_1111
  awaddr[2] = 1 → wstrb = 8'b1111_0000

awsize = 3'b011 (8 bytes):
  wstrb = 8'b1111_1111  (all bytes)
```

### wlast
- **Direction:** Master → Slave
- **Width:** 1 bit
- **Description:** Indicates last data beat in write burst
- **Protocol Rules:**
  - Asserted on final W beat of transaction
  - Beat count must match `awlen + 1` from corresponding AW
  - Only ONE W beat in a burst has `wlast=1`
  - Must remain stable while `wvalid` is asserted
  - Critical for burst boundary detection

**wlast Timing:**
```
Transaction with awlen=3 (4 beats total):

Beat 0: wvalid=1, wlast=0  → First beat
Beat 1: wvalid=1, wlast=0  → Middle beat
Beat 2: wvalid=1, wlast=0  → Middle beat  
Beat 3: wvalid=1, wlast=1  → LAST beat (triggers B response)

Single beat (awlen=0):
Beat 0: wvalid=1, wlast=1  → First AND last
```

### wuser
- **Direction:** Master → Slave
- **Width:** USER_WIDTH bits (optional, configurable)
- **Description:** User-defined sideband signaling
- **Protocol Rules:**
  - User-defined extension to protocol
  - Bridge may pass through or use for custom features
  - Must remain stable while `wvalid` is asserted
  - Not all designs include this signal

## 3.2.4 Handshake Timing

**Single Beat Transfer:**
```
        ___     ___     ___     ___
aclk   |   |___|   |___|   |___|   |___
           ___________
wvalid  ___|           |_______________
           ___________
wready  ___|           |_______________
           ___________
wdata   XXX| 0xABCD   |XXXXXXXXXXXXX
           ___________
wstrb   XXX|   0xF    |XXXXXXXXXXXXX
           ___________
wlast   ___|     1     |_______________
```

**Burst Transfer (4 Beats):**
```
        ___     ___     ___     ___     ___     ___
aclk   |   |___|   |___|   |___|   |___|   |___|   |___
           ___________________________________________
wvalid  ___|                                           |___
           ___________________________________________
wready  ___|                                           |___
           _____   _____   _____   _____
wdata   XXX|_D0_|X|_D1_|X|_D2_|X|_D3_|XXXXXXXXXXXXX
           ___________________________________________
wstrb   XXX|              0xF                         |XXX
           _______________________________     _______
wlast   ___|                               |___|       |___
                                          ^^^
                                   wlast=1 on beat 3
```

**Back Pressure (wready=0):**
```
        ___     ___     ___     ___     ___     ___
aclk   |   |___|   |___|   |___|   |___|   |___|   |___
           ___________________________________________
wvalid  ___|                                           |___
           ___________                 _______________
wready  ___|           |_______________|               |___
           _____                       _____
wdata   XXX|_D0_|XXXXXXXXXXXXXXXXXXX|_D1_|XXXXXXXXXXXXX
           
Beat 0 transferred cycle 1
Beat 1 stalled cycles 2-4 (wready=0)
Beat 1 transferred cycle 5
```

## 3.2.5 Relationship to AW Channel

**Critical Rule:** W channel data must correspond to AW channel addresses in order.

### AW-W Ordering

```
Master sends:
1. AW transaction (awid=5, awlen=3)  → 4 W beats required
2. W beats (4 beats total)
3. AW transaction (awid=7, awlen=1)  → 2 W beats required
4. W beats (2 beats total)

The W beats MUST match AW transactions in FIFO order:
  First 4 W beats → awid=5 transaction
  Next 2 W beats  → awid=7 transaction
```

### W Interleaving (AXI4 Does NOT Allow)

**IMPORTANT:** AXI4 does **NOT** allow W channel interleaving.

```
ILLEGAL in AXI4:
AW: awid=5, awlen=3  (needs 4 W beats)
AW: awid=7, awlen=1  (needs 2 W beats)
W:  beat for awid=5
W:  beat for awid=7  ← ILLEGAL! Must finish awid=5 first
W:  beat for awid=5
...

LEGAL in AXI4:
AW: awid=5, awlen=3
AW: awid=7, awlen=1
W:  beat 0 for awid=5
W:  beat 1 for awid=5
W:  beat 2 for awid=5
W:  beat 3 for awid=5  (wlast=1)
W:  beat 0 for awid=7
W:  beat 1 for awid=7  (wlast=1)
```

**Why No Interleaving?**
- W channel has no ID field
- Slave must match W beats to AW in order
- Simplifies slave implementation
- Note: AW channel CAN interleave (different AWIDs can go out of order)

### Bridge W Channel Behavior

```
Bridge must maintain ALL master's W channel ordering:
- Cannot interleave W from different masters
- Must serialize W channels from multiple masters
- Arbiter grants AW, then W must follow
- Next master's W cannot start until previous W completes (wlast seen)

Example Timeline:
Cycle 0: Master0 AW granted  (awid=M0_5, awlen=1)
Cycle 1: Master0 W beat 0
Cycle 2: Master0 W beat 1 (wlast=1)
Cycle 3: Master1 AW granted  (awid=M1_3, awlen=0)
Cycle 4: Master1 W beat 0 (wlast=1)
         ^^^
         Master1 W cannot start before Master0 wlast
```

## 3.2.6 Burst Length Matching

**Rule:** Number of W beats must match `awlen + 1` from corresponding AW.

### Verification Check

```systemverilog
// Track W beat count per AW transaction
logic [7:0] expected_w_beats;  // From awlen + 1
logic [7:0] actual_w_beats;    // Counter

always_ff @(posedge aclk) begin
    if (!aresetn) begin
        expected_w_beats <= 0;
        actual_w_beats <= 0;
    end else begin
        // Capture expected count when AW transfers
        if (awvalid && awready) begin
            expected_w_beats <= awlen + 1;
            actual_w_beats <= 0;
        end
        
        // Count W beats
        if (wvalid && wready) begin
            actual_w_beats <= actual_w_beats + 1;
            
            // Check on last beat
            if (wlast) begin
                assert(actual_w_beats + 1 == expected_w_beats)
                    else $error("W beat count mismatch!");
            end
        end
    end
end
```

### Common Errors

**Error 1: Too few W beats**
```
awlen = 3  (expect 4 beats)
W: beat 0
W: beat 1
W: beat 2 (wlast=1)  ← ERROR! wlast asserted after only 3 beats
```

**Error 2: Too many W beats**
```
awlen = 1  (expect 2 beats)
W: beat 0
W: beat 1 (wlast=1)
W: beat 2  ← ERROR! Extra beat after wlast
```

**Error 3: wlast missing**
```
awlen = 2  (expect 3 beats)
W: beat 0 (wlast=0)
W: beat 1 (wlast=0)
W: beat 2 (wlast=0)  ← ERROR! wlast never asserted
```

## 3.2.7 Data Width Conversion

When masters and slaves have different data widths, the bridge may insert width converters.

### Upsizing (Narrow Master → Wide Slave)

**Example: 32-bit master writing to 64-bit slave**

Master sends:
```
awaddr = 0x1000, awsize = 2 (4 bytes), awlen = 3 (4 beats)
W beat 0: wdata[31:0] = 0xAAAA_AAAA, wstrb = 4'b1111
W beat 1: wdata[31:0] = 0xBBBB_BBBB, wstrb = 4'b1111
W beat 2: wdata[31:0] = 0xCCCC_CCCC, wstrb = 4'b1111
W beat 3: wdata[31:0] = 0xDDDD_DDDD, wstrb = 4'b1111
```

Converter packs → Slave sees:
```
awaddr = 0x1000, awsize = 3 (8 bytes), awlen = 1 (2 beats)
W beat 0: wdata[63:0] = 0xBBBB_BBBB_AAAA_AAAA, wstrb = 8'b1111_1111
W beat 1: wdata[63:0] = 0xDDDD_DDDD_CCCC_CCCC, wstrb = 8'b1111_1111
```

### Downsizing (Wide Master → Narrow Slave)

**Example: 64-bit master writing to 32-bit slave**

Master sends:
```
awaddr = 0x1000, awsize = 3 (8 bytes), awlen = 1 (2 beats)
W beat 0: wdata[63:0] = 0xBBBB_BBBB_AAAA_AAAA, wstrb = 8'b1111_1111
W beat 1: wdata[63:0] = 0xDDDD_DDDD_CCCC_CCCC, wstrb = 8'b1111_1111
```

Converter splits → Slave sees:
```
awaddr = 0x1000, awsize = 2 (4 bytes), awlen = 3 (4 beats)
W beat 0: wdata[31:0] = 0xAAAA_AAAA, wstrb = 4'b1111
W beat 1: wdata[31:0] = 0xBBBB_BBBB, wstrb = 4'b1111
W beat 2: wdata[31:0] = 0xCCCC_CCCC, wstrb = 4'b1111
W beat 3: wdata[31:0] = 0xDDDD_DDDD, wstrb = 4'b1111
```

**See Section 2.6 for full width conversion details.**

## 3.2.8 Write Strobes and Partial Writes

### Strobe Calculation

Based on `awaddr`, `awsize`, and `awlen`, calculate which bytes are written:

```systemverilog
function automatic logic [STRB_WIDTH-1:0] calc_wstrb(
    input logic [ADDR_WIDTH-1:0] addr,
    input logic [2:0] size,
    input int beat_number
);
    logic [ADDR_WIDTH-1:0] beat_addr;
    logic [STRB_WIDTH-1:0] strb;
    int byte_offset;
    int num_bytes;
    
    // Calculate address for this beat
    beat_addr = addr + (beat_number << size);
    
    // Number of bytes in transfer
    num_bytes = 1 << size;
    
    // Byte offset within data bus
    byte_offset = beat_addr % STRB_WIDTH;
    
    // Generate strobe
    strb = ((1 << num_bytes) - 1) << byte_offset;
    
    return strb;
endfunction
```

### Sparse Writes

Strobes allow byte-granular writes:

```
Write 0xAB to address 0x1002 on a 32-bit bus:

awaddr = 0x1000 (aligned to word)
awsize = 0 (1 byte)
awlen = 0 (1 beat)

Address within word: 0x1002 - 0x1000 = byte 2

wdata = 32'hXX_AB_XX_XX  (only byte 2 matters)
wstrb = 4'b0100         (only enable byte 2)

Memory at 0x1000: [byte3][byte2][byte1][byte0]
After write:      [  -  ][ 0xAB][  -  ][ - ]
                                ^^^
                           Only this byte written
```

### Full vs Partial Strobes

```
Full Write (all strobes set):
  wstrb = 8'b1111_1111  → All bytes written
  Simple for slave (no read-modify-write)

Partial Write (some strobes clear):
  wstrb = 8'b0000_1111  → Lower 4 bytes written
  Slave must preserve upper 4 bytes unchanged
  May require read-modify-write in some slaves
```

## 3.2.9 Common Issues and Debug

### Issue 1: W Channel Starvation
```
Symptom: AW transfers but W channel never provides data
Cause:
  - Master FSM bug (forgot to drive W)
  - W FIFO empty
  - W channel disconnected
Check:
  - After AW transfer, W must follow
  - Monitor wvalid after awvalid
```

### Issue 2: W Beat Count Mismatch
```
Symptom: Wrong number of W beats for AW transaction
Cause:
  - wlast logic error
  - W counter bug
  - Interleaving attempted
Check:
  - Count W beats between AW transfer and wlast
  - Must equal (awlen + 1)
```

### Issue 3: W Interleaving Attempted
```
Symptom: Protocol violation, wrong data written
Cause:
  - Multiple masters driving W simultaneously (bridge bug)
  - Master trying to interleave different transactions
Check:
  - Only ONE W transaction active at a time
  - Complete all W beats (until wlast) before next AW
```

### Issue 4: Invalid wstrb
```
Symptom: Unexpected bytes written or not written
Cause:
  - wstrb doesn't match awsize and awaddr
  - wstrb has illegal pattern
Check:
  - Calculate expected wstrb from awaddr/awsize
  - Ensure contiguous '1' bits in wstrb (for aligned transfers)
```

### Issue 5: wvalid Dropped Before Handshake
```
Symptom: Data beat lost
Cause:
  - wvalid deasserted before wready seen
Check:
  - wvalid must stay HIGH until (wvalid && wready)
  - Master FSM must hold wvalid
```

## 3.2.10 Bridge-Specific W Channel Considerations

### W Channel Arbitration

```
Bridge W channel follows AW arbitration:

Step 1: Arbiter grants AW from master M (awid=X, awlen=N)
Step 2: Bridge connects M's W channel to slave
Step 3: Bridge waits for (N+1) W beats until wlast
Step 4: Bridge can grant next AW (possibly different master)

During Step 3:
  - Other masters' W channels are blocked
  - Other masters see wready=0 from bridge
  - This master's W has exclusive access
```

### W Channel Routing

```
Unlike AW/AR channels (routed by address), W channel:
  - Has no address field
  - Has no ID field
  - Must follow corresponding AW

Bridge routing:
  - After AW routes to slave S
  - W channel automatically routes to same slave S
  - Routing held until wlast seen
  - Then released for next transaction
```

### W Channel Buffering

```
Bridge may include W data buffering:
  - Small FIFO to decouple master and slave timing
  - Improves throughput
  - Allows master to push data ahead

Depth typically:
  - 2-4 entries for basic buffering
  - Deeper (8-16) for high-performance
```

---

**Related Sections:**
- Section 3.1: Write Address Channel (AW)
- Section 3.3: Write Response Channel (B)
- Section 2.6: Width Conversion
- Section 2.4: Arbitration

**Next:** [3.3 Write Response Channel (B)](03_write_response.md)
