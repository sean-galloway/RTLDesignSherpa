# 2.8 Response Routing

Response Routing is the mechanism by which slave responses (read data and write acknowledgments) are directed back to the originating master. This system uses Bridge IDs, demultiplexing logic, and optional CAM structures to ensure responses reach the correct destination.

## 2.8.1 Purpose and Function

Response routing performs the following critical functions:

1. **Response Direction**: Routes R and B channel responses to correct master
2. **ID-Based Routing**: Uses extracted Bridge IDs to determine destination
3. **Multi-Slave Merging**: Combines responses from multiple slaves to single master
4. **Flow Control**: Manages backpressure from master on response channels
5. **Error Propagation**: Ensures error responses reach originating master

## 2.8.2 Block Diagram

![Response Routing Architecture](../assets/graphviz/response_routing.svg)

*Figure 2.8: Response routing architecture showing B and R channel merging from slaves and ID-based demultiplexing to masters.*

## 2.8.3 BID Extraction

### Simple Extraction (No CAM)

For configurations where direct BID mapping suffices:

```systemverilog
// Extract Bridge ID from response ID
logic [TOTAL_RID_WIDTH-1:0] slave_rid;     // From slave
logic [BID_WIDTH-1:0] extracted_bid;       // Master index
logic [RID_WIDTH-1:0] external_rid;        // To master

// Upper bits = Bridge ID, lower bits = original ID
assign extracted_bid = slave_rid[TOTAL_RID_WIDTH-1:RID_WIDTH];
assign external_rid = slave_rid[RID_WIDTH-1:0];

// Route response based on BID
logic [NUM_MASTERS-1:0] master_rvalid;
always_comb begin
    master_rvalid = '0;  // Default: no master selected
    master_rvalid[extracted_bid] = slave_rvalid;
end
```

### CAM-Based Extraction

For complex configurations with OOO or ID reordering:

```systemverilog
// CAM lookup for response routing
logic [TOTAL_RID_WIDTH-1:0] response_id;
logic [BID_WIDTH-1:0] master_index;
logic cam_hit;

// Search CAM for matching transaction
assign {cam_hit, master_index} = cam_lookup(response_id);

// Route response to found master
if (cam_hit) begin
    master_rvalid[master_index] = slave_rvalid;
end else begin
    // Error: No matching transaction (protocol violation)
    error_response();
end
```

## 2.8.4 Response Demultiplexing

### Per-Master Response Paths

Each master has dedicated response channels from the demultiplexer:

```
Master 0 Response:
  - M0_RVALID, M0_RREADY, M0_RDATA, M0_RID, M0_RRESP, M0_RLAST
  - M0_BVALID, M0_BREADY, M0_BID, M0_BRESP

Source: Responses from any slave with BID=0
```

### Demux Implementation

```systemverilog
// Response demultiplexer (4 masters, 3 slaves)
// Combines responses from all slaves, routes to correct master

// Slave responses (multiple sources)
logic s0_rvalid, s1_rvalid, s2_rvalid;
logic [63:0] s0_rdata, s1_rdata, s2_rdata;
logic [5:0] s0_rid, s1_rid, s2_rid;  // Includes BID

// Master responses (multiple destinations)
logic m0_rvalid, m1_rvalid, m2_rvalid, m3_rvalid;
logic [63:0] m0_rdata, m1_rdata, m2_rdata, m3_rdata;
logic [3:0] m0_rid, m1_rid, m2_rid, m3_rid;  // BID stripped

// Demux logic per slave
for (genvar s = 0; s < 3; s++) begin
    logic [1:0] bid;
    assign bid = slave_rid[s][5:4];  // Extract BID
    
    always_comb begin
        case (bid)
            2'b00: begin
                if (slave_rvalid[s] && !m0_busy) begin
                    m0_rvalid = 1'b1;
                    m0_rdata = slave_rdata[s];
                    m0_rid = slave_rid[s][3:0];  // Strip BID
                end
            end
            2'b01: /* Route to M1 */
            2'b10: /* Route to M2 */
            2'b11: /* Route to M3 */
        endcase
    end
end
```

## 2.8.5 Multi-Slave Response Merging

### Problem Statement

When multiple slaves can respond to same master simultaneously:

```
Scenario:
  Master 0 has outstanding transactions to Slave 0 and Slave 1
  Both slaves return R responses in same cycle
  
Problem: Master 0 can only accept one R response per cycle
Solution: Arbitrate between slave responses
```

### Response Arbitration

```systemverilog
// Arbitrate between multiple slave responses for same master
logic [2:0] slave_has_response;  // Which slaves have responses for M0
logic [1:0] selected_slave;      // Which slave wins arbitration

// Detect responses destined for M0
for (genvar s = 0; s < 3; s++) begin
    assign slave_has_response[s] = slave_rvalid[s] && 
                                   (extract_bid(slave_rid[s]) == 2'b00);
end

// Round-robin arbiter for fairness
always_ff @(posedge clk) begin
    if (!rst_n) begin
        selected_slave <= 0;
    end else if (m0_rready && (|slave_has_response)) begin
        // Rotate selection for fairness
        if (slave_has_response[selected_slave])
            ; // Keep current
        else
            selected_slave <= find_next_requesting_slave();
    end
end

// MUX selected slave's response to master
assign m0_rvalid = slave_has_response[selected_slave];
assign m0_rdata = slave_rdata[selected_slave];
assign m0_rid = strip_bid(slave_rid[selected_slave]);
```

### Response Buffering

Optional: Add FIFOs to buffer pending responses:

```
Purpose:
  - Prevent response loss during arbitration conflicts
  - Allow slaves to return responses even if master busy
  - Smooth out bursty response patterns

Configuration:
  per_master_response_fifo_depth = 4-16 entries

Trade-off:
  + No response loss
  + Better throughput
  - Additional resources (~200 LEs per FIFO)
  - +1-2 cycle latency
```

## 2.8.6 Backpressure Management

### Ready Signal Routing

Master RREADY/BREADY must reach correct slave:

```systemverilog
// Route master ready back to slaves
logic m0_rready;  // From master
logic [2:0] slave_rready;  // To slaves

// Only selected slave sees master's ready
for (genvar s = 0; s < 3; s++) begin
    assign slave_rready[s] = (selected_slave == s) ? m0_rready : 1'b0;
end

// Non-selected slaves see ready = 0 (backpressure)
```

### Stall Conditions

Response path can stall when:

```
1. Master not ready (M_RREADY = 0)
   → Selected slave stalls (S_RREADY = 0)
   → Other slaves buffer or stall

2. Arbitration conflict (multiple slaves ready)
   → Non-selected slaves stalled
   → Selected slave proceeds

3. Response FIFO full
   → Slave stalled until space available
```

## 2.8.7 Response Path Latency

### End-to-End R Channel

```
Slave R response → Bridge → Master R channel

Components:
1. Slave response valid
2. BID extraction (0 cycles, combinatorial)
3. Demux routing (0-1 cycles)
4. Response arbitration (1 cycle if conflict)
5. Optional FIFO (0-1 cycles)
6. Master adapter (1 cycle, skid buffer)

Total: 2-4 cycles typical
```

### End-to-End B Channel

```
Similar to R channel:
  Slave B → Extraction → Demux → Arbitration → Master B
  Total: 2-4 cycles
```

## 2.8.8 Error Response Routing

### Slave Error Responses

When slave returns error:

```
RRESP = 2'b10 (SLVERR) or 2'b11 (DECERR)
BRESP = 2'b10 (SLVERR) or 2'b11 (DECERR)

Routing:
  - Extract BID normally
  - Route to originating master
  - Preserve error code
  - Master sees error response
```

### Out-of-Range Error Responses

When router generates error for OOR address:

```
Process:
1. Router captures OOR request
2. Generates internal error response
   - Uses cached request ID (with BID)
   - Sets RRESP/BRESP = DECERR
3. Injects into response path
4. Routes to master using BID
```

## 2.8.9 Resource Utilization

### Response Router Resources

**4 masters, 3 slaves (64-bit data)**:

```
Logic Elements:  ~1500-2000 LEs
Registers:       ~400-600 regs
Block RAM:       0 (unless FIFOs enabled)

Breakdown:
- BID extraction (3 slaves):     ~150 LEs
- Demux logic (4 masters):        ~600 LEs, ~150 regs
- Response arbitration:           ~300 LEs, ~100 regs
- Backpressure routing:           ~200 LEs, ~50 regs
- Control FSMs:                   ~250 LEs, ~100 regs

Optional FIFOs (4 × 8 entries):  +800 LEs, +2KB BRAM
```

### Scaling

```
Resource usage scales with:
- Number of masters: Linear (one demux path per master)
- Number of slaves: Linear (one extraction per slave)
- Data width: Linear (wider data = wider demux)
- FIFO depth: Linear (deeper = more BRAM)
```

## 2.8.10 Configuration Parameters

### Response Routing Configuration (TOML)

```toml
[bridge]
num_masters = 4
num_slaves = 3

[bridge.response_routing]
enable_response_fifos = false       # Buffer responses per master
fifo_depth = 8                      # Entries per FIFO
response_arbiter_type = "round_robin"  # "round_robin", "fixed_priority"
registered_demux = false            # Register demux output (+1 cycle)

# Per-master response credits (optional)
[[masters]]
name = "cpu"
max_response_credits = 16           # Outstanding responses allowed
```

## 2.8.11 Debug and Observability

### Recommended Debug Signals

```
BID Extraction:
- Slave RID/BID (from each slave)
- Extracted BID (master index)
- External RID/BID (to master, BID stripped)

Response Demux:
- Demux select signals (which master per slave)
- Response valid per master
- Response valid per slave

Arbitration:
- Conflict detection (multiple responses for same master)
- Arbiter grant (which slave wins)
- Stall counters

FIFOs (if enabled):
- FIFO occupancy per master
- FIFO full/empty flags
- FIFO overflow errors
```

### Performance Counters

```
- Responses routed per master
- Arbitration conflicts (cycles with multiple responses to same master)
- Response stall cycles (master not ready)
- Average response latency per master
- FIFO overflow counts
- CAM hits/misses (if CAM enabled)
```

## 2.8.12 Common Issues and Debug

**Symptom**: Response not reaching master  
**Check**:
- BID extraction (correct bit slicing?)
- Master index (BID → master mapping)
- Demux select logic
- Backpressure (is master READY?)

**Symptom**: Response goes to wrong master  
**Check**:
- BID values (verify each master has unique BID)
- BID width calculation (clog2 correct?)
- CAM contents (if used)
- ID corruption in transit

**Symptom**: Response ordering incorrect  
**Check**:
- CAM lookup (should preserve order)
- Arbitration fairness (round-robin working?)
- Multiple outstanding transactions per master

**Symptom**: Response loss  
**Check**:
- FIFO overflows (enable FIFOs if needed)
- Dropped responses during arbitration conflicts
- Protocol violations (slave not following AXI rules)

## 2.8.13 Verification Considerations

### Test Scenarios

1. **Single Master, Single Slave**:
```
- Basic routing test
- Verify BID extraction and stripping
- Check response reaches correct master
```

2. **Multiple Masters, Single Slave**:
```
- Interleaved responses
- Verify each response routes to correct master
- Check BID uniqueness prevents collisions
```

3. **Single Master, Multiple Slaves**:
```
- Simultaneous responses from multiple slaves
- Verify arbitration fairness
- Check no response loss
```

4. **All Masters, All Slaves**:
```
- Maximum stress test
- All masters issuing to all slaves
- Responses returning in various orders
- Verify correct routing under heavy load
```

5. **OOO Responses**:
```
- Issue transactions: ID=1, ID=2, ID=3
- Return responses: ID=3, ID=1, ID=2
- Verify CAM correctly routes each
- Check response order at master
```

6. **Backpressure Test**:
```
- Master asserts RREADY=0
- Verify slave stalls (RREADY=0 propagated)
- Master asserts RREADY=1
- Verify responses flow
```

## 2.8.14 Performance Optimization

### Techniques

**1. Registered Demux**:
```
Trade-off: +1 cycle latency for timing closure
Best for: High-frequency designs, many masters
```

**2. Response FIFOs**:
```
Trade-off: +2KB BRAM, +1-2 cycle latency
Benefit: Prevent response loss, smooth conflicts
Best for: High-throughput systems
```

**3. Distributed Arbitration**:
```
Implementation: Per-master arbiters instead of global
Benefit: Reduced logic depth, better timing
Best for: >8 masters
```

**4. Priority Response Routing**:
```
Implementation: High-priority masters get preference in conflicts
Benefit: Guaranteed low latency for critical masters
Best for: Real-time systems
```

## 2.8.15 Advanced Features

### Response Reordering (Future)

Allow bridge to reorder responses for efficiency:

```
Scenario:
  Master issues: Req A (slow slave), Req B (fast slave)
  Fast slave responds first
  Bridge can deliver B before A (if IDs different)

Benefit: Reduced latency for fast responses
Requirement: CAM to track outstanding in-order constraints
```

### Response Coalescing (Future)

Combine multiple responses into fewer beats:

```
Scenario:
  Multiple single-beat reads to narrow slave
  Bridge coaleses into fewer wide beats
  
Benefit: Reduced overhead
Complexity: High (requires buffering and alignment)
```

### Response QoS (Future)

Prioritize responses based on master QoS:

```
Feature: High-QoS masters get response priority
Implementation: Weighted arbitration in response path
Use case: RT masters need bounded response latency
```

## 2.8.16 Timing Considerations

### Critical Paths

Common critical paths in response routing:

```
1. BID extraction → Demux select → Master RDATA
   Depth: ~8-12 logic levels
   
2. Slave RVALID → Arbitration → Master RVALID
   Depth: ~6-10 logic levels
   
3. Master RREADY → Backpressure → Slave RREADY
   Depth: ~5-8 logic levels
```

### Optimization Strategies

```
- Register demux outputs (+1 cycle, breaks path)
- Pipeline arbitration (+1-2 cycles, multi-stage)
- Use CAM for complex ID scenarios (parallel lookup)
- Limit response buffering depth (less MUX levels)
```

## 2.8.17 Future Enhancements

### Planned Features
- **Dynamic Response Buffering**: Adjust FIFO depth based on utilization
- **Response Ordering Hints**: Masters specify ordering requirements
- **Multi-Cycle Arbitration**: Pipelined for >16 masters
- **Response Compression**: Pack narrow responses into wide beats

### Under Consideration
- **Response Speculation**: Predictive routing before full ID available
- **Virtual Response Channels**: Separate paths for different QoS classes
- **Response Mirroring**: Duplicate responses for redundancy
- **Cross-Clock Response**: Async response paths with CDC

---

**Related Sections**:
- Section 2.3: Crossbar Core (response path architecture)
- Section 2.5: ID Management (BID extraction details)
- Section 2.4: Arbitration (response arbitration algorithms)
- Section 3.2: Master Port Interface (response channel signals)
