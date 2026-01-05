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

# 2.4 Arbitration

Arbitration is the mechanism by which the bridge decides which master gains access to a slave when multiple masters simultaneously request the same slave. Each slave has dedicated arbiters for its read and write channels, enabling fair and efficient resource allocation.

## 2.4.1 Purpose and Function

The arbiter performs the following critical functions:

1. **Conflict Resolution**: Selects one master when multiple masters request same slave
2. **Fairness**: Ensures all masters eventually get access (starvation-free)
3. **Throughput Optimization**: Minimizes idle cycles and maximizes utilization
4. **Grant Management**: Maintains grants for burst transactions
5. **Priority Enforcement**: Supports priority-based access policies (optional)

## 2.4.2 Arbitration Architecture

### Per-Slave, Per-Channel Arbiters

Each slave has **two independent arbiters**:

```
Slave 0:
  - AR Arbiter (Read Address Channel)
    * Inputs: M0_ARVALID, M1_ARVALID, M2_ARVALID, M3_ARVALID
    * Output: Grant[1:0] → Selects one master
    
  - AW Arbiter (Write Address Channel)
    * Inputs: M0_AWVALID, M1_AWVALID, M2_AWVALID, M3_AWVALID
    * Output: Grant[1:0] → Selects one master
    * Coordinates with W channel data flow
```

**Independence**: AR and AW arbiters operate independently, allowing simultaneous read and write to same slave (if slave supports full-duplex operation).

### Block Diagram

```
                    ARBITER (per slave, per channel)
                    
    From Masters                                  To Slave
    (via Router)                                  (via MUX)
         │                                            │
         │   ┌────────────────────────────────────┐  │
         │   │                                    │  │
    M0───┼──>│  Request                           │  │
 (VALID) │   │  Capture   ┌──────────────────┐   │  │
         │   │            │                  │   │  │
    M1───┼──>│            │  Arbitration     │   │  │
 (VALID) │   │            │  Logic           │───┼──┼──> GRANT[1:0]
         │   │            │  • Round-Robin   │   │  │    (Master Select)
    M2───┼──>│            │  • Fixed Prio    │   │  │
 (VALID) │   │            │  • Weighted      │   │  │
         │   │            │                  │   │  │
    M3───┼──>│            └──────────────────┘   │  │
 (VALID) │   │                     │             │  │
         │   │            ┌────────▼─────────┐   │  │
    S────┼───│<───────────┤  Burst Tracking  │   │  │
(READY)  │   │            │  (Hold Grant)    │   │  │
         │   │            └──────────────────┘   │  │
    S────┼───│<───────────┐                      │  │
(LAST)   │   │            │  Grant held until   │  │
         │   │            │  LAST asserted       │  │
         │   │            └──────────────────────┘  │
         │   │                                    │  │
         │   └────────────────────────────────────┘  │
         │                                            │
```

## 2.4.3 Round-Robin Arbitration

### Algorithm

The **Round-Robin (RR)** arbiter cycles through masters in order, giving each master one opportunity to access the slave:

```
Priority Order (rotates after each grant):
  Cycle 0: M0 > M1 > M2 > M3
  Cycle 1: M1 > M2 > M3 > M0  (M0 was granted, now lowest priority)
  Cycle 2: M2 > M3 > M0 > M1  (M1 was granted)
  Cycle 3: M3 > M0 > M1 > M2  (M2 was granted)
  Cycle 4: M0 > M1 > M2 > M3  (M3 was granted, cycle repeats)
```

### Implementation

```systemverilog
// Simplified Round-Robin arbiter (4 masters)
logic [1:0] last_grant;      // Which master was granted last
logic [3:0] request;         // Current requests (VALID signals)
logic [1:0] grant;           // Grant decision

always_ff @(posedge clk) begin
    if (!rst_n) begin
        last_grant <= 2'b00;
    end else if (|request && slave_ready) begin
        // Update last_grant when transaction completes
        if (grant_accepted) begin
            last_grant <= grant;
        end
    end
end

always_comb begin
    // Default: No grant
    grant = 2'b00;
    
    // Priority encode starting after last grant
    case (last_grant)
        2'b00: begin  // Last grant to M0, try M1, M2, M3, M0
            if (request[1])      grant = 2'b01;
            else if (request[2]) grant = 2'b10;
            else if (request[3]) grant = 2'b11;
            else if (request[0]) grant = 2'b00;
        end
        2'b01: begin  // Last grant to M1, try M2, M3, M0, M1
            if (request[2])      grant = 2'b10;
            else if (request[3]) grant = 2'b11;
            else if (request[0]) grant = 2'b00;
            else if (request[1]) grant = 2'b01;
        end
        // ... similar for M2, M3
    endcase
end
```

### Characteristics

**Fairness**: Excellent - Each master gets equal access over time  
**Latency**: Bounded - Maximum wait = (N-1) × transaction_time  
**Throughput**: Optimal - No idle cycles when requests pending  
**Starvation**: None - Every master eventually gets grant  

**Best Use Cases**:
- Peers with similar priority
- General-purpose interconnects
- Default choice for most bridges

## 2.4.4 Fixed-Priority Arbitration

### Algorithm

The **Fixed-Priority** arbiter always grants to the highest-priority requesting master:

```
Priority Order (never changes):
  M0 > M1 > M2 > M3  (M0 always highest priority)

Grant Decision:
  if (M0_VALID) → Grant = M0
  else if (M1_VALID) → Grant = M1
  else if (M2_VALID) → Grant = M2
  else if (M3_VALID) → Grant = M3
```

### Implementation

```systemverilog
// Fixed-priority arbiter (4 masters)
logic [3:0] request;
logic [1:0] grant;

always_comb begin
    // Priority encoder: M0 highest, M3 lowest
    if (request[0])      grant = 2'b00;  // M0 highest priority
    else if (request[1]) grant = 2'b01;
    else if (request[2]) grant = 2'b10;
    else if (request[3]) grant = 2'b11;  // M3 lowest priority
    else                 grant = 2'b00;  // Default (no requests)
end
```

### Characteristics

**Fairness**: Poor - Low-priority masters can starve  
**Latency**: Variable - High-priority: minimal, Low-priority: unbounded  
**Throughput**: Optimal - No idle cycles when requests pending  
**Starvation**: Possible for low-priority masters  

**Best Use Cases**:
- Real-time systems with priority requirements
- CPU (high) vs. DMA (low) scenarios
- Time-critical masters need guaranteed access

### Starvation Prevention

Optional enhancement: **Priority aging**
```
- Track cycles since last grant per master
- Temporarily boost priority of starved masters
- Reset age counter after grant

Example:
  M0 age = 100 cycles → Boost M0 above normal priority
  M1 age = 5 cycles   → Normal priority
```

## 2.4.5 Weighted Arbitration

### Algorithm

The **Weighted** arbiter assigns different access rates to masters based on weights:

```
Configuration:
  M0 weight = 4  (50% of bandwidth)
  M1 weight = 2  (25% of bandwidth)
  M2 weight = 1  (12.5% of bandwidth)
  M3 weight = 1  (12.5% of bandwidth)

Grant Sequence (repeating pattern):
  M0, M0, M0, M0, M1, M1, M2, M3  (8 cycles total)
  M0 gets 4/8, M1 gets 2/8, M2 gets 1/8, M3 gets 1/8
```

### Implementation

```systemverilog
// Weighted arbiter using credit counter
logic [7:0] credits [0:3];  // Credit counters per master
logic [1:0] grant;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        credits[0] <= 8'd4;  // M0 weight
        credits[1] <= 8'd2;  // M1 weight
        credits[2] <= 8'd1;  // M2 weight
        credits[3] <= 8'd1;  // M3 weight
    end else if (grant_accepted) begin
        // Decrement granted master's credits
        credits[grant] <= credits[grant] - 1;
        
        // Reload when all credits exhausted
        if (all_credits_zero) begin
            credits[0] <= 8'd4;
            credits[1] <= 8'd2;
            credits[2] <= 8'd1;
            credits[3] <= 8'd1;
        end
    end
end

always_comb begin
    // Grant to master with highest credits and active request
    grant = select_highest_credit_with_request(credits, request);
end
```

### Characteristics

**Fairness**: Configurable - Proportional to weights  
**Latency**: Bounded - Depends on weight ratio  
**Throughput**: Near-optimal - Small overhead for credit tracking  
**Starvation**: None - All masters get share per weight  

**Best Use Cases**:
- QoS requirements (guaranteed bandwidth)
- Mixed workload (video + CPU + DMA)
- Service-level agreements

## 2.4.6 Burst Handling

### Grant Locking

Once granted, a master **holds the grant** until its burst completes:

```
AR Channel Burst:
  1. Master asserts ARVALID with ARLEN = 7 (8-beat burst)
  2. Arbiter grants to this master
  3. Grant held until slave returns RLAST
  4. Other masters blocked during this time

AW/W Channel Burst:
  1. Master asserts AWVALID with AWLEN = 15 (16-beat burst)
  2. Arbiter grants to this master
  3. Grant held until master asserts WLAST
  4. Other masters blocked during W data transfer
```

### Implementation

```systemverilog
// Burst grant locking
logic grant_locked;
logic [1:0] locked_master;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        grant_locked <= 1'b0;
    end else begin
        if (grant_accepted && !last_beat) begin
            // Lock grant for burst
            grant_locked <= 1'b1;
            locked_master <= grant;
        end else if (last_beat) begin
            // Release grant when burst completes
            grant_locked <= 1'b0;
        end
    end
end

assign grant = grant_locked ? locked_master : arbiter_decision;
```

### Fairness Considerations

Long bursts can block other masters:
- Maximum AXI burst: 256 beats
- At 1 cycle/beat: Up to 256 cycles blocked
- Impacts latency for other masters

**Mitigation**:
- Limit burst lengths in master configuration
- Use burst interleaving (complex, not implemented in Phase 1)
- Monitor arbiter stall counters

## 2.4.7 Resource Utilization

### Per-Arbiter Resources

**Round-Robin (4 masters)**:
```
Logic Elements:  ~150 LEs
Registers:       ~40 regs

Breakdown:
- Priority encoder:        ~80 LEs
- Last grant tracking:     ~10 regs
- Request capture:         ~20 regs
- Grant FSM:               ~40 LEs, ~10 regs
```

**Fixed-Priority (4 masters)**:
```
Logic Elements:  ~80 LEs
Registers:       ~20 regs

Simpler than RR (no rotation logic)
```

**Weighted (4 masters)**:
```
Logic Elements:  ~200 LEs
Registers:       ~60 regs

Additional credit counters and comparison logic
```

### Scaling with Master Count

Resource usage scales approximately **O(N²)** where N = master count:

```
2 masters:  ~50 LEs
4 masters:  ~150 LEs
8 masters:  ~400 LEs
16 masters: ~1200 LEs
```

The N² scaling comes from:
- Priority encoder: Compares all pairs of masters
- Grant MUX: N-to-1 multiplexing increases with N

## 2.4.8 Timing Characteristics

### Arbitration Latency

**Single-Cycle Arbitration** (default):
```
Request → Grant Decision: 1 cycle
Grant Decision → MUX Output: 0 cycles (combinatorial)
Total: 1 cycle
```

**Multi-Cycle Arbitration** (high frequency):
```
Request → Grant Decision: 2-3 cycles (pipelined)
Improves timing at cost of latency
```

### Critical Paths

Typical critical paths in arbiter:
1. **Request collection**: All master VALID signals → Arbiter input
2. **Priority encode**: Compare all requests → Grant decision
3. **Grant propagate**: Grant → MUX select → Slave interface

**Path Depth**:
- 4 masters: ~6-8 logic levels
- 8 masters: ~8-12 logic levels
- 16 masters: ~12-16 logic levels

## 2.4.9 Configuration Parameters

### Arbiter Configuration (TOML)

```toml
[bridge]
arbiter_type = "round_robin"    # "round_robin", "fixed_priority", "weighted"

[bridge.arbitration]
pipeline_stages = 1              # 1-3 (more = better timing, higher latency)
enable_priority_aging = false    # Prevent starvation in fixed-priority
aging_threshold = 1000           # Cycles before priority boost

# Weighted arbitration weights (only if arbiter_type = "weighted")
[[bridge.arbitration.weights]]
master = "cpu"
weight = 4                       # Relative weight (1-255)

[[bridge.arbitration.weights]]
master = "dma"
weight = 2

[[bridge.arbitration.weights]]
master = "periph"
weight = 1
```

## 2.4.10 Debug and Observability

### Recommended Debug Signals

```
Per Arbiter:
- Request vector (all masters requesting)
- Grant decision (which master granted)
- Grant locked status (burst in progress)
- Last grant (for RR rotation tracking)

Performance Counters:
- Grants per master (utilization)
- Denied requests per master (contention)
- Average grant latency per master
- Arbiter conflict cycles (multiple requests, one grant)
```

### Common Issues and Debug

**Symptom**: Master never gets grant (starvation)  
**Check**:
- Arbiter type (fixed-priority can starve low-priority masters)
- Other masters continuously requesting?
- Enable priority aging if using fixed-priority

**Symptom**: Unfair access (one master dominates)  
**Check**:
- Arbiter type (should be round-robin for fairness)
- Burst lengths (long bursts block others)
- Request patterns (one master requesting more frequently)

**Symptom**: Low throughput despite requests  
**Check**:
- Arbiter conflicts (too many masters to one slave)
- Pipeline depth (excessive arbitration latency)
- Burst efficiency (short bursts waste cycles)

## 2.4.11 Verification Considerations

### Test Scenarios

1. **Fair Access Test** (Round-Robin):
```
- All masters continuously request same slave
- Verify each master gets equal grants over 1000 cycles
- Expected: Each of 4 masters gets ~250 grants
```

2. **Priority Test** (Fixed-Priority):
```
- High-priority master requests intermittently
- Low-priority masters request continuously
- Verify high-priority always wins when requesting
```

3. **Burst Locking Test**:
```
- Master issues 16-beat burst
- Other masters request during burst
- Verify grant held until LAST
- Verify other masters blocked during burst
```

4. **Weighted Bandwidth Test**:
```
- Configure M0=4, M1=2, M2=1, M3=1
- All masters request continuously for 10000 cycles
- Verify grants proportional: M0≈50%, M1≈25%, M2≈12.5%, M3≈12.5%
```

### Corner Cases

```
- Single master requesting (trivial grant)
- All masters requesting simultaneously (worst-case arbitration)
- Grant released and new grant same cycle (back-to-back)
- Master drops request after arbiter latency (stale grant)
- Maximum length burst (256 beats blocking)
```

## 2.4.12 Performance Impact

### Arbiter Choice Impact

**Round-Robin**:
- **Pros**: Fair, starvation-free, predictable latency
- **Cons**: Cannot prioritize time-critical masters
- **Use**: General-purpose, peer masters

**Fixed-Priority**:
- **Pros**: Guaranteed low latency for high-priority masters
- **Cons**: Low-priority can starve, unpredictable for low-priority
- **Use**: Real-time, priority-sensitive systems

**Weighted**:
- **Pros**: Configurable bandwidth allocation, QoS support
- **Cons**: More complex, small overhead
- **Use**: Mixed workload, SLA requirements

### Arbiter Efficiency

Assuming all masters request same slave continuously:

```
Best Case: 100% efficiency (one master)
  - No arbitration conflicts
  - Zero idle cycles

Typical Case: 25-50% per-master efficiency (4 masters, round-robin)
  - Each master gets ~25% of time grants
  - Load balancing to other slaves improves

Worst Case: Heavy contention
  - 4 masters to 1 slave: 25% efficiency per master
  - Solution: Add slaves or use more slaves in parallel
```

## 2.4.13 Future Enhancements

### Planned Features
- **Dynamic Weight Adjustment**: Runtime-configurable weights via registers
- **QoS Classes**: Multiple priority levels with configurable policies
- **Deadline-Based Arbitration**: Grant based on transaction deadlines
- **Predictive Arbitration**: Speculative grants to reduce latency

### Under Consideration
- **Multi-Level Arbitration**: Hierarchical for >16 masters
- **Token Bucket**: Rate limiting per master
- **History-Based**: Learn access patterns and optimize grants
- **ECC Protection**: For arbitration state (safety-critical systems)

---

**Related Sections**:
- Section 2.3: Crossbar Core (arbiter integration)
- Section 2.1: Master Adapter (request sources)
- Section 2.5: ID Management (transaction tracking during grants)
- Chapter 6: Performance (arbiter impact on throughput)
