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

### Bridge Arbiter Finite State Machines

#### Overview

The Bridge AXI4 crossbar implements independent per-slave arbitration using simple 2-state finite state machines (FSMs). Each slave has two dedicated arbiters:

- **AW Arbiter** - Write Address channel arbitration
- **AR Arbiter** - Read Address channel arbitration

**Total FSM Count:** `2 × NUM_SLAVES`

These arbiters provide fair, round-robin access to slave resources, preventing master starvation while maintaining simple, predictable behavior.

#### AW Channel Arbiter FSM

**Purpose:** Arbitrate write address requests from multiple masters to a single slave

**States:** 2 (IDLE, GRANT_ACTIVE)

**Algorithm:** Round-robin with grant locking

### Figure 5.3: AW Arbiter FSM

![AW Arbiter FSM](assets/puml/aw_arbiter_fsm.png)

**State Descriptions:**

**IDLE State:**
- **Entry Actions:**
  - `aw_grant_matrix[s] = 0` - No grant issued
  - `aw_grant_active[s] = 0` - Arbiter inactive
- **Behavior:**
  - Monitor `aw_request_matrix[s]` for master requests
  - Track round-robin priority via `aw_last_grant[s]`
  - Remain in IDLE until at least one master requests access

**GRANT_ACTIVE State:**
- **Entry Actions:**
  - `aw_grant_matrix[s][m] = 1` - Issue grant to winning master
  - `aw_grant_active[s] = 1` - Mark arbiter as active
- **Behavior:**
  - Hold grant until AW handshake completes (`AWVALID && AWREADY`)
  - W channel data multiplexing follows AW grant
  - B channel response uses ID table (not grant-based)

**State Transitions:**

| From | To | Condition | Description |
|------|-----|-----------|-------------|
| IDLE | GRANT_ACTIVE | `\|aw_request_matrix[s]\| > 0` | At least one master requesting access |
| GRANT_ACTIVE | IDLE | `m_axi_awvalid[s] && m_axi_awready[s]` | AW handshake complete |

#### AR Channel Arbiter FSM

**Purpose:** Arbitrate read address requests from multiple masters to a single slave

**States:** 2 (IDLE, GRANT_ACTIVE)

**Algorithm:** Round-robin with grant locking (same as AW)

### Figure 5.4: AR Arbiter FSM

![AR Arbiter FSM](assets/puml/ar_arbiter_fsm.png)

**State Descriptions:**

**IDLE State:**
- **Entry Actions:**
  - `ar_grant_matrix[s] = 0` - No grant issued
  - `ar_grant_active[s] = 0` - Arbiter inactive
- **Behavior:**
  - Monitor `ar_request_matrix[s]` for master requests
  - Track round-robin priority via `ar_last_grant[s]`
  - Independent from AW arbiter state

**GRANT_ACTIVE State:**
- **Entry Actions:**
  - `ar_grant_matrix[s][m] = 1` - Issue grant to winning master
  - `ar_grant_active[s] = 1` - Mark arbiter as active
- **Behavior:**
  - Hold grant until AR handshake completes (`ARVALID && ARREADY`)
  - R channel data multiplexing follows AR grant
  - R channel response uses ID table for routing

**State Transitions:**

| From | To | Condition | Description |
|------|-----|-----------|-------------|
| IDLE | GRANT_ACTIVE | `\|ar_request_matrix[s]\| > 0` | At least one master requesting read |
| GRANT_ACTIVE | IDLE | `m_axi_arvalid[s] && m_axi_arready[s]` | AR handshake complete |

#### Round-Robin Arbitration Algorithm

**Algorithm Description:**

Both AW and AR arbiters use the same fair round-robin arbitration algorithm:

```
Pseudocode:
1. Start search from (last_grant[s] + 1) % NUM_MASTERS
2. Search cyclically through all masters
3. Select first master with pending request
4. Update last_grant[s] = winning_master
5. Issue grant
```

**Example with 4 Masters:**

```
Initial state: last_grant[0] = 0

Request Pattern:
  Master 0: request
  Master 1: request
  Master 2: no request
  Master 3: request

Arbitration Sequence:
  Grant 1: Master 1 (start from master 1, first requester)
          last_grant = 1

  Grant 2: Master 3 (start from master 2, find master 3)
          last_grant = 3

  Grant 3: Master 0 (start from master 0, first requester)
          last_grant = 0

  Grant 4: Master 1 (start from master 1, first requester)
          last_grant = 1
```

**Fairness Properties:**

1. **No Starvation** - Every requesting master will eventually receive grant
2. **Priority Rotation** - Priority shifts after each grant
3. **Predictable Latency** - Maximum wait time = (NUM_MASTERS - 1) × grant_duration
4. **Equal Opportunity** - All masters treated equally

#### Grant Locking Mechanism

**Purpose:** Prevent grant changes mid-transaction

**AW Grant Locking:**

```systemverilog
// AW grant locked until address handshake completes
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        aw_grant_active[s] <= 1'b0;
        aw_grant_matrix[s] <= '0;
    end else begin
        if (aw_grant_active[s]) begin
            // GRANT_ACTIVE state: Hold grant until handshake
            if (m_axi_awvalid[s] && m_axi_awready[s]) begin
                aw_grant_active[s] <= 1'b0;  // Return to IDLE
                aw_grant_matrix[s] <= '0;
            end
        end else if (|aw_request_matrix[s]) begin
            // IDLE state: Arbitrate if requests pending
            aw_grant_matrix[s] <= round_robin_select(aw_request_matrix[s]);
            aw_grant_active[s] <= 1'b1;  // Enter GRANT_ACTIVE
        end
    end
end
```

**AR Grant Locking:**

```systemverilog
// AR grant locked until address handshake completes
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        ar_grant_active[s] <= 1'b0;
        ar_grant_matrix[s] <= '0;
    end else begin
        if (ar_grant_active[s]) begin
            // GRANT_ACTIVE state: Hold grant until handshake
            if (m_axi_arvalid[s] && m_axi_arready[s]) begin
                ar_grant_active[s] <= 1'b0;  // Return to IDLE
                ar_grant_matrix[s] <= '0;
            end
        end else if (|ar_request_matrix[s]) begin
            // IDLE state: Arbitrate if requests pending
            ar_grant_matrix[s] <= round_robin_select(ar_request_matrix[s]);
            ar_grant_active[s] <= 1'b1;  // Enter GRANT_ACTIVE
        end
    end
end
```

**Why Grant Locking Matters:**

1. **Protocol Compliance** - AXI4 spec requires stable AWID/ARID during handshake
2. **Data Integrity** - W channel must follow granted master's AW request
3. **Response Routing** - B/R channels need consistent transaction tracking
4. **Simplicity** - Single grant active per slave prevents mux conflicts

#### Independent Read/Write Arbitration

**Key Design Feature:** AW and AR arbiters operate completely independently

**Benefits:**

1. **No Head-of-Line Blocking:**
   - Read requests don't wait for write completion
   - Write requests don't wait for read completion

2. **Parallel Operation:**
   - Master 0 can write to Slave 0 (AW path)
   - Master 1 can read from Slave 0 (AR path)
   - Both transactions proceed simultaneously

3. **Resource Efficiency:**
   - Full utilization of read/write bandwidth
   - No artificial serialization

**Example Scenario:**

```
Time T0: Master 0 issues write to Slave 0
         - AW arbiter grants to Master 0
         - AW_GRANT_ACTIVE = 1
         - W data follows

Time T1: Master 1 issues read to Slave 0 (during Master 0 write)
         - AR arbiter grants to Master 1 (independent!)
         - AR_GRANT_ACTIVE = 1
         - R data returns

Result: Read and write happen in parallel - no blocking
```

#### FSM Instance Breakdown by Configuration

**2×2 Configuration (2 masters, 2 slaves):**
- Slave 0 AW Arbiter: 1 FSM
- Slave 0 AR Arbiter: 1 FSM
- Slave 1 AW Arbiter: 1 FSM
- Slave 1 AR Arbiter: 1 FSM
- **Total: 4 FSMs**

**4×4 Configuration (4 masters, 4 slaves):**
- 4 slaves × 2 arbiters per slave = **8 FSMs**

**8×8 Configuration (8 masters, 8 slaves):**
- 8 slaves × 2 arbiters per slave = **16 FSMs**

**Scalability:**
- FSM count scales linearly with NUM_SLAVES
- Arbitration complexity scales with NUM_MASTERS (search time)
- Synthesis impact minimal for up to 16×16 configurations

#### Performance Characteristics

**Latency:**

- **Best Case:** 1 clock cycle (IDLE → GRANT_ACTIVE → IDLE with immediate handshake)
- **Worst Case:** (NUM_MASTERS) clock cycles (round-robin search + contention)
- **Average Case:** ~(NUM_MASTERS / 2) clock cycles

**Throughput:**

- **Back-to-Back Grants:** Possible if different masters (no wait)
- **Same Master Repeated:** 1 cycle minimum between grants (FSM state change)

**Fairness:**

- **Guaranteed:** Every master gets grant within (NUM_MASTERS - 1) arbitration cycles
- **No Priority:** All masters treated equally (can be extended for QoS)

#### Comparison with Other Crossbar Arbiters

| Feature | Bridge Arbiter | APB Crossbar | Commercial Tools |
|---------|----------------|--------------|------------------|
| **States** | 2 (IDLE, GRANT_ACTIVE) | 1 (passthrough) | 3-5 (complex) |
| **Algorithm** | Round-robin | N/A (APB is 1:1) | Priority, QoS, weighted |
| **Grant Locking** | Yes (until handshake) | N/A | Burst-aware locking |
| **Read/Write Indep** | Yes (2 FSMs/slave) | N/A | Yes |
| **Complexity** | Low | Minimal | High |
| **Predictability** | High (round-robin) | N/A | Medium (priority-based) |

**Simplicity Trade-off:**

- **Advantages:**
  - Easy to verify (2-state FSM)
  - Predictable latency
  - Fair resource allocation

- **Limitations (future enhancements):**
  - No Quality-of-Service (QoS) support
  - No priority levels
  - No weighted arbitration

#### Future Enhancements (Phase 3+)

**QoS Support:**
```systemverilog
// Master QoS priority field (AXI4 optional)
input logic [3:0] s_axi_awqos [NUM_MASTERS];

// Arbitration considers QoS priority
function automatic [NUM_MASTERS-1:0] qos_arbitrate(
    input logic [NUM_MASTERS-1:0] requests,
    input logic [3:0] qos [NUM_MASTERS]
);
    // Higher QoS value = higher priority
    // Round-robin among same QoS level
endfunction
```

**Weighted Arbitration:**
```systemverilog
// Master weight configuration
parameter int MASTER_WEIGHTS [NUM_MASTERS] = '{1, 2, 1, 4};

// Grant frequency proportional to weight
// Master 3 gets 4× more grants than Master 0
```

**Burst-Aware Locking:**
```systemverilog
// Lock grant until entire burst completes
// Currently: Lock until address handshake
// Enhanced: Lock until WLAST (write) or RLAST (read)
```

---

**See Also:**
- [1.1 - Introduction](../ch01_overview/01_introduction.md) - Bridge overview
- [3.1 - Module Structure](01_module_structure.md) - Generated RTL organization
- [3.3 - Crossbar Core](03_crossbar_core.md) - Internal crossbar instantiation

**Reference:**
- ARM AMBA AXI4 Specification (IHI 0022E) - Section A7 (Arbitration)

---

**Next:** [3.3 - Crossbar Core](03_crossbar_core.md)
