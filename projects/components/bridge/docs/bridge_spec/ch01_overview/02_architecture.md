### Bridge - Architecture

#### High-Level Architecture

The Bridge component implements a **full M×N AXI4 crossbar** with address-based routing and ID-based response demultiplexing. The architecture consists of three main layers: adapters (per-master), crossbar (interconnect matrix), and protocol/width converters.

**Design Philosophy:**
- **Per-Master Adapters**: Independent data paths for each master
- **Shared Crossbar**: Address-based route selection and arbitration
- **Minimal Conversion**: Direct paths for matching widths, converters only where needed
- **Pipeline Flexibility**: Configurable skid buffers and optional FIFOs

---

#### Block Diagram

```
External Masters          Bridge Internal (64-bit)            External Slaves
================          =======================            ===============

 CPU Master (32-bit) ─┐
                      ├─→ [CPU Adapter] ────┐
 GPU Master (64-bit) ─┤                      │
                      ├─→ [GPU Adapter] ────┤
 DMA Master (64-bit) ─┤                      ├─→ [Crossbar] ─┬─→ DDR (64-bit)
                      └─→ [DMA Adapter] ────┘      Matrix    │
                                                               ├─→ SRAM (32-bit)
                                                               │
                                                               └─→ APB Periph

Adapter Functions:                  Crossbar Functions:
- Timing isolation                  - Address decode
- Width conversion (32→64)          - Arbitration (per slave)
- Address decode                    - ID-based routing
- Bridge ID assignment              - Width conversion (64→slave)
```

**Key Observation:** Internal 64-bit data path simplifies logic while supporting variable-width masters and slaves.

---

#### Module Hierarchy

```
bridge_top.sv (Top-Level)
├── bridge_pkg.sv (Package - Types and Structures)
│   ├── AXI4 channel types (axi4_ar_t, axi4_r_t, etc.)
│   ├── Data structures (64-bit internal width)
│   └── Bridge ID definitions
│
├── master_adapters/ (One per Master)
│   ├── cpu_master_adapter.sv
│   │   ├── axi4_slave_rd (Timing isolation)
│   │   ├── axi4_slave_wr (Timing isolation)
│   │   ├── Address decoder (Which slave?)
│   │   ├── Width converter (32→64 if needed)
│   │   └── Bridge ID injector (Master→bridge_id)
│   │
│   ├── gpu_master_adapter.sv
│   └── dma_master_adapter.sv
│
├── bridge_xbar.sv (Crossbar Interconnect)
│   ├── Arbitration logic (per-slave, per-channel)
│   │   ├── AW channel arbiters
│   │   └── AR channel arbiters
│   │
│   ├── Channel multiplexers (master selection)
│   │   ├── AW/W/AR channel muxes
│   │   └── B/R channel demuxes (ID-based)
│   │
│   ├── Slave adapters (per-slave)
│   │   ├── bridge_cam.sv (Bridge ID → Master ID tracking)
│   │   ├── Width converter (64→slave width)
│   │   └── Protocol converter (AXI4→APB if needed)
│   │
│   └── Backpressure management
│       ├── Skid buffers (configurable depth)
│       └── Optional FIFOs (for deep pipelining)
│
└── Dependencies
    ├── rtl/amba/axi4_slave_rd.sv (Read channel wrapper)
    ├── rtl/amba/axi4_slave_wr.sv (Write channel wrapper)
    ├── rtl/common/skid_buffer.sv (Backpressure buffer)
    └── rtl/bridge/bridge_cam.sv (CAM for ID tracking)
```

---

#### Adapter Architecture (Per-Master)

**Purpose:** Isolate master from crossbar, perform width/address conversion

**CPU Master Adapter Example:**

```
CPU Master (External 32-bit)
    │
    ├─→ [AXI4 Slave Wrapper] ────→ Timing isolation, protocol compliance
    │       (axi4_slave_rd/wr)
    │
    ├─→ [Address Decoder] ────────→ Generate slave_select signals
    │       base_addr/size check      slave_select_ar[N-1:0]
    │                                  slave_select_aw[N-1:0]
    │
    ├─→ [Width Converter] ────────→ 32-bit → 64-bit conversion
    │       (if master ≠ 64-bit)     Upsizing logic
    │
    ├─→ [Bridge ID Injector] ─────→ Add master's unique bridge_id
    │       BRIDGE_ID parameter       to every transaction
    │
    └─→ [64-bit Internal Path] ───→ To crossbar
            cpu_master_64b_ar
            cpu_master_64b_r
            cpu_master_64b_aw
            cpu_master_64b_w
            cpu_master_64b_b
```

**Key Adapter Signals:**

| Signal | Width | Direction | Purpose |
|--------|-------|-----------|---------|
| `{master}_m_axi_*` | Native | Input | External master interface |
| `slave_select_ar[S-1:0]` | S | Output | Read address decode result |
| `slave_select_aw[S-1:0]` | S | Output | Write address decode result |
| `{master}_64b_ar` | Struct | Output | 64-bit internal read addr |
| `{master}_64b_r` | Struct | Input | 64-bit internal read data |
| `{master}_64b_aw` | Struct | Output | 64-bit internal write addr |
| `{master}_64b_w` | Struct | Output | 64-bit internal write data |
| `{master}_64b_b` | Struct | Input | 64-bit internal write resp |

---

#### Crossbar Architecture

**Purpose:** Route transactions between adapters and slaves based on address decode and arbitration

**Crossbar Structure:**

```
From Adapters (64-bit internal)       To Slaves (variable width)
===================================   =============================

cpu_64b_ar ──┐                        
gpu_64b_ar ──┤                        
dma_64b_ar ──┴─→ [AR Arbiter] ──┬─→ [Mux] ──→ ddr_s_axi_ar (64b)
                 (per slave)     │
                                 ├─→ [Mux] ──→ sram_s_axi_ar (32b)
                                 │   ↑ Width convert
                                 └─→ [Mux] ──→ apb_paddr
                                     ↑ Protocol convert

Response Path (ID-based routing):

ddr_s_axi_r ──┐
sram_s_axi_r ─┤
apb_prdata ───┴─→ [Demux by bridge_id] ──┬─→ cpu_64b_r
                   ↑                       ├─→ gpu_64b_r
                   │                       └─→ dma_64b_r
                   └─ bridge_cam.sv lookup
```

**Arbitration Per Slave:**
- Each slave has independent AW and AR arbiters
- Round-robin policy (fair access, no starvation)
- Grant locked during burst (until xlast)
- Response channels routed by bridge_id (no arbitration needed)

---

#### Signal Flow: End-to-End

**Read Transaction Example (CPU → DDR):**

```
1. CPU issues read request:
   cpu_m_axi_araddr = 0x10000000
   cpu_m_axi_arlen = 7  (8-beat burst)

2. CPU Adapter processes:
   - Address decoder: 0x10000000 is in DDR range
     → slave_select_ar[DDR] = 1
   - Width converter: 32-bit → 64-bit (if needed)
   - Bridge ID injector: Adds bridge_id=0 (CPU's unique ID)
   - Outputs: cpu_master_64b_ar (to crossbar)

3. Crossbar processes:
   - AR arbiter (DDR slave): Grants to CPU master
   - AR mux: Routes cpu_master_64b_ar → ddr_s_axi_ar
   - Width converter: 64-bit → 64-bit (no conversion)
   - Transaction reaches DDR controller

4. DDR responds:
   - DDR sends 8 beats: r0, r1, ..., r7
   - Each beat has: rid = original ARID, bridge_id = 0
   
5. Crossbar returns response:
   - R demux: Looks up bridge_id=0 in CAM
     → Maps to CPU master
   - Routes: ddr_s_axi_r → cpu_master_64b_r

6. CPU Adapter returns:
   - Width converter: 64-bit → 32-bit (if needed)
   - External: cpu_m_axi_r (8 beats delivered)
```

**Total Latency:** 2-3 cycles (adapter + crossbar + mux)

---

#### Address Decode Logic

**Per-Master, Per-Transaction:**

```systemverilog
// Example: 3 slaves with different address ranges
always_comb begin
    slave_select_ar = '0;  // Default: no slave selected
    
    if (cpu_m_axi_arvalid) begin
        // Slave 0: DDR (0x00000000 - 0x3FFFFFFF)
        if (cpu_m_axi_araddr >= 64'h00000000 && 
            cpu_m_axi_araddr < 64'h40000000)
            slave_select_ar[0] = 1'b1;
        
        // Slave 1: SRAM (0x40000000 - 0x4FFFFFFF)
        if (cpu_m_axi_araddr >= 64'h40000000 && 
            cpu_m_axi_araddr < 64'h50000000)
            slave_select_ar[1] = 1'b1;
        
        // Slave 2: APB (0x60000000 - 0x6000FFFF)
        if (cpu_m_axi_araddr >= 64'h60000000 && 
            cpu_m_axi_araddr < 64'h60010000)
            slave_select_ar[2] = 1'b1;
    end
    
    // If no match: DECERR will be returned
end
```

**Key Properties:**
- Combinatorial (zero latency)
- Per-channel (AW and AR independent)
- Validates address ranges at generation time
- Returns DECERR for unmapped addresses

---

#### Arbitration Strategy

**Per-Slave Round-Robin:**

```systemverilog
// AR channel arbiter for DDR slave
logic [NUM_MASTERS-1:0] ar_grant_ddr;
logic [NUM_MASTERS-1:0] ar_request_ddr;
logic [$clog2(NUM_MASTERS)-1:0] ar_grant_idx;

// Collect requests from all masters
assign ar_request_ddr = {
    dma_slave_select_ar[DDR] & dma_64b_arvalid,
    gpu_slave_select_ar[DDR] & gpu_64b_arvalid,
    cpu_slave_select_ar[DDR] & cpu_64b_arvalid
};

// Round-robin arbiter
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        ar_grant_idx <= '0;
    end else if (|ar_request_ddr && ddr_s_axi_arready) begin
        // Grant next requester in round-robin order
        ar_grant_idx <= next_grant(ar_grant_idx, ar_request_ddr);
    end
    // Hold grant during burst (until RLAST)
end

// One-hot grant signal
assign ar_grant_ddr = (1 << ar_grant_idx);
```

**Arbitration Properties:**
- Fair access (no master starves)
- Grant locked during burst (AWLEN/ARLEN)
- Independent per slave (no head-of-line blocking)
- Separate AW and AR arbitration (concurrent read/write)

---

#### Bridge ID Tracking

**Purpose:** Route responses back to correct master in multi-master systems

**Mechanism:**

```
Master Issues Request:
    Original AXI ID: 0x5
    Bridge adds: bridge_id=2 (DMA master's unique ID)
    → Sent to slave with both IDs

Slave Responds:
    Returns: RID=0x5, bridge_id=2
    → Crossbar CAM lookup: bridge_id=2 maps to DMA master
    → Response routed to DMA master
    → DMA sees: RID=0x5 (original ID preserved)
```

**CAM (Content Addressable Memory) in Slave Adapters:**

```systemverilog
// Per-slave CAM tracks: {trans_id, bridge_id} → master_id
logic [TRANS_ID_WIDTH-1:0] cam_trans_id [CAM_DEPTH-1:0];
logic [BRIDGE_ID_WIDTH-1:0] cam_bridge_id [CAM_DEPTH-1:0];
logic [MASTER_ID_WIDTH-1:0] cam_master_id [CAM_DEPTH-1:0];

// On AW/AR transaction: Store mapping
// On B/R response: Lookup master from bridge_id
```

**See Chapter 2.6: bridge_cam.sv** for detailed CAM implementation.

---

#### Width Conversion Strategy

**Adapter Level (Master → Internal 64-bit):**

```
32-bit master → Upsize to 64-bit
    - Replicate data for writes
    - Adjust WSTRB for byte enables
    - Multiple internal beats per master beat (reads)

64-bit master → Direct connection
    - Zero conversion overhead
    - Pass-through logic

128-bit master → Downsize to 64-bit
    - Split into multiple 64-bit beats
    - Manage beat counters
```

**Crossbar Level (Internal 64-bit → Slave):**

```
64-bit → 32-bit slave: Downsize
    - Split 64-bit beats into two 32-bit beats
    - Manage beat sequencing

64-bit → 64-bit slave: Direct
    - Zero overhead

64-bit → 128-bit slave: Upsize
    - Combine two 64-bit beats
    - Buffer and align
```

**Design Trade-off:**
- Single 64-bit internal path simplifies crossbar
- Width conversion pushed to edges (adapters and slave interfaces)
- Most common widths (32, 64) have minimal conversion

---

#### Protocol Conversion (AXI4 → APB)

**When Needed:** APB slave in mixed-protocol system

**Conversion Adapter (Auto-Inserted):**

```
AXI4 Request → APB Translation:
    AW/W channels → PADDR/PWDATA/PWRITE
    AR channel → PADDR/PWRITE=0
    
    Wait for PREADY
    
APB Response → AXI4 Translation:
    PRDATA → RDATA (reads)
    PSLVERR → RRESP/BRESP
```

**Limitations (APB Protocol):**
- No burst support (AWLEN/ARLEN must be 0)
- Single-beat transactions only
- Generator validates APB slaves don't receive bursts

**See Chapter 2.5: Protocol Converters** for detailed implementation.

---

#### Clock and Reset Architecture

**Single Clock Domain (Default):**

```systemverilog
module bridge_top (
    input logic aclk,      // All logic uses this clock
    input logic aresetn,   // Active-low async reset
    // ...
);
```

**All components (adapters, crossbar, converters) share:**
- Same clock: `aclk`
- Same reset: `aresetn`
- Simplest configuration, lowest latency

**Multiple Clock Domains (Future Enhancement):**
- CDC at adapter inputs (master-side clock)
- CDC at slave outputs (slave-side clocks)
- Handshake synchronization
- Adds 2-4 cycles latency per crossing

**Reset Behavior:**
- All registers clear to known state
- Arbiters reset to master 0 priority
- CAMs clear all entries
- Skid buffers flush
- Ready for transactions after 10 cycles

---

#### Performance Paths

**Critical Timing Paths:**

1. **Address Decode → Arbiter → Mux**
   - Combinatorial address comparison
   - Arbiter grant logic
   - Mux selection
   - Target: 1 cycle

2. **Adapter Width Conversion**
   - Data path multiplexing
   - Beat counter logic
   - Target: 1 cycle

3. **CAM Lookup → Response Demux**
   - Parallel CAM search
   - Master selection mux
   - Target: 1 cycle

**Optimization Strategies:**
- Register arbiter grants (1 cycle latency)
- Pipeline address decode (if needed)
- Add skid buffers (decouple timing)
- Optional FIFOs for deep pipeline (>400 MHz)

**See Chapter 6: Performance** for detailed analysis and pipeline options.

---

#### Scalability Considerations

**Small Systems (2×2, 4×4):**
- Minimal resource usage (~2-5K LUTs)
- High Fmax (400+ MHz)
- Simple routing

**Medium Systems (8×8, 16×16):**
- Moderate resources (~10-20K LUTs)
- Good Fmax (300-350 MHz)
- May need pipeline stages

**Large Systems (32×256):**
- Significant resources (~50-100K LUTs)
- Requires pipelining (250-300 MHz)
- Consider hierarchical crossbar
- Address decode becomes complex

**Recommendation:** For >16 masters or >32 slaves, consider hierarchical topology with multiple bridge instances.

---

#### Design Trade-offs

| Decision | Pros | Cons |
|----------|------|------|
| **64-bit Internal Path** | Simple logic, common width | Conversion for <64-bit |
| **Per-Master Adapters** | Independent paths, parallel decode | More resources |
| **Round-Robin Arbitration** | Fair, no starvation | Not QoS-aware |
| **Bridge ID Tracking** | Supports OOO, multi-master | CAM resources per slave |
| **Hard Limits (ID/Addr)** | Simpler logic, faster | Less flexible |
| **Channel-Specific Masters** | Resource optimization | Config complexity |

---

#### Future Architecture Enhancements

**Planned:**
- Hierarchical crossbar for >32 masters
- Weighted arbitration (QoS support)
- Multiple internal data widths (configurable)
- Deeper pipeline stages (>400 MHz target)
- Optional CDC at boundaries

**Under Consideration:**
- ACE protocol support (cache coherency)
- AXI4-Lite variant (register-only crossbar)
- Performance monitoring integration
- Dynamic power gating per path

---

**Next:** [Chapter 1.3 - Clocks and Reset](03_clocks_and_reset.md)
