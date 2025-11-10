# Bridge Signal Naming Plan

**Version:** 2.0
**Date:** 2025-11-08
**Purpose:** Comprehensive signal naming convention through entire bridge datapath
**Status:** APPROVED - Ready for Implementation

---

## Table of Contents

1. [Architecture Overview](#architecture-overview)
2. [Key Concepts: TID vs BID](#key-concepts-tid-vs-bid)
3. [Naming Principles](#naming-principles)
4. [Signal Naming by Stage](#signal-naming-by-stage)
5. [CAM/FIFO Transaction Tracking](#camfifo-transaction-tracking)
6. [Complete Example: 2x2 Bridge](#complete-example-2x2-bridge)
7. [Width Adaptation Signals](#width-adaptation-signals)
8. [APB Protocol Signals](#apb-protocol-signals)
9. [Implementation Notes](#implementation-notes)

---

## Architecture Overview

### Bridge Datapath Stages

```
┌─────────────────┐
│ External Master │ (e.g., CPU, DMA)
│   Interface     │
└────────┬────────┘
         │ Stage 1: External Master Interface
         │ Signals: <master>_axi_<channel><signal>
         │ TID: Passes through (e.g., cpu_axi_awid = 0x5)
         │ Direction: INPUT to bridge
         │
         ▼
┌─────────────────────────────────────────────┐
│  Master Adapter Module                      │
│  (<master>_master_adapter.sv)               │
│  Parameter: BRIDGE_ID (fixed per master)    │
│                                             │
│  ┌───────────────────────────────────────┐  │
│  │ Timing Wrapper (axi4_slave_wr/rd)     │  │
│  └────────┬──────────────────────────────┘  │
│           │ Stage 2: Post-Timing (FUB)
│           │ Signals: fub_axi_<channel><signal>
│           │ TID: Passthrough (fub_axi_awid = 0x5)
│           │
│           ▼
│  ┌───────────────────────────────────────┐  │
│  │ Address Decode                        │  │
│  └────────┬──────────────────────────────┘  │
│           │ Stage 3: Decode Outputs
│           │ Signals: slave_select_aw[N]
│           │
│           ▼
│  ┌───────────────────────────────────────┐  │
│  │ Width Adaptation (per-width paths)    │  │
│  │ - Decode + conversion logic           │  │
│  │ - ALL complexity in master adapter    │  │
│  └────────┬──────────────────────────────┘  │
│           │ Stage 4: Adapter Outputs
│           │ TID: <master>_<W>b_awid = 0x5
│           │ BID: <master>_<W>b_bid = BRIDGE_ID
└───────────┼─────────────────────────────────┘
            │
            ▼
┌─────────────────────────────────────────────┐
│    Crossbar Module                          │
│ (<bridge_name>_xbar.sv)                     │
│                                             │
│  ┌───────────────────────────────────────┐  │
│  │ Request Routing (Combinational)       │  │
│  │ - OR-based mux of master paths        │  │
│  │ - TID passthrough to slave            │  │
│  └────────┬──────────────────────────────┘  │
│           │ Stage 5a: To Slave
│           │ TID: <slave>_xb_awid = 0x5
│           │
│  ┌────────▼──────────────────────────────┐  │
│  │ CAM/FIFO (Per-Slave, Per-Channel)    │  │
│  │ - bridge_cam (if OOO)                 │  │
│  │ - gaxi_fifo (if in-order)             │  │
│  │                                        │  │
│  │ Stores: TID → BID mapping             │  │
│  │   allocate_tag = TID (0x5)            │  │
│  │   allocate_data = BID (BRIDGE_ID)     │  │
│  │                                        │  │
│  │ Returns: BID for routing              │  │
│  │   deallocate_tag = TID (0x5)          │  │
│  │   deallocate_data = BID (0)           │  │
│  └────────┬──────────────────────────────┘  │
│           │ Stage 5b: CAM Lookup
│           │
│  ┌────────▼──────────────────────────────┐  │
│  │ Response Muxing (Based on BID)        │  │
│  │ - Route to master[BID]                │  │
│  │ - TID passthrough to master           │  │
│  └────────┬──────────────────────────────┘  │
│           │ Stage 6: Back to Adapter
│           │ TID: <master>_<W>b_bid_tid = 0x5
└───────────┼─────────────────────────────────┘
            │
            ▼
┌─────────────────────────────────────────────┐
│  Slave Adapter Module                       │
│  (<slave>_slave_adapter.sv)                 │
│                                             │
│  ┌───────────────────────────────────────┐  │
│  │ Timing Wrapper ONLY                   │  │
│  │ (axi4_master_wr/rd)                   │  │
│  │ - Skid buffer for timing              │  │
│  │ - NO decode, NO conversion            │  │
│  └────────┬──────────────────────────────┘  │
│           │ Stage 7: To External Slave
│           │ TID: <slave>_axi_awid = 0x5
└───────────┼─────────────────────────────────┘
            │
            ▼
┌─────────────────┐
│ External Slave  │ (e.g., DDR, SRAM)
│   Interface     │
└─────────────────┘
  Stage 7: External Slave Interface
  TID: Unchanged through entire bridge
  Direction: OUTPUT from bridge
```

---

## Key Concepts: TID vs BID

### Transaction ID (TID)

**Definition:** AXI4 transaction identifier that passes through the bridge **unchanged**.

**Purpose:** Allows masters to track their own transactions, enables out-of-order responses.

**Flow:** `master → bridge → slave → bridge → master` (same TID value throughout)

**Examples:**
```systemverilog
// Master sends request
cpu_axi_awid = 4'h5  // TID from CPU

// Through bridge (UNCHANGED)
fub_axi_awid = 4'h5  // Post-timing
cpu_32b_awid = 4'h5  // After width conversion
ddr_xb_awid = 4'h5   // To crossbar
ddr_axi_awid = 4'h5  // To slave

// Slave responds (SAME TID)
ddr_axi_bid = 4'h5   // From slave
ddr_xb_bid = 4'h5    // From crossbar
cpu_32b_bid_tid = 4'h5  // Back to master adapter
cpu_axi_bid = 4'h5   // Back to CPU (UNCHANGED)
```

### Bridge ID (BID)

**Definition:** Fixed parameter per master adapter that identifies which master a transaction originated from.

**Purpose:** Enables crossbar to route responses back to the correct master.

**Assignment:** Set via `BRIDGE_ID` parameter during instantiation:
- Master 0 (CPU): `BRIDGE_ID = 0`
- Master 1 (DMA): `BRIDGE_ID = 1`
- Master 2 (GPU): `BRIDGE_ID = 2`
- etc.

**Storage:** CAM/FIFO stores `TID → BID` mapping per slave

**Examples:**
```systemverilog
// Master adapter instantiation
cpu_master_adapter #(
    .BRIDGE_ID(0)  // ← CPU is always BID=0
) u_cpu_adapter (...);

dma_master_adapter #(
    .BRIDGE_ID(1)  // ← DMA is always BID=1
) u_dma_adapter (...);

// Master adapter outputs (constant BID)
assign cpu_32b_bid = 2'd0;  // BID is fixed parameter
assign dma_64b_bid = 2'd1;  // BID is fixed parameter

// CAM stores TID→BID mapping
bridge_cam u_ddr_aw_cam (
    .allocate_tag(ddr_xb_awid),    // TID = 0x5 (from CPU)
    .allocate_data(cpu_32b_bid),   // BID = 0 (CPU's BRIDGE_ID)
    ...
    .deallocate_tag(ddr_xb_bid),   // TID = 0x5 (slave response)
    .deallocate_data(ddr_b_bid)    // BID = 0 (route to CPU)
);
```

### TID vs BID Comparison

| Aspect | TID (Transaction ID) | BID (Bridge ID) |
|--------|---------------------|-----------------|
| **Purpose** | Track individual transactions | Identify source master |
| **Scope** | Per transaction | Per master |
| **Value** | Variable (0x0 - 0xF) | Fixed parameter (0, 1, 2, ...) |
| **Width** | ID_WIDTH (typically 4 bits) | log2(NUM_MASTERS) (2-3 bits) |
| **Changes?** | NO - passes through unchanged | NO - constant per master |
| **AXI4 Signal** | awid, arid, bid, rid | Not part of AXI4 spec |
| **Storage** | CAM TAG field | CAM DATA field |
| **Example** | `cpu_axi_awid = 0x5` | `BRIDGE_ID = 0` |

### Why We Need Both

**Problem:** Multiple masters can send transactions with the **same TID** value:
```
CPU sends:  TID=0x5
DMA sends:  TID=0x5  (same TID, different master!)
```

**Solution:** CAM stores `(TID, BID)` pairs:
```
CAM Table for DDR slave:
┌─────┬─────┐
│ TID │ BID │
├─────┼─────┤
│ 0x5 │  0  │  ← From CPU (first allocation)
│ 0x5 │  1  │  ← From DMA (Mode 2: allows duplicates)
└─────┴─────┘
```

**Response Routing:** When slave responds with `bid=0x5`:
- CAM lookup: `TID=0x5` → returns oldest `BID=0` (FIFO order)
- Route to master[0] (CPU)
- Next response with `bid=0x5` → returns `BID=1` (DMA)

### Key Insight

**TID is for the master's bookkeeping.**
**BID is for the bridge's bookkeeping.**

Both are necessary for correct operation in multi-master systems with out-of-order slaves.

---

## Naming Principles

### Principle 1: Protocol Identifier

**All AXI4 signals include `_axi_` in the name for protocol identification**

Rationale:
- Easy to identify AXI4 signals when debugging waveforms
- Distinguishes from APB (`_apb_`) or internal control signals
- Consistent with industry practice

Examples:
```systemverilog
m0_axi_awaddr     // Master 0, AXI4 protocol, AW channel, addr signal
s0_axi_rdata      // Slave 0, AXI4 protocol, R channel, data signal
cpu_apb_paddr     // APB peripheral, APB protocol, paddr signal
```

### Principle 2: Width Identifiers for Multi-Width Paths

**Internal signals include width suffix when master connects to multiple slave widths**

Format: `<master>_<width>b_<channel><signal>`

Rationale:
- Master adapter generates N output paths (one per unique slave width)
- Width suffix identifies which path the signal belongs to
- Crossbar routes based on width and slave selection

Examples:
```systemverilog
cpu_32b_awaddr    // CPU adapter output, 32-bit path
cpu_64b_awaddr    // CPU adapter output, 64-bit path
cpu_512b_wdata    // CPU adapter output, 512-bit path
```

### Principle 3: Stage Prefixes

**Internal signals use stage-specific prefixes to indicate location in datapath**

| Stage | Prefix | Example | Meaning |
|-------|--------|---------|---------|
| Post-Timing | `fub_axi_` | `fub_axi_awaddr` | After timing wrapper (FUB = Functional Unit Block) |
| Crossbar Internal | `<slave>_xb_` | `ddr_xb_awaddr` | Internal to crossbar (xb = crossbar) |
| Width Path | `<master>_<width>b_` | `cpu_32b_awaddr` | Adapter output, specific width path |

### Principle 4: No Direction Prefix in Signal Names

**Signal names do NOT include `m_` or `s_` direction prefixes**

Rationale:
- Port name already identifies the endpoint (m0, s0, cpu, ddr)
- Direction prefix is redundant
- Cleaner signal names

Wrong:
```systemverilog
m0_m_axi_awaddr   // ❌ Redundant "m_" direction prefix
s0_s_axi_rdata    // ❌ Redundant "s_" direction prefix
```

Correct:
```systemverilog
m0_axi_awaddr     // ✅ Port name "m0" is sufficient
s0_axi_rdata      // ✅ Port name "s0" is sufficient
```

---

## Signal Naming by Stage

### Stage 1: External Master Interface

**Location:** Top-level bridge module ports
**Purpose:** Receive transactions from external AXI4 masters
**Direction:** INPUT to bridge (bridge acts as slave)

**Naming Convention:**
```
<master_name>_axi_<channel><signal>
```

**Examples:**
```systemverilog
// Master 0 (config: name="m0", prefix="m0_")
input  logic [31:0]  m0_axi_awaddr,
input  logic         m0_axi_awvalid,
output logic         m0_axi_awready,
input  logic [63:0]  m0_axi_wdata,
input  logic         m0_axi_wvalid,
output logic         m0_axi_wready,
output logic [3:0]   m0_axi_bid,
output logic [1:0]   m0_axi_bresp,
output logic         m0_axi_bvalid,
input  logic         m0_axi_bready,

// CPU master (config: name="cpu", prefix="cpu_")
input  logic [31:0]  cpu_axi_awaddr,
input  logic         cpu_axi_awvalid,
output logic         cpu_axi_awready,
```

**Key Points:**
- Uses `<master_name>` from config (NOT the full prefix)
- Always includes `_axi_` protocol identifier
- Direction INVERTED from master perspective (bridge receives, so INPUT)

---

### Stage 2: Post-Timing Wrapper (FUB Signals)

**Location:** Inside master adapter, after axi4_slave_wr/rd timing wrapper
**Purpose:** Buffered signals for timing closure
**Direction:** Internal to adapter module

**Naming Convention:**
```
fub_axi_<channel><signal>
```

**Examples:**
```systemverilog
// Inside cpu_adapter.sv
logic [31:0]  fub_axi_awaddr;
logic         fub_axi_awvalid;
logic         fub_axi_awready;
logic [63:0]  fub_axi_wdata;
logic         fub_axi_wvalid;
logic         fub_axi_wready;
```

**Key Points:**
- Generic prefix `fub_` (Functional Unit Block) indicates post-timing stage
- Used as input to address decode logic
- Same width as external master interface
- Internal to adapter only (not exposed outside)

---

### Stage 3: Address Decode Outputs

**Location:** Inside master adapter, output from decode logic
**Purpose:** One-hot slave selection based on address ranges
**Direction:** Internal control signals

**Naming Convention:**
```
slave_select_aw[NUM_SLAVES]  // Write address channel decode
slave_select_ar[NUM_SLAVES]  // Read address channel decode
```

**Examples:**
```systemverilog
// Inside cpu_adapter.sv
logic [1:0] slave_select_aw;  // 2 slaves
logic [1:0] slave_select_ar;  // 2 slaves

// Decode logic
always_comb begin
    slave_select_aw = '0;
    if (fub_axi_awaddr <= 32'h7FFF_FFFF)
        slave_select_aw[0] = 1'b1;  // ddr
    else if (fub_axi_awaddr >= 32'h8000_0000)
        slave_select_aw[1] = 1'b1;  // sram
end
```

**Key Points:**
- One-hot encoding (only one bit set at a time)
- Separate for AW and AR channels (independent read/write paths)
- Used to control width adaptation and crossbar routing

---

### Stage 4: Adapter Output to Crossbar (Width Paths)

**Location:** Output ports of master adapter module
**Purpose:** Per-width adapted signals routed to crossbar
**Direction:** OUTPUT from adapter to crossbar

**Naming Convention:**
```
<master_name>_<width>b_<channel><signal>
```

**Examples:**
```systemverilog
// cpu_adapter.sv outputs (CPU is 64b, connects to 32b and 64b slaves)

// 32b width path (for 32b slaves)
output axi4_aw_t   cpu_32b_aw,
output logic       cpu_32b_awvalid,
input  logic       cpu_32b_awready,
output axi4_w_t    cpu_32b_w,
output logic       cpu_32b_wvalid,
input  logic       cpu_32b_wready,
input  axi4_b_t    cpu_32b_b,
input  logic       cpu_32b_bvalid,
output logic       cpu_32b_bready,

// 64b width path (for 64b slaves - direct passthrough)
output axi4_aw_t   cpu_64b_aw,
output logic       cpu_64b_awvalid,
input  logic       cpu_64b_awready,
output axi4_w_t    cpu_64b_w,
output logic       cpu_64b_wvalid,
input  logic       cpu_64b_wready,
input  axi4_b_t    cpu_64b_b,
input  logic       cpu_64b_bvalid,
output logic       cpu_64b_bready,
```

**Key Points:**
- Width suffix (`32b`, `64b`, `512b`) identifies path
- One path per unique slave width connected to this master
- Direct passthrough if master width matches slave width
- Width conversion if master width != slave width

---

### Stage 5: Crossbar Internal Routing

**Location:** Inside crossbar module, routing request to slaves
**Purpose:** Combine multiple master paths to single slave interface
**Direction:** Internal to crossbar

**Naming Convention:**
```
<slave_name>_xb_<channel><signal>
```

**Examples:**
```systemverilog
// Inside bridge_2x2_rw_xbar.sv

// DDR slave (32b)
logic [31:0]  ddr_xb_awaddr;
logic         ddr_xb_awvalid;
logic         ddr_xb_awready;
logic [31:0]  ddr_xb_wdata;
logic         ddr_xb_wvalid;
logic         ddr_xb_wready;

// Combinational routing (OR-based muxing)
assign ddr_xb_awaddr =
    (cpu_slave_select_aw[0] ? cpu_32b_aw.addr : '0) |
    (dma_slave_select_aw[0] ? dma_32b_aw.addr : '0);

assign ddr_xb_awvalid =
    (cpu_slave_select_aw[0] ? cpu_32b_awvalid : '0) |
    (dma_slave_select_aw[0] ? dma_32b_awvalid : '0);
```

**Key Points:**
- `_xb_` suffix indicates crossbar-internal signal
- OR-based combining (safe because one-hot selection)
- Same width as target slave
- Internal only (not exposed outside crossbar)

---

### Stage 6: Crossbar Response Muxing

**Location:** Inside crossbar module, returning responses to masters
**Purpose:** Route slave responses back to correct master width path
**Direction:** From crossbar to adapter (reverse path)

**Naming Convention:**
```
<master_name>_<width>b_<channel><signal>  (same as Stage 4, reverse direction)
```

**Examples:**
```systemverilog
// Inside bridge_2x2_rw_xbar.sv

// Response routing for CPU 32b path
assign cpu_32b_awready =
    (cpu_slave_select_aw[0] ? ddr_xb_awready : '0) |
    (cpu_slave_select_aw[1] ? sram_xb_awready : '0);

assign cpu_32b_bvalid =
    (cpu_slave_select_aw[0] ? ddr_xb_bvalid : '0) |
    (cpu_slave_select_aw[1] ? sram_xb_bvalid : '0);

assign cpu_32b_b =
    (cpu_slave_select_aw[0] ? ddr_xb_b : '0) |
    (cpu_slave_select_aw[1] ? sram_xb_b : '0);
```

**Key Points:**
- Same signal names as adapter outputs (Stage 4)
- Reverse direction (crossbar drives, adapter receives)
- OR-based combining using same select signals
- Matches width of master path

---

### Stage 7: External Slave Interface

**Location:** Top-level bridge module ports
**Purpose:** Drive transactions to external AXI4 slaves
**Direction:** OUTPUT from bridge (bridge acts as master)

**Naming Convention:**
```
<slave_name>_axi_<channel><signal>
```

**Examples:**
```systemverilog
// Slave 0: DDR controller (config: name="s0", prefix="s0_")
output logic [31:0]  s0_axi_awaddr,
output logic         s0_axi_awvalid,
input  logic         s0_axi_awready,
output logic [31:0]  s0_axi_wdata,
output logic         s0_axi_wvalid,
input  logic         s0_axi_wready,
input  logic [3:0]   s0_axi_bid,
input  logic [1:0]   s0_axi_bresp,
input  logic         s0_axi_bvalid,
output logic         s0_axi_bready,

// Slave: DDR controller (config: name="ddr", prefix="ddr_")
output logic [31:0]  ddr_axi_awaddr,
output logic         ddr_axi_awvalid,
input  logic         ddr_axi_awready,
```

**Key Points:**
- Uses `<slave_name>` from config (NOT the full prefix)
- Always includes `_axi_` protocol identifier
- Direction FROM bridge perspective (bridge drives, so OUTPUT)
- Direct connection from crossbar internal `_xb_` signals

---

## Complete Example: 2x2 Bridge

### Configuration

```toml
[bridge]
name = "bridge_2x2_rw"

[[bridge.masters]]
name = "m0"
prefix = "m0_"
data_width = 32
channels = "rw"

[[bridge.masters]]
name = "m1"
prefix = "m1_"
data_width = 64
channels = "rw"

[[bridge.slaves]]
name = "s0"
prefix = "s0_"
data_width = 32
base_addr = "0x00000000"
addr_range = "0x10000000"

[[bridge.slaves]]
name = "s1"
prefix = "s1_"
data_width = 64
base_addr = "0x10000000"
addr_range = "0x10000000"

[connectivity]
m0 = ["s0", "s1"]  # M0 connects to both slaves (needs 32b and 64b paths)
m1 = ["s0", "s1"]  # M1 connects to both slaves (needs 32b and 64b paths)
```

### Signal Flow: M0 Write to S0 (32b → 32b, direct path)

```
1. External Master Interface (Stage 1)
   m0_axi_awaddr = 0x0000_1000  (INPUT to bridge)
   m0_axi_awvalid = 1
   m0_axi_awready = 1           (OUTPUT from bridge)

2. Post-Timing Wrapper (Stage 2, inside m0_adapter)
   fub_axi_awaddr = 0x0000_1000 (buffered copy)
   fub_axi_awvalid = 1

3. Address Decode (Stage 3, inside m0_adapter)
   slave_select_aw[0] = 1       (s0 selected)
   slave_select_aw[1] = 0

4. Width Adaptation (Stage 4, m0_adapter outputs)
   m0_32b_aw.addr = 0x0000_1000 (direct path, no conversion)
   m0_32b_awvalid = 1
   m0_32b_awready = 1           (from crossbar)

5. Crossbar Routing (Stage 5, inside xbar)
   s0_xb_awaddr = m0_32b_aw.addr (OR with other masters)
   s0_xb_awvalid = m0_32b_awvalid

6. Response Muxing (Stage 6, inside xbar)
   m0_32b_awready = s0_xb_awready (OR with other slaves)

7. External Slave Interface (Stage 7)
   s0_axi_awaddr = 0x0000_1000  (OUTPUT from bridge)
   s0_axi_awvalid = 1
   s0_axi_awready = 1           (INPUT to bridge)
```

### Signal Flow: M1 Write to S0 (64b → 32b, needs conversion)

```
1. External Master Interface (Stage 1)
   m1_axi_awaddr = 0x0000_2000  (INPUT to bridge)
   m1_axi_awvalid = 1
   m1_axi_wdata = 64'hDEADBEEF_CAFEBABE

2. Post-Timing Wrapper (Stage 2, inside m1_adapter)
   fub_axi_awaddr = 0x0000_2000
   fub_axi_wdata = 64'hDEADBEEF_CAFEBABE

3. Address Decode (Stage 3, inside m1_adapter)
   slave_select_aw[0] = 1       (s0 selected, 32b slave)
   slave_select_aw[1] = 0

4. Width Adaptation (Stage 4, m1_adapter outputs)
   // M1 adapter converts 64b → 32b for s0
   m1_32b_aw.addr = 0x0000_2000
   m1_32b_awvalid = 1
   m1_32b_awlen = orig_len * 2  (burst split)
   m1_32b_w.data = 32'hCAFEBABE (first beat)
   m1_32b_wvalid = 1

5. Crossbar Routing (Stage 5, inside xbar)
   s0_xb_awaddr = m1_32b_aw.addr
   s0_xb_wdata = m1_32b_w.data

7. External Slave Interface (Stage 7)
   s0_axi_awaddr = 0x0000_2000
   s0_axi_wdata = 32'hCAFEBABE (first beat)
   // Second beat: 32'hDEADBEEF (from converter state machine)
```

---

## Width Adaptation Signals

### Multi-Width Master Example

**Scenario:** CPU master (64b) connects to:
- DDR slave (32b) → requires 64b→32b conversion
- SRAM slave (64b) → direct connection
- Flash slave (128b) → requires 64b→128b conversion

**Adapter Output Signals:**

```systemverilog
// cpu_adapter.sv module ports

// 32b width path (for DDR)
output axi4_aw_t   cpu_32b_aw,
output logic       cpu_32b_awvalid,
input  logic       cpu_32b_awready,
output axi4_w_t    cpu_32b_w,
output logic       cpu_32b_wvalid,
input  logic       cpu_32b_wready,
input  axi4_b_t    cpu_32b_b,
input  logic       cpu_32b_bvalid,
output logic       cpu_32b_bready,

// 64b width path (for SRAM - direct)
output axi4_aw_t   cpu_64b_aw,
output logic       cpu_64b_awvalid,
input  logic       cpu_64b_awready,
output axi4_w_t    cpu_64b_w,
output logic       cpu_64b_wvalid,
input  logic       cpu_64b_wready,
input  axi4_b_t    cpu_64b_b,
input  logic       cpu_64b_bvalid,
output logic       cpu_64b_bready,

// 128b width path (for Flash)
output axi4_aw_t   cpu_128b_aw,
output logic       cpu_128b_awvalid,
input  logic       cpu_128b_awready,
output axi4_w_t    cpu_128b_w,
output logic       cpu_128b_wvalid,
input  logic       cpu_128b_wready,
input  axi4_b_t    cpu_128b_b,
input  logic       cpu_128b_bvalid,
output logic       cpu_128b_bready,

// Decode outputs
output logic [2:0] slave_select_aw,  // One-hot: [flash, sram, ddr]
output logic [2:0] slave_select_ar,
```

**Width Selection Logic (inside adapter):**

```systemverilog
// Route to correct width path based on decode
always_comb begin
    cpu_32b_awvalid = slave_select_aw[0] & fub_axi_awvalid;  // DDR
    cpu_64b_awvalid = slave_select_aw[1] & fub_axi_awvalid;  // SRAM
    cpu_128b_awvalid = slave_select_aw[2] & fub_axi_awvalid; // Flash
end
```

---

## APB Protocol Signals

### APB Slave Naming

**Location:** Top-level bridge module ports
**Purpose:** Drive transactions to external APB slaves
**Direction:** OUTPUT from bridge (bridge acts as APB master)

**Naming Convention:**
```
<slave_name>_apb_<signal>
```

**Note:** APB signals do NOT include channel prefix (no AW/W/B/AR/R channels)

**Examples:**
```systemverilog
// APB Peripheral 0 (config: name="apb0", prefix="apb0_")
output logic [31:0]  apb0_apb_paddr,
output logic         apb0_apb_psel,
output logic         apb0_apb_penable,
output logic         apb0_apb_pwrite,
output logic [31:0]  apb0_apb_pwdata,
input  logic [31:0]  apb0_apb_prdata,
input  logic         apb0_apb_pready,
input  logic         apb0_apb_pslverr,

// APB Peripheral (config: name="gpio", prefix="gpio_")
output logic [31:0]  gpio_apb_paddr,
output logic         gpio_apb_psel,
```

### AXI4-to-APB Converter Internal Signals

**Location:** Inside APB shim/converter module
**Purpose:** Convert AXI4 crossbar output to APB protocol

**Input from Crossbar:**
```systemverilog
// APB shim receives AXI4 from crossbar
input  axi4_aw_t   apb0_xb_aw,
input  logic       apb0_xb_awvalid,
output logic       apb0_xb_awready,
input  axi4_w_t    apb0_xb_w,
input  logic       apb0_xb_wvalid,
output logic       apb0_xb_wready,
output axi4_b_t    apb0_xb_b,
output logic       apb0_xb_bvalid,
input  logic       apb0_xb_bready,
```

**Output to External APB:**
```systemverilog
// APB shim drives external APB slave
output logic [31:0]  apb0_apb_paddr,
output logic         apb0_apb_psel,
output logic         apb0_apb_penable,
output logic         apb0_apb_pwrite,
output logic [31:0]  apb0_apb_pwdata,
input  logic [31:0]  apb0_apb_prdata,
input  logic         apb0_apb_pready,
input  logic         apb0_apb_pslverr,
```

---

## Implementation Notes

### SignalNaming Module Updates Required

**File:** `bridge_pkg/signal_naming.py`

**Function:** `axi4_signal_name()`

Current (FIXED):
```python
def axi4_signal_name(port_name: str, direction: Direction,
                     channel: AXI4Channel, signal: str) -> str:
    # No direction prefix (m/s) in signal names
    return f"{port_name}_axi_{channel.value}{signal}"
```

Result: `m0_axi_awaddr`, `s0_axi_rdata` ✅

**Function:** `apb_signal_name()`

Current:
```python
def apb_signal_name(port_name: str, signal: str) -> str:
    return f"{port_name}_{signal}"
```

**Needs Update:**
```python
def apb_signal_name(port_name: str, signal: str) -> str:
    # Add _apb_ protocol identifier for consistency
    return f"{port_name}_apb_{signal}"
```

Result: `apb0_apb_paddr`, `gpio_apb_psel` ✅

### Direction Inversion

**Master Ports (Bridge receives from external master):**
```python
# In SignalInfo database for AXI4_MASTER_SIGNALS:
# Direction is from MASTER's perspective, but bridge is SLAVE
# So INVERT direction when generating bridge ports

if port_type == "master":
    # Master drives awaddr → Bridge receives awaddr → INPUT
    if sig_info.direction == PortDirection.OUTPUT:
        bridge_direction = "input"
    elif sig_info.direction == PortDirection.INPUT:
        bridge_direction = "output"
```

**Slave Ports (Bridge drives external slave):**
```python
# In SignalInfo database for AXI4_SLAVE_SIGNALS:
# Direction is from SLAVE's perspective, but bridge is MASTER
# So INVERT direction when generating bridge ports

if port_type == "slave":
    # Slave receives awaddr → Bridge drives awaddr → OUTPUT
    if sig_info.direction == PortDirection.OUTPUT:
        bridge_direction = "input"
    elif sig_info.direction == PortDirection.INPUT:
        bridge_direction = "output"
```

### Width Path Generation

**Algorithm for determining width paths per master:**

```python
def get_unique_slave_widths(master: MasterConfig, connectivity: Dict) -> List[int]:
    """
    Get list of unique slave widths this master connects to.

    Returns sorted list of widths for predictable path generation.
    """
    slave_widths = set()

    for slave_name in connectivity[master.name]:
        slave = get_slave_by_name(slave_name)
        slave_widths.add(slave.data_width)

    return sorted(slave_widths)  # e.g., [32, 64, 512]
```

**Example Usage:**
```python
master = MasterConfig(name="cpu", data_width=64, ...)
widths = get_unique_slave_widths(master, connectivity)
# widths = [32, 64, 512]

for width in widths:
    generate_width_path(master, width)
    # Generates: cpu_32b_*, cpu_64b_*, cpu_512b_*
```

---

## Summary Table

| Stage | Location | Signal Format | Direction | Example |
|-------|----------|---------------|-----------|---------|
| 1 | Top-level (master) | `<master>_axi_<ch><sig>` | INPUT to bridge | `m0_axi_awaddr` |
| 2 | Adapter internal | `fub_axi_<ch><sig>` | Internal | `fub_axi_awaddr` |
| 3 | Adapter internal | `slave_select_<ch>[N]` | Internal | `slave_select_aw[0]` |
| 4 | Adapter → Crossbar | `<master>_<W>b_<ch><sig>` | Adapter OUTPUT | `cpu_32b_awaddr` |
| 5 | Crossbar internal | `<slave>_xb_<ch><sig>` | Internal | `ddr_xb_awaddr` |
| 6 | Crossbar → Adapter | `<master>_<W>b_<ch><sig>` | Crossbar OUTPUT | `cpu_32b_bvalid` |
| 7 | Top-level (slave) | `<slave>_axi_<ch><sig>` | OUTPUT from bridge | `s0_axi_awaddr` |
| APB | Top-level (APB) | `<slave>_apb_<sig>` | OUTPUT from bridge | `apb0_apb_paddr` |

---

**Document Status:** DRAFT - Ready for discussion and refinement
**Next Steps:** Review with user, implement in generator code, test with 2x2 example

