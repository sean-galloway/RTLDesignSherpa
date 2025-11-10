# Bridge Architecture Documentation

**Version:** 2.0
**Date:** 2025-11-04
**Purpose:** Definitive architecture reference for bridge RTL generator
**Audience:** Future AI agents, developers working on bridge generator

---

## Table of Contents

1. [Core Architecture Principles](#core-architecture-principles)
2. [Current Implementation: Adapter-Based Architecture](#current-implementation-adapter-based-architecture)
3. [Signal Flow Overview](#signal-flow-overview)
4. [Component Details](#component-details)
5. [Response Muxing Strategy](#response-muxing-strategy)
6. [Width Conversion Strategy](#width-conversion-strategy)
7. [Generator Flow](#generator-flow)
8. [Common Misconceptions](#common-misconceptions)

---

## Core Architecture Principles

### Principle 1: No Fixed Crossbar Width

**❌ WRONG ASSUMPTION:**
```
All masters → upsize to fixed 128b crossbar → downsize to slaves
(TWO conversions for mismatched paths)
```

**✅ CORRECT ARCHITECTURE:**
```
Master (256b) → direct path → Slave (256b)  [0 conversions]
Master (256b) → converter → Slave (64b)     [1 conversion]
```

**Key Insight:** The crossbar is a **routing fabric**, not a width normalizer. It routes appropriately-sized signals, not fixed-width signals.

### Principle 2: Adapter-Based Per-Master Routing

**Current Implementation (V2):**

Each master has a dedicated adapter module that:
1. **Timing Isolation** - Interface wrapper for timing closure
2. **Address Decode** - One-hot slave selection based on address ranges
3. **Width Adaptation** - Generates N output paths (one per unique slave width)
4. **Direct Passthrough** - No conversion when master width matches slave width

**Example: 64b master connecting to 32b and 64b slaves**
```
Master (64b) → Adapter
    ├─ 32b path → (via converter) → 32b slaves
    └─ 64b path → (direct) → 64b slaves
```

### Principle 3: Response Muxing via OR Logic

**Problem:** Multiple slaves can respond to the same master, creating MULTIDRIVEN errors.

**Solution:** OR-based muxing of all slave responses:
```systemverilog
// For each master and width path, OR together all slave responses
assign master_64b_awready =
    (master_slave_select_aw[0] ? slave0_awready : '0) |
    (master_slave_select_aw[1] ? slave1_awready : '0);
```

**Key Insight:** Only ONE slave is selected at a time (one-hot), so ORing is safe and eliminates multiple drivers.

---

## Current Implementation: Adapter-Based Architecture

### Module Hierarchy

```
bridge_<name>
├── <master>_adapter (per master)
│   ├── axi4_slave_wr (timing wrapper)
│   ├── Address decode logic
│   └── Width adaptation logic (generates N paths)
│
├── <bridge_name>_xbar (crossbar routing)
│   ├── Request routing (master → slave)
│   └── Response muxing (slaves → master)
│
└── External slave ports
```

### Key Architecture Decisions

1. **Adapters replace converters** - Each master has one adapter that handles all width paths
2. **No separate width converters** - Width conversion logic integrated into adapter
3. **Crossbar handles routing only** - Simple combinational routing based on select signals
4. **Response muxing in crossbar** - OR-based combining of slave responses

### File Structure

```
rtl/generated/<bridge_name>/
├── <bridge_name>_pkg.sv        # Package with type definitions
├── <master>_adapter.sv         # Per-master adapter (replaces converters)
├── <bridge_name>_xbar.sv       # Crossbar routing module
└── <bridge_name>.sv            # Top-level bridge module
```

---

## Signal Flow Overview

### Complete Path: 64b Master → Two 32b Slaves

```
┌─────────────────────────────────────────────────────────────────┐
│ External Master Port (cpu_m_axi_*)                              │
│   • Data: 64 bits                                               │
│   • ID: 4 bits                                                  │
│   • Addr: 32 bits                                               │
└────────────────┬────────────────────────────────────────────────┘
                 │
                 ▼
┌─────────────────────────────────────────────────────────────────┐
│ CPU Adapter Module                                              │
│                                                                  │
│ ┌─────────────────────────────────────────────────────────┐    │
│ │ axi4_slave_wr (Timing Wrapper)                          │    │
│ │   • Skid buffers for timing closure                     │    │
│ │   • Pass-through (no width conversion)                  │    │
│ │   • Output: fub_axi_* signals (64b)                     │    │
│ └──────────────┬──────────────────────────────────────────┘    │
│                │                                                 │
│                ▼                                                 │
│ ┌─────────────────────────────────────────────────────────┐    │
│ │ Address Decode (Combinational)                          │    │
│ │   • Reads: fub_axi_awaddr / fub_axi_araddr             │    │
│ │   • Outputs: slave_select_aw[N], slave_select_ar[N]    │    │
│ │   • One-hot encoding (only one bit set)                │    │
│ │                                                          │    │
│ │   if (addr <= 0x7FFFFFFF)                              │    │
│ │       slave_select_aw[0] = 1;  // ddr                  │    │
│ │   else if (addr >= 0x80000000)                         │    │
│ │       slave_select_aw[1] = 1;  // sram                 │    │
│ └──────────────┬──────────────────────────────────────────┘    │
│                │                                                 │
│                ▼                                                 │
│ ┌─────────────────────────────────────────────────────────┐    │
│ │ Width Adaptation Logic                                  │    │
│ │                                                          │    │
│ │ For each unique slave width connected to this master:   │    │
│ │                                                          │    │
│ │ 32b path (for 32b slaves):                             │    │
│ │   • Convert 64b → 32b (using converter logic)          │    │
│ │   • Outputs: cpu_32b_aw, cpu_32b_w, cpu_32b_b          │    │
│ │                                                          │    │
│ │ 64b path (for 64b slaves):                             │    │
│ │   • Direct passthrough (no conversion)                  │    │
│ │   • Outputs: cpu_64b_aw, cpu_64b_w, cpu_64b_b          │    │
│ └──────────────┬──────────────────────────────────────────┘    │
│                │                                                 │
│ Adapter Outputs (to crossbar):                                  │
│   • slave_select_aw[2]  (one-hot slave selection)              │
│   • cpu_32b_aw, cpu_32b_awvalid, cpu_32b_awready               │
│   • cpu_32b_w, cpu_32b_wvalid, cpu_32b_wready                  │
│   • cpu_32b_b, cpu_32b_bvalid, cpu_32b_bready                  │
│   • cpu_64b_aw, cpu_64b_awvalid, cpu_64b_awready               │
│   • cpu_64b_w, cpu_64b_wvalid, cpu_64b_wready                  │
│   • cpu_64b_b, cpu_64b_bvalid, cpu_64b_bready                  │
└────────────────┬────────────────────────────────────────────────┘
                 │
                 ▼
┌─────────────────────────────────────────────────────────────────┐
│ Crossbar Module (<bridge_name>_xbar)                           │
│                                                                  │
│ ┌─────────────────────────────────────────────────────────┐    │
│ │ Request Routing (Master → Slave)                        │    │
│ │                                                          │    │
│ │ For each slave:                                         │    │
│ │   • Select correct width path from master              │    │
│ │   • Route based on slave_select signal                │    │
│ │                                                          │    │
│ │ Example: Slave 0 (32b)                                 │    │
│ │   assign slave0_awaddr =                               │    │
│ │       slave_select_aw[0] ? cpu_32b_aw.addr : '0;      │    │
│ │   assign slave0_awvalid =                              │    │
│ │       slave_select_aw[0] ? cpu_32b_awvalid : '0;      │    │
│ └──────────────┬──────────────────────────────────────────┘    │
│                │                                                 │
│                ▼                                                 │
│ ┌─────────────────────────────────────────────────────────┐    │
│ │ Response Muxing (Slaves → Master)                       │    │
│ │                                                          │    │
│ │ OR together responses from all slaves:                  │    │
│ │                                                          │    │
│ │ assign cpu_32b_awready =                               │    │
│ │     (slave_select_aw[0] ? slave0_awready : '0) |       │    │
│ │     (slave_select_aw[1] ? slave1_awready : '0);        │    │
│ │                                                          │    │
│ │ assign cpu_32b_b.id =                                  │    │
│ │     (slave_select_aw[0] ? slave0_bid : '0) |           │    │
│ │     (slave_select_aw[1] ? slave1_bid : '0);            │    │
│ │                                                          │    │
│ │ Safe because slave_select is one-hot!                  │    │
│ └─────────────────────────────────────────────────────────┘    │
└────────────────┬────────────────────────────────────────────────┘
                 │
                 ▼
┌─────────────────────────────────────────────────────────────────┐
│ External Slave Ports (ddr_s_axi_*, sram_s_axi_*, etc.)         │
│   • Correctly sized (32b, 64b, etc.)                           │
│   • Ready to connect to actual slaves                          │
└─────────────────────────────────────────────────────────────────┘
```

### Key Signal Conventions

**Naming Pattern:**
- `<master>_<width>b_<channel>` - Master adapter outputs (e.g., `cpu_32b_aw`, `cpu_64b_w`)
- `<slave>_s_axi_<signal>` - Slave interface signals (e.g., `ddr_s_axi_awaddr`)
- `<master>_slave_select_<channel>` - One-hot slave selection (e.g., `cpu_slave_select_aw`)

**Signal Directions:**
- **Requests (Master → Slave):** AW, W, AR channels
- **Responses (Slave → Master):** B, R channels
- **Ready (Slave → Master):** awready, wready, arready
- **Valid (Master → Slave):** awvalid, wvalid, bvalid, arvalid, rvalid

---

## Component Details

### 1. Adapter Module (`<master>_adapter.sv`)

**Purpose:** Per-master processing before crossbar routing

**Responsibilities:**
1. **Timing Isolation** - Via axi4_slave_wr/rd wrapper
2. **Address Decode** - Generate one-hot slave selection
3. **Width Adaptation** - Create N output paths for N unique slave widths
4. **Response Routing** - Accept responses from crossbar

**Generated Signals:**

```systemverilog
// Address decode outputs
output logic [NUM_SLAVES-1:0] slave_select_aw;
output logic [NUM_SLAVES-1:0] slave_select_ar;

// Per-width paths (example: 32b and 64b slaves)
// 32b path
output axi4_aw_t     cpu_32b_aw;
output logic         cpu_32b_awvalid;
input  logic         cpu_32b_awready;
output axi4_w_32b_t  cpu_32b_w;
output logic         cpu_32b_wvalid;
input  logic         cpu_32b_wready;
input  axi4_b_t      cpu_32b_b;
input  logic         cpu_32b_bvalid;
output logic         cpu_32b_bready;

// 64b path
output axi4_aw_t     cpu_64b_aw;
output logic         cpu_64b_awvalid;
input  logic         cpu_64b_awready;
output axi4_w_64b_t  cpu_64b_w;
output logic         cpu_64b_wvalid;
input  logic         cpu_64b_wready;
input  axi4_b_t      cpu_64b_b;
input  logic         cpu_64b_bvalid;
output logic         cpu_64b_bready;
```

**Address Decode Logic:**

Smart comparison eliminates redundant checks:
```systemverilog
always_comb begin
    slave_select_aw = '0;
    // First slave: skip >= 0 (unsigned always >= 0)
    if (fub_axi_awaddr <= 32'h7FFFFFFF) begin
        slave_select_aw[0] = 1'b1;  // ddr
    end
    // Last slave: skip <= 0xFFFFFFFF (32-bit always <= max)
    else if (fub_axi_awaddr >= 32'h80000000) begin
        slave_select_aw[1] = 1'b1;  // sram
    end
end
```

**Width Adaptation:**

When master width matches slave width:
```systemverilog
// Direct passthrough (64b master → 64b slave path)
assign cpu_64b_aw.id    = fub_axi_awid;
assign cpu_64b_aw.addr  = fub_axi_awaddr;
assign cpu_64b_w.data   = fub_axi_wdata;
assign cpu_64b_awvalid  = fub_axi_awvalid;
```

When master width differs from slave width:
```systemverilog
// Width converter (64b master → 32b slave path)
// TODO: Instantiate axi4_dwidth_converter_wr
// For now: Direct connection (will be replaced with converter)
assign cpu_32b_aw.id    = fub_axi_awid;
assign cpu_32b_aw.addr  = fub_axi_awaddr;
assign cpu_32b_w.data   = fub_axi_wdata[31:0];  // Truncate
assign cpu_32b_awvalid  = fub_axi_awvalid;
```

### 2. Crossbar Module (`<bridge_name>_xbar.sv`)

**Purpose:** Route width-adapted signals from adapters to slaves

**Responsibilities:**
1. **Request Routing** - Select correct width path for each slave
2. **Response Muxing** - OR together slave responses for each master

**Generated Structure:**

```systemverilog
module bridge_1x2_wr_xbar (
    input  logic aclk,
    input  logic aresetn,

    // Adapter inputs
    input  logic [NUM_SLAVES-1:0] cpu_slave_select_aw,
    input  axi4_aw_t     cpu_32b_aw,
    input  logic         cpu_32b_awvalid,
    output logic         cpu_32b_awready,
    // ... more signals

    // Slave outputs
    output logic [3:0]   ddr_s_axi_awid,
    output logic [31:0]  ddr_s_axi_awaddr,
    // ... more slave signals
);

// ================================================================
// Request Routing (Master → Slave)
// ================================================================

// Slave 0: ddr (32b)
assign ddr_s_axi_awid    = cpu_slave_select_aw[0] ? cpu_32b_aw.id : '0;
assign ddr_s_axi_awaddr  = cpu_slave_select_aw[0] ? cpu_32b_aw.addr : '0;
assign ddr_s_axi_awvalid = cpu_slave_select_aw[0] ? cpu_32b_awvalid : '0;

// ================================================================
// Response Muxing (Slaves → Master)
// ================================================================

// OR together all slave responses (safe due to one-hot selection)
assign cpu_32b_awready =
    (cpu_slave_select_aw[0] ? ddr_s_axi_awready : '0) |
    (cpu_slave_select_aw[1] ? sram_s_axi_awready : '0);

assign cpu_32b_b.id =
    (cpu_slave_select_aw[0] ? ddr_s_axi_bid : '0) |
    (cpu_slave_select_aw[1] ? sram_s_axi_bid : '0);

endmodule
```

**Key Characteristics:**
- Purely combinational routing
- No state machines or arbitration (future enhancement)
- One-hot slave selection ensures safe ORing
- Separate routing for each AXI channel (AW, W, B, AR, R)

### 3. Package Module (`<bridge_name>_pkg.sv`)

**Purpose:** Type definitions for struct-based signals

**Generated Types:**

```systemverilog
package bridge_1x2_wr_pkg;

    // AW channel struct
    typedef struct packed {
        logic [3:0]  id;
        logic [31:0] addr;
        logic [7:0]  len;
        logic [2:0]  size;
        logic [1:0]  burst;
        logic        lock;
        logic [3:0]  cache;
        logic [2:0]  prot;
    } axi4_aw_t;

    // W channel struct (parameterized by width)
    typedef struct packed {
        logic [31:0] data;
        logic [3:0]  strb;
        logic        last;
    } axi4_w_32b_t;

    typedef struct packed {
        logic [63:0] data;
        logic [7:0]  strb;
        logic        last;
    } axi4_w_64b_t;

    // B channel struct
    typedef struct packed {
        logic [3:0]  id;
        logic [1:0]  resp;
    } axi4_b_t;

    // Similar for AR, R channels...

endpackage
```

**Benefits:**
- Cleaner signal grouping
- Easier to read generated RTL
- Type-safe connections
- Matches SystemVerilog best practices

---

## Response Muxing Strategy

### Problem Statement

When multiple slaves can respond to the same master, traditional assign statements create multiple drivers:

```systemverilog
// ❌ WRONG: Multiple drivers on cpu_32b_awready
assign cpu_32b_awready = cpu_slave_select_aw[0] ? slave0_awready : '0;
assign cpu_32b_awready = cpu_slave_select_aw[1] ? slave1_awready : '0;
// Verilator: %Warning-MULTIDRIVEN
```

### Solution: OR-Based Muxing

Since slave_select is one-hot (only one bit set at a time), ORing all responses is safe:

```systemverilog
// ✅ CORRECT: Single assign with OR
assign cpu_32b_awready =
    (cpu_slave_select_aw[0] ? slave0_awready : '0) |
    (cpu_slave_select_aw[1] ? slave1_awready : '0) |
    (cpu_slave_select_aw[2] ? slave2_awready : '0);
```

**Why This Works:**
- One-hot selection means only ONE slave is selected
- Selected slave contributes its value
- Unselected slaves contribute '0
- OR of (value | '0 | '0) = value
- No actual multiple drivers - just one active source

### Implementation in crossbar_generator.py

**Method: `_generate_response_muxes()`**

For each master and width combination:
1. Find all slaves at that width connected to that master
2. Generate OR-based mux for each response signal

**Write Channel Responses:**
- awready (slave → master)
- wready (slave → master)
- b.id, b.resp, bvalid (slave → master)

**Read Channel Responses:**
- arready (slave → master)
- r.id, r.data, r.resp, r.last, rvalid (slave → master)

**Example Generated Code:**

```systemverilog
// Master: cpu, Width path: 32b
assign cpu_32b_awready =
    (cpu_slave_select_aw[0] ? ddr_s_axi_awready : '0) |
    (cpu_slave_select_aw[1] ? sram_s_axi_awready : '0);

assign cpu_32b_wready =
    (cpu_slave_select_aw[0] ? ddr_s_axi_wready : '0) |
    (cpu_slave_select_aw[1] ? sram_s_axi_wready : '0);

assign cpu_32b_b.id =
    (cpu_slave_select_aw[0] ? ddr_s_axi_bid : '0) |
    (cpu_slave_select_aw[1] ? sram_s_axi_bid : '0);

assign cpu_32b_b.resp =
    (cpu_slave_select_aw[0] ? ddr_s_axi_bresp : '0) |
    (cpu_slave_select_aw[1] ? sram_s_axi_bresp : '0);

assign cpu_32b_bvalid =
    (cpu_slave_select_aw[0] ? ddr_s_axi_bvalid : '0) |
    (cpu_slave_select_aw[1] ? sram_s_axi_bvalid : '0);
```

### Verification

**Verilator Results:**
- Zero MULTIDRIVEN warnings (was 18)
- Zero UNSIGNED warnings (was 6)
- Zero CMPCONST warnings (was 6)
- Clean synthesis

---

## Width Conversion Strategy

### Decision Matrix: When to Use Converters

| Master Width | Slave Width | Strategy | Converter Needed? |
|--------------|-------------|----------|-------------------|
| 64b | 64b | Direct passthrough | No |
| 64b | 32b | Downsize converter | Yes (future) |
| 32b | 64b | Upsize converter | Yes (future) |
| 256b | 64b | Downsize converter | Yes (future) |

### Current Implementation

**Phase 1 (Current):** Direct passthrough for all paths
- Width conversion logic is stubbed out
- All paths use direct signal mapping
- Works for testing routing logic

**Phase 2 (Future):** Integrate width converters
- Instantiate axi4_dwidth_converter_rd/wr when needed
- Converter placed in adapter module
- One converter per master-width combination

### Per-Master Converter Count

Each master generates converters for unique slave widths it connects to:

**Example 1: Master (64b) → Slaves (32b, 64b, 128b)**
- 32b path: axi4_dwidth_converter_wr (64→32)
- 64b path: Direct passthrough
- 128b path: axi4_dwidth_converter_wr (64→128)
- Total: 2 converters

**Example 2: Master (256b) → Slaves (64b, 64b, 64b)**
- 64b path: axi4_dwidth_converter_wr (256→64)
- Total: 1 converter (shared by all 64b slaves)

### Resource Efficiency

**Key Optimization:** Converters are shared across slaves of the same width

Traditional approach (wasteful):
```
Master → Conv(64→32) → Slave0 (32b)
      ├→ Conv(64→32) → Slave1 (32b)  ← Duplicate!
      └→ Conv(64→32) → Slave2 (32b)  ← Duplicate!
```

Adapter approach (efficient):
```
Master → Adapter
    ├─ 32b path (1 converter) → {Slave0, Slave1, Slave2}
    └─ 64b path (0 converter) → {Slave3}
```

---

## Generator Flow

### High-Level Generation Sequence

1. **Parse Configuration** (YAML/CSV files)
   - Extract master/slave definitions
   - Build connectivity matrix
   - Determine unique widths per master

2. **Generate Package** (`package_generator.py`)
   - Type definitions for AW, W, B, AR, R channels
   - Parameterized by data width
   - Imported by all generated modules

3. **Generate Adapters** (`adapter_generator.py`)
   - One adapter per master
   - Timing wrapper instantiation
   - Address decode logic
   - Width adaptation paths
   - Response handling

4. **Generate Crossbar** (`crossbar_generator.py`)
   - Request routing (master → slave)
   - Response muxing (slaves → master)
   - One routing section per slave
   - One mux section per master

5. **Generate Top Module** (`bridge_module_generator.py`)
   - External port declarations
   - Adapter instantiations
   - Crossbar instantiation
   - Signal connections

6. **Generate Filelist** (`package_generator.py`)
   - Include paths
   - Source file list
   - Dependency ordering

### Configuration Parameters

**Master Specification:**
```yaml
masters:
  - name: cpu
    prefix: cpu_m_axi_
    data_width: 32
    addr_width: 32
    id_width: 4
    channels: wr  # Write-only (AW, W, B)
```

**Slave Specification:**
```yaml
slaves:
  - name: ddr
    prefix: ddr_s_axi_
    data_width: 32
    addr_width: 32
    id_width: 4
    channels: wr
    base_addr: 0x00000000
    addr_range: 0x80000000
```

**Connectivity Matrix:**
```csv
master\slave,ddr,sram
cpu,1,1
```

### Critical Generator Logic

**1. Determine Unique Widths per Master** (`adapter_generator.py`)

```python
def _get_connected_slave_widths(self, master: MasterConfig) -> List[int]:
    """Get sorted list of unique slave widths this master connects to."""
    widths = set()
    for idx in master.slave_connections:
        widths.add(self.slaves[idx].data_width)
    return sorted(list(widths))
```

**2. Generate Smart Address Decode** (`adapter_generator.py`)

```python
def _generate_decode_logic(self, addr_signal: str, select_signal: str) -> List[str]:
    addr_width = self.master.addr_width
    max_addr = (1 << addr_width) - 1

    for i, idx in enumerate(self.master.slave_connections):
        slave = self.slaves[idx]
        end_addr = slave.base_addr + slave.addr_range - 1

        # Skip redundant comparisons
        if slave.base_addr == 0:
            # Skip >= 0 (unsigned always >= 0)
            lines.append(f"if ({addr_signal} <= {addr_width}'h{end_addr:08X})")
        elif end_addr == max_addr:
            # Skip <= max (always true for full width)
            lines.append(f"else if ({addr_signal} >= {addr_width}'h{slave.base_addr:08X})")
        else:
            # Both bounds needed
            lines.append(f"else if ({addr_signal} >= {addr_width}'h{slave.base_addr:08X} && {addr_signal} <= {addr_width}'h{end_addr:08X})")
```

**3. Generate Response Muxes** (`crossbar_generator.py`)

```python
def _generate_response_muxes(self) -> List[str]:
    """Generate OR-based muxing of slave responses."""
    for master in self.masters:
        widths = self._get_connected_slave_widths(master)

        for width in widths:
            suffix = f"{width}b"

            # Write responses
            if master.channels in ["wr", "rw"]:
                self._generate_write_response_mux(master, width, suffix)

            # Read responses
            if master.channels in ["rd", "rw"]:
                self._generate_read_response_mux(master, width, suffix)
```

---

## Common Misconceptions

### ❌ Misconception 1: Fixed Crossbar Width

**WRONG:** "The crossbar operates at a fixed 256b width, so all signals must be upsized/downsized to match."

**CORRECT:** The crossbar routes appropriately-sized signals. Each master generates N width-specific paths (one per unique slave width). The crossbar selects the correct path based on the target slave's width.

**Example:**
- Master (64b) connecting to 32b and 64b slaves generates TWO paths:
  - 32b path (via converter) for 32b slaves
  - 64b path (direct) for 64b slaves

### ❌ Misconception 2: Converters at External Ports

**WRONG:** "Width converters are instantiated at external master/slave ports."

**CORRECT:** Width conversion happens inside the adapter module, AFTER timing isolation and address decode. External ports remain at their native widths.

**Signal Flow:**
```
External Port (64b)
  → Timing Wrapper (64b, no conversion)
  → Address Decode (64b, no conversion)
  → Width Adaptation (generates 32b + 64b paths)
  → Crossbar routes based on slave width
```

### ❌ Misconception 3: Multiple Assign Statements for Responses

**WRONG:** "Each slave's response is assigned individually, creating one assign per slave."

**CORRECT:** All slave responses for a given master are OR'd together in a SINGLE assign statement. This eliminates MULTIDRIVEN errors.

**Wrong Code:**
```systemverilog
assign cpu_32b_awready = slave_select[0] ? slave0_awready : '0;  // ❌
assign cpu_32b_awready = slave_select[1] ? slave1_awready : '0;  // ❌ MULTIDRIVEN
```

**Correct Code:**
```systemverilog
assign cpu_32b_awready =
    (slave_select[0] ? slave0_awready : '0) |  // ✅
    (slave_select[1] ? slave1_awready : '0);   // ✅ Single assign
```

### ❌ Misconception 4: Crossbar Does Width Conversion

**WRONG:** "The crossbar module contains width conversion logic."

**CORRECT:** The crossbar is purely a routing fabric. It routes pre-sized signals from adapters to slaves. All width conversion happens in the adapter modules.

**Crossbar Responsibilities:**
- Route requests (master → slave) based on select signals
- Mux responses (slaves → master) using OR logic
- NO width conversion, NO state machines, NO arbitration

### ❌ Misconception 5: One Converter Per Master-Slave Pair

**WRONG:** "If a master connects to 3 slaves of the same width, you need 3 converters."

**CORRECT:** Converters are shared across slaves of the same width. One converter per unique width.

**Example:**
- Master (256b) → Slave0 (64b), Slave1 (64b), Slave2 (64b)
- Total converters: **1** (one 256→64 converter shared by all three slaves)

---

## References

### Related Documentation

- `/projects/components/bridge/CLAUDE.md` - AI-specific guidance
- `/projects/components/bridge/PRD.md` - Product requirements
- `/projects/components/bridge/docs/bridge_spec/` - Detailed specification

### Key Source Files

**Generator Core:**
- `bin/bridge_generator.py` - Main entry point
- `bin/bridge_pkg/generators/adapter_generator.py` - Per-master adapter generation
- `bin/bridge_pkg/generators/crossbar_generator.py` - Crossbar routing and response muxing
- `bin/bridge_pkg/generators/package_generator.py` - Type definitions
- `bin/bridge_pkg/components/bridge_module_generator.py` - Top-level bridge module

**Configuration:**
- `bin/bridge_batch.csv` - Bulk generation list
- `bin/test_configs/*.yaml` - Per-bridge YAML configurations
- `bin/test_configs/*_connectivity.csv` - Connectivity matrices

**Generated Output:**
- `rtl/generated/<bridge_name>/` - All generated RTL files

### Example Configurations

**Minimal 1x2 Write-Only Bridge:**
- Config: `test_configs/bridge_1x2_wr_minimal.yaml`
- Output: `rtl/generated/bridge_1x2_wr/`
- Features: 1 master (32b), 2 slaves (32b), write-only

**Full 4x4 Read/Write Bridge:**
- Config: `test_configs/bridge_4x4_rw.yaml`
- Output: `rtl/generated/bridge_4x4_rw/`
- Features: 4 masters (mixed widths), 4 slaves (mixed widths), full read/write

---

**Document History:**
- v1.0 (2025-11-03): Initial architecture documentation
- v2.0 (2025-11-04): Updated with adapter-based architecture and response muxing

**Maintained By:** RTL Design Sherpa Project
