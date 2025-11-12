# Bridge Generator Session Summary

**Date:** 2025-11-08 (Updated: 2025-11-10)
**Session Focus:** TOML support, signal naming fixes, and comprehensive signal naming plan
**Status:** ✅ Complete - Implementation Done (Bridge ID Tracking Complete)

---

## 📖 Update: Bridge ID Tracking Now Complete

The signal naming plan described in this document has been fully implemented as part of the bridge ID tracking feature.

**See Complete Implementation:**
- `bridge_spec/ch03_generated_rtl/07_bridge_id_tracking.md` - Full bridge ID tracking spec
- `bin/BRIDGE_ID_TRACKING_DESIGN.md` - Implementation status (COMPLETE)

---

---

## Accomplishments

### 1. Fixed TOML Configuration Support ✅

**Problem:** Generator only recognized `.yaml`/`.yml` extensions, not `.toml`

**Solution:**
- Updated `bridge_generator.py` to recognize `.toml` extension (4 locations)
- Modified `config_loader.py` to parse embedded `[connectivity]` sections from TOML
- Added `_convert_embedded_connectivity()` function to handle TOML connectivity

**Files Modified:**
- `bin/bridge_generator.py` - Changed `is_yaml` to `is_config_file`, added `.toml` support
- `bin/bridge_pkg/config_loader.py` - Added TOML connectivity parsing

**Test Result:**
```bash
python3 bridge_generator.py --ports test_configs/bridge_2x2_simple.toml --output-dir ../rtl/generated
✅ SUCCESS - Generated bridge_2x2_rw without external CSV
```

---

### 2. Fixed Signal Naming (No Direction Prefix) ✅

**Problem:** Generated signals had redundant direction prefix:
- Generated: `m0_m_axi_awaddr` (extra `m_` prefix)
- Expected: `m0_axi_awaddr` (clean, protocol-identified)

**Solution:**
- Modified `signal_naming.py` line 332
- Changed from: `f"{port_name}_{direction_str}_axi_{channel.value}{signal}"`
- Changed to: `f"{port_name}_axi_{channel.value}{signal}"`

**Rationale:**
- Port name already identifies endpoint (m0, s0, cpu, ddr)
- `_axi_` provides protocol identification for debugging
- Direction prefix `m_`/`s_` is redundant

**Files Modified:**
- `bin/bridge_pkg/signal_naming.py` - Removed direction prefix

**Test Result:**
```systemverilog
// Generated signals (CORRECT):
output logic [31:0] m0_axi_awaddr,   // ✅ Clean naming
output logic        m0_axi_awvalid,
output logic [31:0] s0_axi_awaddr,   // ✅ Clean naming
input  logic        s0_axi_awready,
```

---

### 3. Created Comprehensive Signal Naming Plan ✅

**Document:** `docs/SIGNAL_NAMING_PLAN.md`

**Coverage:**
- 7 stages of signal flow (master → adapter → xbar → adapter → slave)
- TID vs BID concepts and usage
- CAM/FIFO transaction tracking architecture
- Width adaptation signal naming
- APB protocol signals
- Complete 2x2 bridge example

**Key Architecture Decisions:**

1. **Master Adapter = Complex**
   - Timing wrapper (axi4_slave_wr/rd)
   - Address decode
   - Width conversion (all logic here)

2. **Crossbar = Simple Routing**
   - Combinational OR-based muxing
   - Per-slave CAM/FIFO for transaction tracking
   - Response routing based on BID

3. **Slave Adapter = Simple Wrapper**
   - Timing wrapper ONLY (axi4_master_wr/rd)
   - No decode, no conversion

4. **TID Passthrough**
   - Transaction ID passes through bridge unchanged
   - Enables master-side OOO tracking

5. **BID Routing**
   - Bridge ID (fixed parameter per master)
   - CAM stores TID → BID mapping
   - Enables crossbar to route responses

---

## Signal Naming Conventions

### Stage-by-Stage Naming

| Stage | Location | Signal Format | Example |
|-------|----------|---------------|---------|
| 1 | Bridge top (master) | `<master>_axi_<ch><sig>` | `cpu_axi_awaddr` |
| 2 | Master adapter (FUB) | `fub_axi_<ch><sig>` | `fub_axi_awaddr` |
| 3 | Master adapter (decode) | `slave_select_<ch>[N]` | `slave_select_aw[0]` |
| 4 | Master adapter output | `<master>_<W>b_<ch><sig>` | `cpu_32b_awaddr` |
| 4 | Master adapter BID | `<master>_<W>b_bid` | `cpu_32b_bid` |
| 5a | Crossbar routing | `<slave>_xb_<ch><sig>` | `ddr_xb_awaddr` |
| 5b | CAM instance | `u_<slave>_<ch>_cam` | `u_ddr_aw_cam` |
| 6 | Response to master | `<master>_<W>b_<ch>id_tid` | `cpu_32b_bid_tid` |
| 7 | Bridge top (slave) | `<slave>_axi_<ch><sig>` | `ddr_axi_awaddr` |

### Key Signal Types

**TID Signals (Transaction ID - Passthrough):**
```systemverilog
cpu_axi_awid        // External master TID (input)
cpu_32b_awid        // Adapter output TID
ddr_xb_awid         // Crossbar TID
ddr_axi_awid        // External slave TID (output)
cpu_32b_bid_tid     // Response TID (back to master)
cpu_axi_bid         // External master response TID (output)
```

**BID Signals (Bridge ID - Fixed):**
```systemverilog
cpu_32b_bid         // Master's BID (constant = BRIDGE_ID parameter)
ddr_aw_bid          // BID captured for CAM storage
ddr_b_bid           // BID from CAM lookup (routing decision)
```

---

## CAM/FIFO Architecture

### Per-Slave Transaction Tracking

Each slave has **2 trackers** (one for write, one for read):
- `u_<slave>_aw_cam` - Write channel tracking (AW → B)
- `u_<slave>_ar_cam` - Read channel tracking (AR → R)

### OOO vs In-Order Selection

**Configuration field:** `enable_ooo` in slave specification

```toml
[[bridge.slaves]]
name = "ddr"
enable_ooo = true   # ← Use bridge_cam (supports out-of-order)

[[bridge.slaves]]
name = "apb0"
enable_ooo = false  # ← Use gaxi_fifo (in-order only)
```

**CAM (Out-of-Order):**
```systemverilog
bridge_cam #(
    .TAG_WIDTH(4),        // TID width
    .DATA_WIDTH(2),       // BID width: log2(num_masters)
    .DEPTH(16)
) u_ddr_aw_cam (
    .allocate_tag(ddr_xb_awid),    // Store: TID → BID
    .allocate_data(ddr_aw_bid),
    .deallocate_tag(ddr_xb_bid),   // Lookup: TID → BID
    .deallocate_data(ddr_b_bid)
);
```

**FIFO (In-Order):**
```systemverilog
gaxi_fifo #(
    .DEPTH(16),
    .DATA_WIDTH(2)        // BID width only
) u_apb0_aw_fifo (
    .push_valid(apb0_xb_awvalid & apb0_xb_awready),
    .push_data(apb0_aw_bid),      // Push BID
    .pop_valid(apb0_xb_bvalid & apb0_xb_bready),
    .pop_data(apb0_b_bid)         // Pop BID (FIFO order)
);
```

---

## Module Hierarchy

```
rtl/generated/bridge_2x2_rw/
├── bridge_2x2_rw.sv              # Top-level
│   └── Instantiates:
│       ├── u_cpu_adapter (BRIDGE_ID=0)
│       ├── u_dma_adapter (BRIDGE_ID=1)
│       ├── u_xbar
│       ├── u_ddr_slave_adapter
│       └── u_sram_slave_adapter
│
├── bridge_2x2_rw_pkg.sv          # Types/parameters
│
├── cpu_master_adapter.sv         # COMPLEX (timing + decode + conversion)
├── dma_master_adapter.sv         # COMPLEX (timing + decode + conversion)
│
├── bridge_2x2_rw_xbar.sv        # SIMPLE (routing + CAMs)
│   └── Instantiates:
│       ├── u_ddr_aw_cam (bridge_cam)
│       ├── u_ddr_ar_cam (bridge_cam)
│       ├── u_sram_aw_cam (bridge_cam)
│       └── u_sram_ar_cam (bridge_cam)
│
├── ddr_slave_adapter.sv          # SIMPLE (timing wrapper only)
└── sram_slave_adapter.sv         # SIMPLE (timing wrapper only)

rtl/bridge/ (hand-written)
└── bridge_cam.sv                 # Reusable CAM for TID tracking
```

---

## Configuration Example

**File:** `test_configs/bridge_2x2_simple.toml`

```toml
[bridge]
name = "bridge_2x2_simple"
description = "2 master x 2 slave full read/write bridge"

[[bridge.masters]]
name = "m0"
prefix = "m0_"
id_width = 4
addr_width = 32
data_width = 32
user_width = 1
channels = "rw"

[[bridge.masters]]
name = "m1"
prefix = "m1_"
id_width = 4
addr_width = 32
data_width = 32
user_width = 1
channels = "rw"

[[bridge.slaves]]
name = "s0"
prefix = "s0_"
id_width = 4
addr_width = 32
data_width = 32
user_width = 1
channels = "rw"
base_addr = "0x00000000"
addr_range = "0x10000000"
enable_ooo = true  # ← Out-of-order slave (use CAM)

[[bridge.slaves]]
name = "s1"
prefix = "s1_"
id_width = 4
addr_width = 32
data_width = 32
user_width = 1
channels = "rw"
base_addr = "0x10000000"
addr_range = "0x10000000"
enable_ooo = false  # ← In-order slave (use FIFO)

[connectivity]
m0 = ["s0", "s1"]
m1 = ["s0", "s1"]
```

---

## Next Steps for Implementation

### Phase 1: Update Generators

1. **Verify signal naming changes**
   - Test `signal_naming.py` with unit tests
   - Regenerate all existing bridges
   - Verify no `_m_axi_` or `_s_axi_` prefixes

2. **Implement BID signals**
   - Add `BRIDGE_ID` parameter to master adapter generator
   - Add BID output signals (`<master>_<W>b_bid`)
   - Add BID input signals for responses (`<master>_<W>b_bid_tid`)

3. **Implement CAM/FIFO instantiation**
   - Add `enable_ooo` parameter to `SlaveInfo` class
   - Generate CAM instances for OOO slaves
   - Generate FIFO instances for in-order slaves
   - Wire up BID capture and routing logic

### Phase 2: Update Master Adapter Generator

1. **Simplify module** (remove conversion logic, keep decode)
2. **Add BID constant assignment**
3. **Add TID passthrough wiring**
4. **Generate per-width paths**

### Phase 3: Update Slave Adapter Generator

1. **Simplify to timing wrapper only**
2. **Remove all decode logic**
3. **Remove all conversion logic**
4. **Just instantiate axi4_master_wr/rd**

### Phase 4: Update Crossbar Generator

1. **Add CAM/FIFO instantiation per slave**
2. **Add BID capture logic (which master is active)**
3. **Add response routing based on BID**
4. **Maintain simple OR-based request routing**

### Phase 5: Testing

1. **Generate 2x2 simple bridge**
2. **Verify signal names match plan**
3. **Verify TID passthrough**
4. **Verify BID routing**
5. **Create testbench for CAM operation**
6. **Test OOO responses**

---

## Files Modified This Session

1. `bin/bridge_generator.py` - TOML extension support
2. `bin/bridge_pkg/config_loader.py` - TOML connectivity parsing
3. `bin/bridge_pkg/signal_naming.py` - Removed direction prefix
4. `bin/test_configs/bridge_2x2_simple.toml` - Test configuration (created)
5. `docs/SIGNAL_NAMING_PLAN.md` - Comprehensive naming plan (created)
6. `docs/BRIDGE_GENERATOR_FLOW.md` - Debug guide (read)

---

## Key Takeaways

1. **TID passes through unchanged** - Simplifies master-side tracking
2. **BID identifies master** - Fixed parameter, enables response routing
3. **CAM stores TID→BID** - Handles out-of-order responses
4. **FIFO stores BID only** - For in-order slaves (simpler, less area)
5. **Master adapter = complex** - All decode and conversion logic
6. **Slave adapter = simple** - Just timing wrapper
7. **Crossbar = routing** - Simple mux + CAM/FIFO tracking

---

**Document Status:** Complete
**Ready For:** Implementation of signal naming plan in generator code

