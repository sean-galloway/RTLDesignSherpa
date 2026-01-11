# RAPIDS Refactor Plan: Phase 1 (STREAM-like Simplicity)

**Created:** 2026-01-09
**Status:** Planning
**Goal:** Refactor RAPIDS to use proven STREAM patterns with AXIS interfaces

---

## Executive Summary

Rebuild RAPIDS incrementally within the existing structure:
- **Phase 1:** STREAM-like simplicity (aligned, line-based, no chunk tracking)
- **Phase 2:** Add sophistication (chunk-based, mis-aligned handling)

This approach:
- Avoids creating a third component (stream, rapids_line, rapids)
- Tests AXIS interfaces and unified SRAM controller with simple logic first
- Adds complexity only after foundation works

---

## Architecture Overview

### Current RAPIDS (Broken)
```
AXIS Slave → sink_sram_control → sink_axi_write_engine → Memory
                 ↑ (same AXI interface pattern as write - WRONG)

Memory → source_axi_read_engine → source_sram_control → AXIS Master
                                        ↑ (same AXI interface pattern as read - WRONG)
```

**Problem:** Both SRAM controllers have identical AXI interface patterns when they should have opposite behaviors (fill vs drain).

### Target RAPIDS Architecture (Phase 1)
```
┌─────────────────────────────────────────────────────────────────────┐
│                         RAPIDS Phase 1                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  SINK PATH (Network → Memory)                                       │
│  ┌──────────────┐    ┌─────────────────┐    ┌─────────────────────┐ │
│  │ AXIS Slave   │───►│ Unified SRAM    │───►│ AXI Write Engine   │ │
│  │ (fill wrap)  │    │ Controller      │    │ (from STREAM)      │ │
│  └──────────────┘    │ (from STREAM)   │    └─────────────────────┘ │
│                      │                 │                             │
│                      │  Fill ←┐  ┌→ Drain                           │
│                      │        │  │                                   │
│  SOURCE PATH (Memory → Network)         │                           │
│  ┌─────────────────┐ │        │  │      │ ┌──────────────┐         │
│  │ AXI Read Engine │─┴────────┘  └──────┴─│ AXIS Master  │         │
│  │ (from STREAM)   │                      │ (drain wrap) │         │
│  └─────────────────┘                      └──────────────┘         │
│                                                                      │
│  SCHEDULER GROUPS                                                    │
│  ┌─────────────────────────┐  ┌─────────────────────────┐          │
│  │ Sink Scheduler Group    │  │ Source Scheduler Group  │          │
│  │ Array (from STREAM)     │  │ Array (from STREAM)     │          │
│  └─────────────────────────┘  └─────────────────────────┘          │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Key Design Decision: Option B - Unified SRAM Controller with Generic Interfaces

### Concept

Create a **single unified sram_controller** (based on STREAM's) with:
- **Fill interface:** Protocol-agnostic data input (alloc + write)
- **Drain interface:** Protocol-agnostic data output (avail + read)

Protocol-specific wrappers handle the conversion:
- **axis_to_fill_wrapper:** AXIS Slave → Fill interface
- **drain_to_axis_wrapper:** Drain interface → AXIS Master
- **axi_read_engine:** AXI4 Master Read → Fill interface (from STREAM)
- **axi_write_engine:** Drain interface → AXI4 Master Write (from STREAM)

### Interface Definition (Generic)

```systemverilog
//=========================================================================
// Fill Interface (Data Producer → SRAM)
// Used by: AXIS Slave wrapper (sink), AXI Read Engine (source)
//=========================================================================
input  logic                        fill_alloc_req,       // Space allocation request
input  logic [7:0]                  fill_alloc_size,      // Beats to allocate
input  logic [CIW-1:0]              fill_alloc_id,        // Channel ID
output logic [NC-1:0][SCW-1:0]      fill_space_free,      // Free space per channel

input  logic                        fill_valid,           // Data valid
output logic                        fill_ready,           // Ready for data
input  logic [CIW-1:0]              fill_id,              // Channel ID
input  logic [DW-1:0]               fill_data,            // Data payload

//=========================================================================
// Drain Interface (SRAM → Data Consumer)
// Used by: AXI Write Engine (sink), AXIS Master wrapper (source)
//=========================================================================
output logic [NC-1:0][SCW-1:0]      drain_data_avail,     // Available data per channel
input  logic [NC-1:0]               drain_req,            // Drain request per channel
input  logic [NC-1:0][7:0]          drain_size,           // Drain size per channel

output logic [NC-1:0]               drain_valid,          // Data valid per channel
input  logic                        drain_read,           // Consumer read enable
input  logic [CIW-1:0]              drain_id,             // Channel ID to drain
output logic [DW-1:0]               drain_data            // Data payload
```

This matches STREAM's `sram_controller.sv` interface pattern exactly, just with generic naming.

---

## Module Mapping: STREAM → RAPIDS

### Modules to Copy (No Changes)
| STREAM Module | RAPIDS Location | Purpose |
|---------------|-----------------|---------|
| `simple_sram.sv` | Already exists | Per-channel FIFO storage |
| `stream_latency_bridge.sv` | Copy to rapids_fub | FIFO read latency compensation |

### Modules to Adapt (Minor Changes)
| STREAM Module | RAPIDS Module | Changes Required |
|---------------|---------------|------------------|
| `sram_controller.sv` | `unified_sram_controller.sv` | Rename interfaces to generic fill/drain |
| `sram_controller_unit.sv` | `unified_sram_controller_unit.sv` | Rename interfaces |
| `axi_read_engine.sv` | Copy as-is | None (connects to fill interface) |
| `axi_write_engine.sv` | Copy as-is | None (connects from drain interface) |
| `stream_alloc_ctrl.sv` | Copy as-is | Used by alloc interface |
| `stream_drain_ctrl.sv` | Copy as-is | Used by drain interface |

### Modules to Create (New)
| Module | Purpose | Complexity |
|--------|---------|------------|
| `axis_to_fill_wrapper.sv` | AXIS Slave → Fill interface | Low (~100 lines) |
| `drain_to_axis_wrapper.sv` | Drain interface → AXIS Master | Low (~100 lines) |
| `rapids_sink_path.sv` | Sink integration top | Medium (~200 lines) |
| `rapids_source_path.sv` | Source integration top | Medium (~200 lines) |
| `rapids_core.sv` | Full core integration | Medium (~300 lines) |

---

## Data Flow Details

### Sink Path: Network → Memory

```
1. AXIS Slave receives packet from network
   ├── tdata, tvalid, tready, tlast, tuser
   └── tuser[1:0] identifies packet type (CDA=01, PKT_DATA=00)

2. axis_to_fill_wrapper converts AXIS to fill interface
   ├── Handles tlast → marks EOS in SRAM metadata
   ├── Maps tuser → fill control signals
   └── Provides fill_alloc_req when starting new transfer

3. unified_sram_controller buffers data
   ├── Per-channel FIFOs (not shared SRAM segmentation)
   ├── fill_space_free provides backpressure to wrapper
   └── drain_data_avail signals AXI write engine

4. axi_write_engine (from STREAM) drains to memory
   ├── Uses drain interface to read from SRAM
   ├── Generates AXI4 write bursts
   └── Reports completion to scheduler
```

### Source Path: Memory → Network

```
1. axi_read_engine (from STREAM) fills from memory
   ├── Uses fill interface to write to SRAM
   ├── Generates AXI4 read bursts
   └── fill_space_free provides backpressure

2. unified_sram_controller buffers data
   ├── Same module as sink path (parameterized or separate instance)
   ├── drain_data_avail signals AXIS wrapper
   └── Per-channel independent operation

3. drain_to_axis_wrapper converts drain to AXIS
   ├── drain_valid → tvalid
   ├── drain_data → tdata
   ├── Generates tlast from EOS metadata
   └── Sets appropriate tuser for packet type

4. AXIS Master transmits to network
   └── Standard AXIS protocol
```

---

## Phase 1 Simplifications (STREAM-like)

Following STREAM's intentional simplifications:

| Feature | Phase 1 (Simple) | Phase 2 (Full RAPIDS) |
|---------|------------------|----------------------|
| **Addresses** | Aligned only | Alignment fixup logic |
| **Length** | In beats | In chunks (4-byte units) |
| **Buffers** | No circular | Circular buffer support |
| **Credits** | Simple limits | Exponential encoding |
| **Descriptors** | 256-bit STREAM format | RAPIDS extended format |
| **Channels** | 8 (like STREAM) | 16 (full RAPIDS) |

---

## File Organization

```
projects/components/rapids/rtl/
├── rapids_fub/
│   ├── unified_sram_controller.sv      # NEW: Generic fill/drain (from STREAM)
│   ├── unified_sram_controller_unit.sv # NEW: Per-channel unit (from STREAM)
│   ├── stream_latency_bridge.sv        # COPY: From STREAM
│   ├── axis_to_fill_wrapper.sv         # NEW: AXIS → fill
│   ├── drain_to_axis_wrapper.sv        # NEW: drain → AXIS
│   ├── axi_read_engine.sv              # COPY: From STREAM
│   ├── axi_write_engine.sv             # COPY: From STREAM
│   ├── stream_alloc_ctrl.sv            # COPY: From STREAM
│   ├── stream_drain_ctrl.sv            # COPY: From STREAM
│   ├── simple_sram.sv                  # EXISTS: Keep as-is
│   ├── scheduler.sv                    # ADAPT: Simplify from current
│   └── descriptor_engine.sv            # ADAPT: Simplify from current
│
├── rapids_macro/
│   ├── rapids_sink_path.sv             # NEW: Sink integration
│   ├── rapids_source_path.sv           # NEW: Source integration
│   ├── sink_scheduler_group.sv         # NEW: Sink scheduler group
│   ├── source_scheduler_group.sv       # NEW: Source scheduler group
│   ├── sink_scheduler_group_array.sv   # NEW: Sink array (8 channels)
│   ├── source_scheduler_group_array.sv # NEW: Source array (8 channels)
│   └── rapids_core.sv                  # NEW: Core integration
│
├── rapids_top/
│   └── rapids_top_ch8.sv               # NEW: 8-channel top level
│
└── includes/
    ├── rapids_pkg.sv                   # ADAPT: Update for Phase 1
    └── rapids_imports.svh              # Keep
```

---

## Implementation Steps

### Step 1: Copy STREAM Modules
```bash
# Copy modules that work as-is
cp projects/components/stream/rtl/fub/simple_sram.sv \
   projects/components/rapids/rtl/rapids_fub/

cp projects/components/stream/rtl/fub/stream_latency_bridge.sv \
   projects/components/rapids/rtl/rapids_fub/

cp projects/components/stream/rtl/fub/axi_read_engine.sv \
   projects/components/rapids/rtl/rapids_fub/

cp projects/components/stream/rtl/fub/axi_write_engine.sv \
   projects/components/rapids/rtl/rapids_fub/

cp projects/components/stream/rtl/fub/stream_alloc_ctrl.sv \
   projects/components/rapids/rtl/rapids_fub/

cp projects/components/stream/rtl/fub/stream_drain_ctrl.sv \
   projects/components/rapids/rtl/rapids_fub/
```

### Step 2: Create Unified SRAM Controller
- Copy `sram_controller.sv` and `sram_controller_unit.sv`
- Rename interfaces: `axi_rd_*` → `fill_*`, `axi_wr_*` → `drain_*`

### Step 3: Create AXIS Wrappers
- `axis_to_fill_wrapper.sv`: AXIS Slave → fill interface
- `drain_to_axis_wrapper.sv`: drain interface → AXIS Master

### Step 4: Create Data Path Integration
- `rapids_sink_path.sv`: axis_to_fill_wrapper → unified_sram_controller → axi_write_engine
- `rapids_source_path.sv`: axi_read_engine → unified_sram_controller → drain_to_axis_wrapper

### Step 5: Create Scheduler Groups
- Adapt STREAM's scheduler_group for sink path
- Adapt STREAM's scheduler_group for source path
- Create array wrappers for 8 channels each

### Step 6: Create Top-Level Integration
- `rapids_core.sv`: Combines sink and source paths
- `rapids_top_ch8.sv`: Full 8-channel instantiation

---

## Test Strategy

### Phase 1 Tests (Port from STREAM)
1. **FUB Tests:** unified_sram_controller, axis wrappers
2. **Integration Tests:** sink path end-to-end, source path end-to-end
3. **System Tests:** bidirectional transfer

### Test Reuse from STREAM
- sram_controller tests → unified_sram_controller tests
- axi_read_engine tests → copy as-is
- axi_write_engine tests → copy as-is
- scheduler_group tests → adapt for sink/source variants

---

## Success Criteria for Phase 1

1. **Sink path works:** AXIS in → Memory out
2. **Source path works:** Memory in → AXIS out
3. **Bidirectional works:** Both paths operating concurrently
4. **All STREAM tests pass** (adapted for RAPIDS)
5. **MonBus integration works** (event reporting)

---

## Phase 2 Roadmap (Future)

After Phase 1 is stable:
1. Add chunk-based length tracking
2. Add alignment fixup logic (from current RAPIDS)
3. Expand to 16 channels
4. Add exponential credit encoding
5. Add circular buffer support
6. Add RAPIDS-specific descriptor format

---

## Questions Resolved

**Q: Should we create rapids_line as separate component?**
A: No - build RAPIDS incrementally within existing structure.

**Q: Unified vs separate SRAM controllers?**
A: Unified with generic fill/drain interfaces (Option B selected).

**Q: Start with aligned/line-based first?**
A: Yes - Phase 1 uses STREAM simplifications, Phase 2 adds complexity.

---

**Document Version:** 1.0
**Created By:** Claude (Documentation and implementation support)
