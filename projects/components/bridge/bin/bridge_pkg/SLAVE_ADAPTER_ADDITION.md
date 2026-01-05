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

# Slave Adapter Addition to Bridge Architecture

**Date:** 2025-11-08
**Status:** In Progress
**Purpose:** Add slave-side timing isolation and protocol conversion layer

---

## Architecture Change

### Current Architecture (Incomplete)

```
External Master → [Bridge Top] → [Master Adapter] → [Crossbar] → DIRECT → External Slaves
                                   (has axi4_slave_*                         (no isolation!)
                                    timing wrapper)
```

**Missing:** Slave-side timing isolation and protocol conversion!

### Target Architecture (Complete)

```
External Master → [Bridge Top] → [Master Adapter] → [Crossbar] → [Slave Adapter] → External Slaves
                                   (axi4_slave_*)                  (axi4_master_*
                                                                    or AXI→APB/AXIL)
```

---

## Slave Adapter Purpose

**Every slave adapter contains:**

### For AXI4 Slaves:
1. **axi4_master_wr** - Write channel timing isolation (skid buffers)
2. **axi4_master_rd** - Read channel timing isolation (skid buffers)
3. **Final stage** before external slave interface

### For APB Slaves:
1. **axi4_to_apb** - Protocol converter
2. **AXI4 to APB protocol translation**
3. **Timing isolation via converter's internal buffers**

### For AXI4-Lite Slaves:
1. **axi4_to_axil** - Protocol converter
2. **AXI4 full to AXI4-Lite conversion**
3. **Timing isolation**

---

## Signal Flow (AXI4 Slave Example)

### Write Path:

```
Crossbar → ddr_axi_aw* (internal) → [axi4_master_wr]  → ddr_axi_aw* (external) → DDR Slave
                                     ├─ fub_axi_*: INPUT from crossbar
                                     └─ m_axi_*: OUTPUT to external slave
```

**Key Insight:** The `axi4_master_wr` module:
- **Input side** (`fub_axi_*`): Receives AXI4 from crossbar (slave interface)
- **Output side** (`m_axi_*`): Drives AXI4 to external slave (master interface)
- **Purpose:** Provides final skid buffers, breaks combinatorial paths

---

## Implementation Plan

### Phase 1: Create Slave Adapter Generator ✅ (DONE)

**File:** `bridge_pkg/generators/slave_adapter_generator.py`

**Features:**
- Generates `{slave_name}_adapter.sv` modules
- Supports AXI4, APB, AXIL protocols
- Uses SignalNaming for consistent signal naming
- Port direction inversion (adapter is intermediary)

**Generated Module:**
```systemverilog
module ddr_adapter (
    input  logic aclk,
    input  logic aresetn,

    // Crossbar interface (AXI4 from crossbar)
    input  logic [3:0]  ddr_axi_awid,      // From crossbar
    input  logic [31:0] ddr_axi_awaddr,
    // ... (all AXI4 signals)
    output logic        ddr_axi_awready,   // To crossbar

    // External slave interface
    output logic [3:0]  ddr_axi_awid,      // To external DDR
    output logic [31:0] ddr_axi_awaddr,
    // ... (all AXI4 signals)
    input  logic        ddr_axi_awready    // From external DDR
);

    // axi4_master_wr instance
    axi4_master_wr #(...) u_master_wr (
        .fub_axi_* (ddr_axi_*),  // Crossbar interface
        .m_axi_*   (ddr_axi_*)   // External interface
    );

endmodule
```

### Phase 2: Integrate into Bridge Module Generator (IN PROGRESS)

**Changes Needed:**

1. **Bridge Top-Level Changes:**
   - Slave ports remain at top level (external interface)
   - Add internal crossbar-to-slave-adapter signals

2. **Crossbar Instance:**
   - Connect crossbar slave outputs to internal signals (not external ports)

3. **Add Slave Adapter Instantiations:**
   - One adapter per slave
   - Between crossbar outputs and external slave ports

4. **Update generate_all() Method:**
   - Generate slave adapter files
   - Add to file list

**Modified Architecture:**

```systemverilog
module bridge_1x2_wr (
    input  logic aclk,
    input  logic aresetn,

    // Master 0: cpu (external)
    input  logic [31:0]  cpu_axi_awaddr,
    output logic         cpu_axi_awready,
    // ...

    // Slave 0: ddr (external)
    output logic [31:0]  ddr_axi_awaddr,   // External port
    input  logic         ddr_axi_awready,
    // ...

    // Slave 1: sram (external)
    output logic [31:0]  sram_axi_awaddr,  // External port
    input  logic         sram_axi_awready
    // ...
);

    // Internal crossbar-to-slave signals
    logic [31:0]  xbar_ddr_axi_awaddr;     // Crossbar → ddr adapter
    logic         xbar_ddr_axi_awready;
    // ...

    logic [31:0]  xbar_sram_axi_awaddr;    // Crossbar → sram adapter
    logic         xbar_sram_axi_awready;
    // ...

    // Master adapter
    cpu_adapter u_cpu_adapter (...);

    // Crossbar
    bridge_1x2_wr_xbar u_xbar (
        .cpu_* (...),
        .ddr_axi_* (xbar_ddr_axi_*),     // Internal signals
        .sram_axi_* (xbar_sram_axi_*)    // Internal signals
    );

    // Slave adapters (NEW!)
    ddr_adapter u_ddr_adapter (
        .ddr_axi_* (xbar_ddr_axi_*),     // From crossbar (internal)
        .ddr_axi_* (ddr_axi_*)           // To external (external ports)
    );

    sram_adapter u_sram_adapter (
        .sram_axi_* (xbar_sram_axi_*),   // From crossbar (internal)
        .sram_axi_* (sram_axi_*)         // To external (external ports)
    );

endmodule
```

**Wait - Signal Naming Conflict!**

There's a naming conflict: Both crossbar-facing and external-facing use same prefix (`ddr_axi_*`).

**Solution: Use different internal prefixes:**

```systemverilog
// Internal crossbar→adapter signals
logic [31:0]  xbar_to_ddr_awaddr;
logic         xbar_to_ddr_awready;

// Slave adapter instance
ddr_adapter u_ddr_adapter (
    // Crossbar interface (internal)
    .xbar_awaddr (xbar_to_ddr_awaddr),
    .xbar_awready (xbar_to_ddr_awready),
    // External interface (bridge ports)
    .ext_awaddr (ddr_axi_awaddr),
    .ext_awready (ddr_axi_awready)
);
```

**Even Better: Hierarchical naming in slave adapter:**

```systemverilog
module ddr_adapter (
    // Crossbar interface
    input  logic [31:0] xbar_awaddr,    // Use 'xbar_' prefix
    output logic        xbar_awready,

    // External slave interface
    output logic [31:0] ext_awaddr,     // Use 'ext_' prefix
    input  logic        ext_awready
);

    axi4_master_wr u_master_wr (
        .fub_axi_awaddr (xbar_awaddr),  // From crossbar
        .fub_axi_awready (xbar_awready),
        .m_axi_awaddr (ext_awaddr),     // To external
        .m_axi_awready (ext_awready)
    );

endmodule
```

---

## File Changes Required

### 1. slave_adapter_generator.py ✅ (DONE)
- Created generator class
- Supports AXI4/APB/AXIL
- Uses correct signal naming

### 2. bridge_module_generator.py (TODO)
- Add slave adapter instantiation method
- Change slave port connections to go through adapters
- Update generate_all() to create adapter files

### 3. crossbar_generator.py (TODO - minor)
- May need internal signal prefix option

---

## Testing Plan

After implementation:

1. **Regenerate bridge_1x2_wr**
2. **Verilator lint** - Check for connection errors
3. **Run CocoTB tests** - Verify functional correctness
4. **Check waveforms** - Verify skid buffer operation

---

## Benefits

1. ✅ **Complete timing isolation** - Skid buffers on both sides
2. ✅ **Protocol conversion support** - APB/AXIL slaves work correctly
3. ✅ **Matching architecture** - Master and slave sides symmetric
4. ✅ **Proper boundary** - Clean crossbar AXI4 ↔ external protocol
5. ✅ **As requested** - User specifically asked for axi4_master_* wrappers

---

## Current Status

- ✅ Phase 1 Complete: Slave adapter generator created
- 🔄 Phase 2 In Progress: Integration into bridge module generator
- ⏳ Phase 3 Pending: Testing and verification

---

**Next Steps:**
1. Update `bridge_module_generator.py` to instantiate slave adapters
2. Add internal signal generation for crossbar-to-adapter connections
3. Update `generate_all()` method
4. Test with bridge_1x2_wr regeneration

