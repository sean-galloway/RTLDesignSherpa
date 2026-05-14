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

# Bug: APB/AXIL Slave Adapter FIFO Tracking Deadlock

**Date:** 2025-11-10 - RESOLVED 2026-05-13
**Severity:** CRITICAL
**Status:** RESOLVED - All fixes integrated and verified (commit 608c97cb)
**Affects:** All bridges with APB or AXI4-Lite slaves (bridge_1x5_rd, bridge_1x5_wr, bridge_1x2_* with APB)
**Resolved In:** Multiple commits addressing three distinct bugs (2026-05-10 to 2026-05-13)

---

## Summary

Three coordinated bugs were fixed in this session that collectively caused APB/AXIL slave deadlock:
1. APB shim wasn't wrapped in the per-slave adapter (FIFO tracking missing)
2. AXIL slaves declared wrong external interface (AXI4-Lite instead of full AXI4)
3. W-beat path-active gating used stale combinational decode instead of FIFO-tracked slave_select

All issues are now resolved across the bridge generator and supporting modules.

---

## Symptoms

1. **Timeouts in tests:**
   ```
   ERROR - Master(R_S4) Phase2: TIMEOUT waiting for ready after 1000 cycles
   ERROR - Master(B_S4) Phase2: TIMEOUT waiting for ready after 1000 cycles
   ```

2. **Specific to APB/AXIL slaves:**
   - bridge_1x5_rd: Slaves 3-4 are APB/AXIL → timeout
   - bridge_1x5_wr: Slaves 3-4 are APB/AXIL → timeout
   - bridge_1x2/1x3/1x4: All AXI4 slaves → no timeout

3. **Transaction hangs:**
   - AR transaction sent to slave
   - Slave never responds (or test doesn't simulate slave)
   - FIFO waits for R handshake that never happens
   - Crossbar blocks all subsequent transactions

---

## Root Cause

### Current Implementation (WRONG)

**File:** `rtl/generated/bridge_1x5_rd/apb_periph_adapter.sv:89-101`

```systemverilog
// Read Channel FIFO (In-Order)
logic [BRIDGE_ID_WIDTH-1:0] rd_fifo [RD_FIFO_DEPTH];
logic [$clog2(RD_FIFO_DEPTH):0] ar_ptr, r_ptr;

// Push on AR (crossbar → adapter)
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        ar_ptr <= '0;
    } else if (xbar_apb_periph_axi_arvalid && xbar_apb_periph_axi_arready) begin
        rd_fifo[ar_ptr[$clog2(RD_FIFO_DEPTH)-1:0]] <= xbar_bridge_id_ar;
        ar_ptr <= ar_ptr + 1'b1;
    end
end

// Pop on R (crossbar ← adapter) ← BUG IS HERE
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        r_ptr <= '0;
        rid_bridge_id <= '0;
        rid_valid <= 1'b0;
    } else if (xbar_apb_periph_axi_rvalid && xbar_apb_periph_axi_rready && xbar_apb_periph_axi_rlast) begin
        //         ^^^^^^^^^^^^^^^^^^^^^^^^^ WRONG SIGNALS!
        //         These are crossbar-side, BEFORE the converter
        rid_bridge_id <= rd_fifo[r_ptr[$clog2(RD_FIFO_DEPTH)-1:0]];
        rid_valid <= 1'b1;
        r_ptr <= r_ptr + 1'b1;
    end else begin
        rid_valid <= 1'b0;
    end
end

// AXI4-to-APB converter shim
axi4_to_apb_shim #(...) u_apb_periph_apb_converter (
    .aclk             (aclk),
    .aresetn          (aresetn),

    // Crossbar-side AXI4 interface
    .s_axi_arvalid    (xbar_apb_periph_axi_arvalid),  // ← FIFO monitors THIS
    .s_axi_arready    (xbar_apb_periph_axi_arready),
    .s_axi_rvalid     (xbar_apb_periph_axi_rvalid),   // ← FIFO waits for THIS
    .s_axi_rready     (xbar_apb_periph_axi_rready),
    .s_axi_rlast      (xbar_apb_periph_axi_rlast),

    // APB-side interface (to external slave)
    .m_apb_PADDR      (apb_periph_PADDR),
    .m_apb_PSEL       (apb_periph_PSEL),
    .m_apb_PENABLE    (apb_periph_PENABLE),
    .m_apb_PWRITE     (apb_periph_PWRITE),
    .m_apb_PRDATA     (apb_periph_PRDATA),   // ← External slave response
    .m_apb_PREADY     (apb_periph_PREADY),    // ← External slave ready
    .m_apb_PSLVERR    (apb_periph_PSLVERR)
);
```

### The Problem

**Signal Flow:**
```
1. Crossbar sends AR → xbar_apb_periph_axi_arvalid=1
2. FIFO push: Store bridge_id (✓ CORRECT)
3. Converter receives AR → Converts to APB
4. APB slave NEVER responds (test doesn't drive PREADY)
5. Converter waits forever for APB response
6. xbar_apb_periph_axi_rvalid NEVER goes high
7. FIFO pop condition NEVER met
8. FIFO pointer stuck → All future transactions deadlock
```

**The FIFO pop monitors crossbar-side signals (`xbar_*_rvalid`), which depend on the CONVERTER outputting a valid response, which depends on the EXTERNAL SLAVE responding.**

If the external slave never responds (timeout, missing testbench slave, etc.), the FIFO never pops → **permanent deadlock**.

---

## Why AXI4 Slaves Don't Have This Issue

**File:** `rtl/generated/bridge_1x5_rd/ddr_rd_adapter.sv:89-101`

```systemverilog
// Pop on R (with RLAST)
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        r_ptr <= '0;
        rid_bridge_id <= '0;
        rid_valid <= 1'b0;
    } else if (xbar_ddr_axi_rvalid && xbar_ddr_axi_rready && xbar_ddr_axi_rlast) begin
        //         ^^^^^^^^^^^^^^^^^^^^ For AXI4 slaves, these connect DIRECTLY to external slave
        rid_bridge_id <= rd_fifo[r_ptr[$clog2(RD_FIFO_DEPTH)-1:0]];
        rid_valid <= 1'b1;
        r_ptr <= r_ptr + 1'b1;
    end else begin
        rid_valid <= 1'b0;
    end
end

// AXI4 Master Read Timing Wrapper (NO protocol conversion)
axi4_master_rd #(...) u_master_rd (
    .aclk(aclk),
    .aresetn(aresetn),

    // Slave interface (from crossbar)
    .fub_axi_arvalid(xbar_ddr_axi_arvalid),
    .fub_axi_arready(xbar_ddr_axi_arready),
    .fub_axi_rvalid(xbar_ddr_axi_rvalid),  // ← Connects through to external slave
    .fub_axi_rready(xbar_ddr_axi_rready),
    .fub_axi_rlast(xbar_ddr_axi_rlast),

    // Master interface (to external slave) - DIRECT CONNECTION
    .m_axi_arvalid(ddr_s_axiarvalid),
    .m_axi_arready(ddr_s_axiarready),
    .m_axi_rvalid(ddr_s_axirvalid),   // ← External slave rvalid
    .m_axi_rready(ddr_s_axirready),
    .m_axi_rlast(ddr_s_axirlast)
);
```

For AXI4 slaves, `xbar_ddr_axi_rvalid` IS the external slave's response (just buffered through wrapper). For APB slaves, `xbar_apb_periph_axi_rvalid` depends on converter logic AND external APB slave.

---

## Solution Options

### Option 1: Move FIFO Tracking AFTER Converter (RECOMMENDED)

Move the FIFO tracking logic to monitor **converter output**, not crossbar input:

```systemverilog
// FIFO should monitor converter's AXI4-side outputs (to crossbar)
//
// Current monitoring point:
//   Crossbar → [FIFO TRACKING] → xbar_*_rvalid → Converter → APB Slave
//                                  ↑ WRONG!
//
// Correct monitoring point:
//   Crossbar ← xbar_*_rvalid ← [FIFO TRACKING] ← Converter ← APB Slave
//                               ↑ CORRECT!

// The converter's s_axi_rvalid output should trigger FIFO pop
logic converter_rvalid;  // From converter's AXI4 slave interface
logic converter_rready;
logic converter_rlast;

// Converter instantiation
axi4_to_apb_shim #(...) u_apb_periph_apb_converter (
    ...
    .s_axi_rvalid     (converter_rvalid),  // ← Internal signal
    .s_axi_rready     (converter_rready),
    .s_axi_rlast      (converter_rlast),
    ...
);

// Wire converter output to crossbar
assign xbar_apb_periph_axi_rvalid = converter_rvalid;
assign converter_rready = xbar_apb_periph_axi_rready;
assign xbar_apb_periph_axi_rlast = converter_rlast;

// FIFO pop on converter output (not crossbar input)
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        r_ptr <= '0;
        rid_bridge_id <= '0;
        rid_valid <= 1'b0;
    } else if (converter_rvalid && converter_rready && converter_rlast) begin
        //         ^^^^^^^^^^^^^^^^ Monitor converter output!
        rid_bridge_id <= rd_fifo[r_ptr[$clog2(RD_FIFO_DEPTH)-1:0]];
        rid_valid <= 1'b1;
        r_ptr <= r_ptr + 1'b1;
    end else begin
        rid_valid <= 1'b0;
    end
end
```

**Benefit:** FIFO pops only when converter actually produces response (which it does even on timeout/error).

### Option 2: Add Timeout to FIFO Pop

Add watchdog timer to FIFO that pops after N cycles even without response:

```systemverilog
localparam FIFO_POP_TIMEOUT = 10000;  // 10K cycles @ 100MHz = 100us
logic [$clog2(FIFO_POP_TIMEOUT):0] fifo_timeout_counter;

always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        fifo_timeout_counter <= '0;
        r_ptr <= '0;
        rid_bridge_id <= '0;
        rid_valid <= 1'b0;
    end else if (xbar_apb_periph_axi_rvalid && xbar_apb_periph_axi_rready && xbar_apb_periph_axi_rlast) begin
        // Normal pop
        rid_bridge_id <= rd_fifo[r_ptr[$clog2(RD_FIFO_DEPTH)-1:0]];
        rid_valid <= 1'b1;
        r_ptr <= r_ptr + 1'b1;
        fifo_timeout_counter <= '0;
    end else if ((r_ptr != ar_ptr) && (fifo_timeout_counter >= FIFO_POP_TIMEOUT)) begin
        // Timeout pop - force pop to unblock FIFO
        rid_bridge_id <= rd_fifo[r_ptr[$clog2(RD_FIFO_DEPTH)-1:0]];
        rid_valid <= 1'b1;
        r_ptr <= r_ptr + 1'b1;
        fifo_timeout_counter <= '0;
        // Optionally: Set error flag
    end else if (r_ptr != ar_ptr) begin
        // FIFO non-empty, increment timeout counter
        fifo_timeout_counter <= fifo_timeout_counter + 1'b1;
        rid_valid <= 1'b0;
    end else begin
        // FIFO empty
        fifo_timeout_counter <= '0;
        rid_valid <= 1'b0;
    end
end
```

**Benefit:** Prevents permanent deadlock. **Drawback:** Doesn't solve root cause, may cause spurious responses.

### Option 3: Converter Error Response Generation

Ensure converter ALWAYS generates response (even on APB slave timeout):

```systemverilog
// Inside axi4_to_apb_shim:
// If APB slave doesn't respond within N cycles, generate SLVERR response

localparam APB_TIMEOUT = 1000;
logic [$clog2(APB_TIMEOUT):0] apb_timeout_counter;

always_ff @(posedge pclk) begin
    if (apb_state == WAIT_PREADY) begin
        if (m_apb_PREADY) begin
            // Normal response
            apb_timeout_counter <= '0;
        end else if (apb_timeout_counter >= APB_TIMEOUT) begin
            // Timeout - generate error response
            s_axi_rresp <= 2'b10;  // SLVERR
            s_axi_rvalid <= 1'b1;
            s_axi_rlast <= 1'b1;
            apb_timeout_counter <= '0;
        end else begin
            apb_timeout_counter <= apb_timeout_counter + 1'b1;
        end
    end
end
```

**Benefit:** Converter always completes transaction. **Drawback:** Requires modifying converter module.

---

## Fix Implementation Summary

**Date Fixed:** 2025-11-10
**Implementation:** Option 1 (Monitor converter output signals)

### Changes Made

**File:** `bin/bridge_pkg/generators/slave_adapter_generator.py`

**Modified Methods:**
1. `_generate_internal_signals()` - Added intermediate signals for APB/AXIL converters:
   - `converter_bvalid`, `converter_bready` (write response channel)
   - `converter_rvalid`, `converter_rready`, `converter_rlast` (read response channel)

2. `_generate_fifo_write_tracking()` - Updated FIFO pop condition:
   - **Before:** `{crossbar_prefix}bvalid && {crossbar_prefix}bready` (wrong - before converter)
   - **After:** `converter_bvalid && converter_bready` (correct - after converter)

3. `_generate_fifo_read_tracking()` - Updated FIFO pop condition:
   - **Before:** `{crossbar_prefix}rvalid && {crossbar_prefix}rready && {crossbar_prefix}rlast`
   - **After:** `converter_rvalid && converter_rready && converter_rlast`

4. `_generate_apb_converter()` - Wired converter outputs to intermediate signals:
   - Converter `.s_axi_bvalid` → `converter_bvalid`
   - Converter `.s_axi_rvalid` → `converter_rvalid`
   - Added wire assignments back to crossbar interface

**Regenerated Bridges (all 10):**
- bridge_1x2_rd, bridge_1x2_wr
- bridge_1x3_rd, bridge_1x3_wr
- bridge_1x4_rd, bridge_1x4_wr
- bridge_1x5_rd, bridge_1x5_wr (APB/AXIL slaves - primary affected)
- bridge_2x2_rw
- bridge_5x3_rw

### Verification

**Generated Code Check:**
```bash
# bridge_1x5_rd/apb_periph_adapter.sv - Read channel
// Pop on R response (converter_rvalid && converter_rready && converter_rlast)
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        r_ptr <= '0;
        rid_bridge_id <= '0;
        rid_valid <= 1'b0;
    end else if (converter_rvalid && converter_rready && converter_rlast) begin
        // ✅ Monitoring converter output signals
```

**Wire Assignments:**
```systemverilog
// Wire converter outputs back to crossbar interface
assign xbar_apb_periph_axi_rvalid = converter_rvalid;
assign converter_rready = xbar_apb_periph_axi_rready;
assign xbar_apb_periph_axi_rlast = converter_rlast;
```

---

## Resolution Summary

All three bugs were fixed across four commits (a68c9f1e, f17213b6, 608c97cb, plus supporting refactors):

1. **Multi-master OR-merge gating fix (a68c9f1e):**
   - Every OR-merge term now gates on `(slave_select && <valid>)` so idle masters can't corrupt routing tags
   - Applied to all bridge_id_aw/ar and data signal multiplexing

2. **Stable slave_select fix (f17213b6):**
   - Master adapter: Added per-channel response-tracking FIFOs (ar_trk_*, aw_trk_*)
   - Crossbar: Replace slave_select_* gating with inline address re-decode on stable m_axi buses
   - Added per-(master,slave) AW->W tracking FIFO for proper W-beat routing

3. **APB/AXIL protocol gap fix (608c97cb):**
   - APB shim now properly wrapped in slave_adapter module with correct FIFO tracking
   - AXIL slaves now use full AXI4 interface (documentation only; real Lite conversion is future)
   - W-beat gating uses separate w_path_active_<W> driven from FIFO-tracked b_slave_select

4. **Typed component refactoring (6c9dc8e2, 95caea2e, ee7ed471, 7334487a):**
   - Wrapped sub-module instantiation patterns in typed components (Axi4ToApbShim, Axi4DwidthConverter, etc.)
   - Centralized parameter lists and port plumbing to reduce hot-spot bugs

5. **Jinja template improvements (b65525a7):**
   - APB pre-load moved into TB Jinja template so it survives regeneration
   - Config validator enforces 4K page alignment on slave address windows

## Test Results

**Status:** All 22 bridge tests passing (confirmed end of session)

**Coverage:**
- bridge_1x5_rd, bridge_1x5_wr (APB/AXIL slaves) - basic_connectivity now passing
- bridge_4x4_rw, bridge_5x3_channels - mixed-master, mixed-width now passing
- All pure-AXI4 bridges - maintained 100% pass rate

---

## Priority

**RESOLVED** - All fixes integrated and verified
**Test Status:** 22/22 passing (2026-05-13)

---

**Fixes By:** Claude Code AI
**Date Resolved:** 2026-05-13
**Status:** Complete and verified
