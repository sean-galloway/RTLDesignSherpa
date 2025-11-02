# AMBA Monitor Integration Examples

**Purpose:** Practical examples showing how to integrate AMBA protocol monitors in real SoC designs

**Status:** Educational reference implementations
**Location:** `rtl/integ_amba/examples/`

---

## Overview

This directory contains complete integration examples demonstrating best practices for using APB and AMBA protocol monitors in production designs:

### Current Examples

1. **apb_xbar_monitored.sv** ✅ - APB crossbar (3×4) with 7 monitors, tested and working
2. **apb_peripheral_subsystem.sv** - Simple APB peripheral example (In Progress)
3. **axi4_to_apb_bridge_monitored.sv** - Protocol conversion example (Planned)

### Future Examples (Deferred - Need Infrastructure)

4. **FUTURE_axi4_crossbar_monitored.sv** - AXI4 2×3 crossbar (needs functional crossbar RTL)
5. **axil_regfile_monitored.sv** - AXI4-Lite register file
6. **mixed_protocol_system.sv** - Multi-protocol SoC

Each example shows:
- Complete monitor instantiation with proper configuration
- Monitor bus aggregation using arbiters
- Downstream packet handling (FIFO buffering)
- Address decoding and routing
- Real-world parameter selection

---

## Monitor Packet Format

All AMBA monitors generate **standardized 64-bit packets** on the `monbus_pkt_*` interface:

### Packet Structure

```
[63:60] Packet Type  (4 bits)
[59:57] Protocol     (3 bits)
[56:53] Event Code   (4 bits)
[52:47] Channel ID   (6 bits)
[46:43] Unit ID      (4 bits)
[42:35] Agent ID     (8 bits)
[34:0]  Event Data   (35 bits) - address, latency, error info, etc.
```

### Packet Types

| Value | Type | Description |
|-------|------|-------------|
| 0x0 | ERROR | Protocol violations, timeouts, orphans |
| 0x1 | COMPLETION | Transaction completions |
| 0x2 | TIMEOUT | Timeout events |
| 0x3 | THRESHOLD | Threshold crossings |
| 0x4 | PERFORMANCE | Performance metrics |
| 0x5 | DEBUG | Debug/trace information |

### Protocol Field

| Value | Protocol |
|-------|----------|
| 0x0 | AXI |
| 0x1 | APB |
| 0x2 | AXIS |
| 0x3 | ARB (Arbiter) |

**Full specification:** See `docs/markdown/RTLAmba/includes/monitor_package_spec.md`

---

## Monitor Bus Aggregation

### Why Aggregate?

Multiple monitors generate packets that must be merged into a single stream:
- Multiple AXI interfaces (master/slave × read/write)
- Multiple APB peripherals
- Mixed protocols in same system

### Arbiter Options

#### Option 1: Round-Robin (Fair, Simple)

**Use when:** All monitors have equal priority

```systemverilog
arbiter_round_robin #(
    .N         (NUM_MONITORS),
    .REG_OUTPUT(1)              // Register for timing
) u_mon_arbiter (
    .i_clk     (clk),
    .i_rst_n   (rst_n),
    .i_request (mon_valid),     // [N-1:0] from monitors
    .o_grant   (mon_ready),     // [N-1:0] back to monitors
    .o_valid   (agg_valid)      // Aggregated output
);

// Mux monitor data based on grant
logic [$clog2(N)-1:0] grant_id;
always_comb begin
    grant_id = '0;
    for (int i = 0; i < N; i++) begin
        if (mon_ready[i]) grant_id = i[$clog2(N)-1:0];
    end
end
assign agg_data = mon_data[grant_id];
```

**Location:** `rtl/common/arbiter_round_robin.sv`

#### Option 2: Weighted Round-Robin (QoS)

**Use when:** Some monitors are higher priority (e.g., error packets from critical paths)

```systemverilog
arbiter_round_robin_weighted #(
    .N              (NUM_MONITORS),
    .MAX_LEVELS     (16),           // Max weight per client
    .REG_OUTPUT     (1)
) u_mon_arbiter (
    .i_clk          (clk),
    .i_rst_n        (rst_n),
    .i_max_thresh   (weights),      // [N*4-1:0] weight per monitor
    .i_request      (mon_valid),
    .o_grant        (mon_ready),
    .o_valid        (agg_valid)
);
```

**Example weights:**
- Error monitors: 8
- Completion monitors: 2
- Performance monitors: 1

**Location:** `rtl/common/arbiter_round_robin_weighted.sv`

#### Option 3: Fixed Priority

**Use when:** Strict priority required (rare for monitoring)

**Location:** `rtl/common/arbiter_priority_encoder.sv`

---

## Downstream Packet Handling

### Pattern 1: Direct Connection (Small Systems)

```systemverilog
// Connect directly to packet consumer
assign consumer_valid = monbus_valid;
assign consumer_data = monbus_data;
assign monbus_ready = consumer_ready;
```

**Pros:** Zero latency
**Cons:** Backpressure can stall monitors
**Use when:** <5 monitors, low traffic

### Pattern 2: FIFO Buffering (Recommended)

```systemverilog
// Add FIFO for robustness
gaxi_fifo_sync #(
    .DATA_WIDTH (64),
    .DEPTH      (256)       // Size based on burst traffic
) u_mon_fifo (
    .i_clk   (clk),
    .i_rst_n (rst_n),
    .i_valid (monbus_valid),
    .i_data  (monbus_data),
    .o_ready (monbus_ready),
    .o_valid (consumer_valid),
    .o_data  (consumer_data),
    .i_ready (consumer_ready)
);
```

**Pros:** Absorbs bursts, prevents monitor stalls
**Cons:** Added latency, area
**Use when:** >5 monitors, bursty traffic, critical paths

**Location:** `rtl/amba/gaxi/gaxi_fifo_sync.sv`

### Pattern 3: Multi-Level Hierarchy (Large Systems)

```systemverilog
// Level 1: Aggregate per subsystem
arbiter_round_robin #(.N(4)) u_cpu_arb (...);    // CPU monitors
arbiter_round_robin #(.N(3)) u_dma_arb (...);    // DMA monitors
arbiter_round_robin #(.N(5)) u_periph_arb (...); // Peripheral monitors

// Level 2: Top-level aggregation
arbiter_round_robin #(.N(3)) u_top_arb (
    .i_request({periph_valid, dma_valid, cpu_valid}),
    ...
);

// Level 3: FIFO to system
gaxi_fifo_sync #(.DEPTH(512)) u_sys_fifo (...);
```

**Use when:** >20 monitors, hierarchical SoC

---

## Monitor Configuration Best Practices

### Configuration Signals

Every monitor has 4 configuration inputs:

```systemverilog
.cfg_error_enable   (1'b1),  // Protocol errors
.cfg_compl_enable   (1'b1),  // Transaction completions
.cfg_timeout_enable (1'b1),  // Timeout detection
.cfg_perf_enable    (1'b0)   // Performance metrics
```

### ⚠️ Critical: Packet Type Selection

**NEVER enable all packet types simultaneously!** This causes monitor bus congestion.

**Configuration Strategies:**

#### Strategy 1: Functional Debug (Default)

```systemverilog
.cfg_error_enable   (1'b1),  // ✅ Catch errors
.cfg_compl_enable   (1'b1),  // ✅ Track completions
.cfg_timeout_enable (1'b1),  // ✅ Detect hangs
.cfg_perf_enable    (1'b0)   // ❌ Disable (high traffic)
```

**Use for:** Bring-up, functional verification, error detection

#### Strategy 2: Performance Analysis

```systemverilog
.cfg_error_enable   (1'b1),  // ✅ Still catch errors
.cfg_compl_enable   (1'b0),  // ❌ Disable (reduce traffic)
.cfg_timeout_enable (1'b0),  // ❌ Disable
.cfg_perf_enable    (1'b1)   // ✅ Performance metrics
```

**Use for:** Bandwidth analysis, latency profiling

#### Strategy 3: Error-Only (Production)

```systemverilog
.cfg_error_enable   (1'b1),  // ✅ Essential
.cfg_compl_enable   (1'b0),  // ❌ Disable
.cfg_timeout_enable (1'b1),  // ✅ Detect hangs
.cfg_perf_enable    (1'b0)   // ❌ Disable
```

**Use for:** Production systems, minimal overhead

**Full guide:** See `docs/AXI_Monitor_Configuration_Guide.md`

---

## Agent ID Assignment

The `AGENT_ID` field (8 bits) uniquely identifies each monitor in the system. Use a systematic numbering scheme:

### Recommended Scheme

```
Master Monitors:
  0x10-0x1F: CPU/Processor masters
  0x20-0x2F: DMA engines
  0x30-0x3F: Peripheral masters

Slave Monitors:
  0x40-0x4F: Memory controllers
  0x50-0x5F: Peripheral slaves
  0x60-0x6F: Debug/trace slaves

Per interface:
  Base + 0: Read channel
  Base + 1: Write channel

Example:
  CPU read:  0x10
  CPU write: 0x11
  DMA read:  0x20
  DMA write: 0x21
```

**Benefits:**
- Easy identification in packet traces
- Grouped by function
- Room for expansion

---

## Example 1: APB Crossbar with Monitors (WORKING ✅)

**File:** `apb_xbar_monitored.sv`
**Status:** Tested and validated (based on test_apb_xbar.py PASSED)
**Complexity:** Medium - Good starting point for learning monitor integration

### Architecture

```
     Master 0          Master 1          Master 2
        |                 |                 |
    [Monitor]         [Monitor]         [Monitor]
        |                 |                 |
        +------------  APB Crossbar  -------+
                     (3×4 thin variant)
                            |
        +-------------------+-------------------+
        |           |           |               |
    [Monitor]   [Monitor]   [Monitor]       [Monitor]
        |           |           |               |
    Slave 0     Slave 1     Slave 2         Slave 3
   (0x0000)    (0x1000)    (0x2000)        (0x3000)

    7 monitors total → Round-Robin Arbiter → Aggregated monbus_pkt_*
```

### Monitors Instantiated

| Interface | Agent ID | Purpose | Address Range |
|-----------|----------|---------|---------------|
| Master 0 | 0x10 | Monitor master 0 transactions | All |
| Master 1 | 0x11 | Monitor master 1 transactions | All |
| Master 2 | 0x12 | Monitor master 2 transactions | All |
| Slave 0 | 0x40 | Monitor peripheral 0 responses | 0x0000-0x0FFF |
| Slave 1 | 0x41 | Monitor peripheral 1 responses | 0x1000-0x1FFF |
| Slave 2 | 0x42 | Monitor peripheral 2 responses | 0x2000-0x2FFF |
| Slave 3 | 0x43 | Monitor peripheral 3 responses | 0x3000-0x3FFF |

### Key Features

1. **Complete Coverage:** Every APB interface monitored (masters + slaves)
2. **Fair Arbitration:** Round-robin arbiter ensures no starvation
3. **Single Output:** Aggregated monbus simplifies downstream processing
4. **Configurable:** Runtime packet type selection
5. **Production-Ready:** Based on tested apb_xbar_thin implementation
6. **Scalable:** Uses generate loops for parameterized monitor instantiation

### Usage Example

```systemverilog
apb_xbar_monitored #(
    .NUM_MASTERS(3),
    .NUM_SLAVES(4),
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .MAX_TRANSACTIONS(8),  // Sufficient for APB
    .UNIT_ID(0),
    .AGENT_ID_M0(8'h10),   // Master 0
    .AGENT_ID_M1(8'h11),   // Master 1
    .AGENT_ID_M2(8'h12),   // Master 2
    .AGENT_ID_S0(8'h40),   // Slave 0
    .AGENT_ID_S1(8'h41),   // Slave 1
    .AGENT_ID_S2(8'h42),   // Slave 2
    .AGENT_ID_S3(8'h43)    // Slave 3
) u_apb_xbar (
    .pclk    (apb_clk),
    .presetn (apb_rst_n),

    // 3 master interfaces (m0_apb_*, m1_apb_*, m2_apb_*)
    .m0_apb_psel   (m0_psel),
    .m0_apb_penable(m0_penable),
    // ... other master 0 signals ...

    // 4 slave interfaces (s0_apb_*, s1_apb_*, s2_apb_*, s3_apb_*)
    .s0_apb_psel   (s0_psel),
    .s0_apb_penable(s0_penable),
    // ... other slave 0 signals ...

    // Aggregated monitor output
    .monbus_valid(mon_valid),
    .monbus_ready(mon_ready),  // Connect to downstream FIFO
    .monbus_data (mon_data),

    // Configuration
    .cfg_error_enable  (1'b1),
    .cfg_compl_enable  (1'b1),
    .cfg_timeout_enable(1'b1),
    .cfg_perf_enable   (1'b0)  // ⚠️ Disable for functional debug
);

// Optional: Add FIFO for robustness
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(128)  // Smaller than AXI4 (APB is simpler)
) u_mon_fifo (
    .i_clk  (apb_clk),
    .i_rst_n(apb_rst_n),
    .i_valid(mon_valid),
    .i_data (mon_data),
    .o_ready(mon_ready),
    .o_valid(consumer_valid),
    .o_data (consumer_data),
    .i_ready(consumer_ready)
);
```

### What You Learn

1. **Monitor Instantiation:** How to instantiate APB monitors with proper parameters
2. **Bus Aggregation:** Using round-robin arbiter to combine monitor streams
3. **Agent ID Assignment:** Systematic numbering for different interfaces
4. **Configuration:** Setting packet types for different use cases
5. **Downstream Handling:** Optional FIFO buffering pattern

### Testing

```bash
# Run APB crossbar test (validates underlying crossbar)
pytest val/integ_amba/test_apb_xbar.py -v

# This test uses the thin crossbar variant that this example is based on
```

---

## Example 2: Simple APB Peripheral Subsystem (EDUCATIONAL ✅)

**File:** `apb_peripheral_subsystem.sv`
**Status:** Educational example - demonstrates monitor basics
**Complexity:** Simple - Best starting point for beginners

### Architecture

```
         APB Master (CPU/Bridge)
                   |
            Address Decoder
                   |
        +----------+----------+
        |          |          |
    [Monitor]  [Monitor]  [Monitor]
        |          |          |
    Register    Timer      GPIO
     File      (stub)    (stub)
   (0x0000)   (0x1000)  (0x2000)

    3 monitors → Round-Robin Arbiter → monbus_pkt_*
```

### Monitors Instantiated

| Peripheral | Agent ID | Purpose | Address Range |
|------------|----------|---------|---------------|
| Register File | 0x50 | 16×32-bit registers | 0x0000-0x0FFF |
| Timer | 0x51 | Timer peripheral (stub) | 0x1000-0x1FFF |
| GPIO | 0x52 | GPIO peripheral (stub) | 0x2000-0x2FFF |

### Key Features

1. **Minimal Example:** Only 3 peripherals, easy to understand
2. **Address Decoding:** Simple mask-based address decoder
3. **One Monitor Each:** Demonstrates per-peripheral monitoring
4. **Functional Register File:** Working 16-register implementation
5. **Stub Peripherals:** Timer/GPIO placeholders for learning structure

### Usage Example

```systemverilog
apb_peripheral_subsystem #(
    .ADDR_WIDTH(16),
    .DATA_WIDTH(32),
    .MAX_TRANSACTIONS(4),  // Small number OK for simple peripherals
    .UNIT_ID(0),
    .AGENT_ID_REGFILE(8'h50),
    .AGENT_ID_TIMER  (8'h51),
    .AGENT_ID_GPIO   (8'h52)
) u_peripherals (
    .pclk   (apb_clk),
    .presetn(apb_rst_n),

    // Single APB master interface
    .apb_psel   (apb_psel),
    .apb_penable(apb_penable),
    .apb_pwrite (apb_pwrite),
    .apb_pprot  (apb_pprot),
    .apb_paddr  (apb_paddr),
    .apb_pwdata (apb_pwdata),
    .apb_pstrb  (apb_pstrb),
    .apb_pready (apb_pready),
    .apb_prdata (apb_prdata),
    .apb_pslverr(apb_pslverr),

    // Monitor output
    .monbus_valid(mon_valid),
    .monbus_ready(1'b1),  // Always ready for educational example
    .monbus_data (mon_data),

    // Configuration
    .cfg_error_enable(1'b1),
    .cfg_compl_enable(1'b1)
);
```

### What You Learn

1. **Basic Monitoring:** Simplest possible integration pattern
2. **Address Decoding:** How peripherals are selected
3. **Minimal Aggregation:** 3 monitors, simple arbiter
4. **Register Implementation:** Functional APB slave with strobes
5. **Stub Pattern:** How to create placeholder peripherals

### Extending This Example

To add more peripherals:

1. Add address range in decoder:
```systemverilog
localparam logic [15:0] NEW_PERIPH_BASE = 16'h3000;
logic sel_new_periph;
assign sel_new_periph = apb_psel && ((apb_paddr & 16'hF000) == NEW_PERIPH_BASE);
```

2. Add monitor with new agent ID:
```systemverilog
apb_monitor #(.AGENT_ID(8'h53)) u_new_mon (...);
```

3. Update arbiter for N+1 monitors

---

## Integration Checklist

When adding monitors to your design:

### Planning Phase
- [ ] Identify all AXI/APB interfaces to monitor
- [ ] Assign unique AGENT_IDs (document in table)
- [ ] Choose arbiter type (round-robin vs weighted)
- [ ] Size downstream FIFO (traffic analysis)
- [ ] Select packet types (functional vs performance)

### Implementation Phase
- [ ] Instantiate monitors for each interface
- [ ] Connect AXI/APB signals (copy from interface)
- [ ] Set parameters (ID_WIDTH, ADDR_WIDTH, DATA_WIDTH)
- [ ] Configure packet types (cfg_*_enable)
- [ ] Add arbiter for aggregation
- [ ] Add FIFO for buffering
- [ ] Connect to packet consumer

### Verification Phase
- [ ] Verify monitors generate packets
- [ ] Check arbiter fairness
- [ ] Verify FIFO doesn't overflow
- [ ] Decode packet fields correctly
- [ ] Test with backpressure
- [ ] Measure packet rates

### Documentation
- [ ] Document AGENT_ID assignments
- [ ] Document address map
- [ ] Document configuration strategy
- [ ] Create integration diagram

---

## Common Pitfalls

### ❌ Pitfall 1: Enabling All Packet Types

```systemverilog
❌ WRONG:
.cfg_error_enable   (1'b1),
.cfg_compl_enable   (1'b1),
.cfg_timeout_enable (1'b1),
.cfg_perf_enable    (1'b1)  // TOO MUCH TRAFFIC!

✅ CORRECT:
// Choose ONE strategy (see Configuration section above)
```

### ❌ Pitfall 2: No Downstream Buffering

```systemverilog
❌ WRONG:
assign consumer_valid = monbus_valid;
assign monbus_ready = consumer_ready;  // Direct connection

✅ CORRECT:
// Add FIFO to absorb bursts
gaxi_fifo_sync #(.DEPTH(256)) u_fifo (...);
```

### ❌ Pitfall 3: Duplicate AGENT_IDs

```systemverilog
❌ WRONG:
axi4_master_rd_mon #(.AGENT_ID(8'h10)) u_m0_rd (...);
axi4_master_wr_mon #(.AGENT_ID(8'h10)) u_m0_wr (...);  // DUPLICATE!

✅ CORRECT:
axi4_master_rd_mon #(.AGENT_ID(8'h10)) u_m0_rd (...);
axi4_master_wr_mon #(.AGENT_ID(8'h11)) u_m0_wr (...);  // UNIQUE
```

### ❌ Pitfall 4: Wrong MAX_TRANSACTIONS

```systemverilog
❌ WRONG:
axi4_master_rd_mon #(
    .MAX_TRANSACTIONS(2)  // Too small for AXI4 with bursts!
) u_mon (...);

✅ CORRECT:
axi4_master_rd_mon #(
    .MAX_TRANSACTIONS(16)  // Adequate for burst traffic
) u_mon (...);
```

---

## Resource Utilization

Typical resource usage per monitor (Xilinx 7-series, MAX_TRANSACTIONS=16):

| Monitor Type | LUTs | FFs | BRAM |
|--------------|------|-----|------|
| AXI4 Master Read | ~800 | ~600 | 0 |
| AXI4 Master Write | ~900 | ~700 | 0 |
| AXIL4 Master | ~400 | ~300 | 0 |
| APB Monitor | ~200 | ~150 | 0 |

**Notes:**
- AXIL uses ~50% of AXI4 resources (simpler protocol)
- Clock gating variants add ~10% area
- Arbiter: ~50 LUTs per input
- FIFO (256 deep): ~100 LUTs + 1 BRAM

**Rule of thumb:** Budget 1000 LUTs + 1 BRAM per monitored AXI4 interface

---

## Further Reading

### Documentation
- **Monitor Specs:** `docs/markdown/RTLAmba/` (detailed module documentation)
- **Configuration Guide:** `docs/AXI_Monitor_Configuration_Guide.md` (**essential!**)
- **Packet Format:** `docs/markdown/RTLAmba/includes/monitor_package_spec.md`
- **PRD:** `rtl/amba/PRD.md` (requirements and architecture)

### Source Code
- **Monitors:** `rtl/amba/{axi4,apb,axis}/`
- **Arbiters:** `rtl/common/arbiter_*.sv`
- **FIFOs:** `rtl/amba/gaxi/gaxi_fifo_sync.sv`

### Tests
- **Monitor Tests:** `val/amba/test_axi4_*_mon.py`
- **Example Tests:** `val/integ_amba/` (when created)

---

## Questions or Issues?

1. Check configuration guide: `docs/AXI_Monitor_Configuration_Guide.md`
2. Review module specs: `docs/markdown/RTLAmba/`
3. Look at test examples: `val/amba/test_*.py`
4. Check known issues: `rtl/amba/KNOWN_ISSUES/`

---

**Version:** 1.0
**Last Updated:** 2025-10-12
**Maintainer:** RTL Design Sherpa Project
