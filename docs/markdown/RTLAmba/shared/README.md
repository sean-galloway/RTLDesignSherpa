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

# AMBA Shared Infrastructure

**Location:** `rtl/amba/shared/`
**Test Location:** Tested indirectly via protocol modules
**Status:** ✅ Production Ready

---

## Overview

The shared subsystem provides foundational infrastructure modules used throughout the AMBA ecosystem. These modules implement common functionality for monitors, arbiters, clock domain crossing, and utility functions. They are typically not instantiated directly by users but form the backbone of higher-level protocol modules.

### Key Features

- ✅ **Monitor Infrastructure:** Complete AXI/APB transaction monitoring system
- ✅ **CDC Utilities:** Clock domain crossing with proper synchronization
- ✅ **Arbitration:** Monitor bus arbitration for multi-agent systems
- ✅ **Address Generation:** AXI burst address calculation
- ✅ **Clock Gating:** Power management infrastructure
- ✅ **Production Ready:** Extensively tested through protocol modules

---

## Module Categories

### Monitor Infrastructure (7 modules)

Core modules that implement the AXI/APB monitoring functionality:

| Module | Purpose | Key Features | Documentation |
|--------|---------|--------------|---------------|
| **axi_monitor_base** | Core monitor logic | Transaction tracking, timeout detection, event generation | [axi_monitor_base.md](axi_monitor_base.md) |
| **axi_monitor_filtered** | Monitor wrapper with filtering | 3-level packet filtering, configuration validation | [axi_monitor_filtered.md](axi_monitor_filtered.md) |
| **axi_monitor_trans_mgr** | Transaction table management | Out-of-order tracking, ID management | [axi_monitor_trans_mgr.md](axi_monitor_trans_mgr.md) |
| **axi_monitor_reporter** | Event packet generation | Error/completion/performance packets | [axi_monitor_reporter.md](axi_monitor_reporter.md) |
| **axi_monitor_timeout** | Timeout detection | Configurable thresholds, multi-channel monitoring | [axi_monitor_timeout.md](axi_monitor_timeout.md) |
| **axi_monitor_timer** | Frequency-invariant timer | Configurable tick generation | [axi_monitor_timer.md](axi_monitor_timer.md) |
| **amba_clock_gate_ctrl** | Clock gating control | Dynamic gating, idle detection | [amba_clock_gate_ctrl.md](amba_clock_gate_ctrl.md) |

### Arbitration (4 modules)

Monitor bus arbiters for aggregating packets from multiple monitors:

| Module | Purpose | Algorithm | Documentation |
|--------|---------|-----------|---------------|
| **monbus_arbiter** | Basic monitor bus arbiter | Round-robin with priority | [monbus_arbiter.md](monbus_arbiter.md) |
| **arbiter_monbus_common** | Common arbiter infrastructure | Shared logic for all arbiters | [arbiter_monbus_common.md](arbiter_monbus_common.md) |
| **arbiter_rr_pwm_monbus** | Round-robin PWM arbiter | Equal priority rotation | [arbiter_rr_pwm_monbus.md](arbiter_rr_pwm_monbus.md) |
| **arbiter_wrr_pwm_monbus** | Weighted round-robin arbiter | Configurable priority weights | [arbiter_wrr_pwm_monbus.md](arbiter_wrr_pwm_monbus.md) |

### AXI Utilities (5 modules)

Utility modules for AXI protocol handling:

| Module | Purpose | Use Case | Documentation |
|--------|---------|----------|---------------|
| **axi_gen_addr** | Burst address generation | Calculate next address for INCR/WRAP bursts | [axi_gen_addr.md](axi_gen_addr.md) |
| **axi_master_rd_splitter** | Read channel splitter | Split AXI read across boundaries | [axi_master_rd_splitter.md](axi_master_rd_splitter.md) |
| **axi_master_wr_splitter** | Write channel splitter | Split AXI write with response consolidation | [axi_master_wr_splitter.md](axi_master_wr_splitter.md) |
| **axi_split_combi** | Combined splitter | Bidirectional split (read + write) | [axi_split_combi.md](axi_split_combi.md) |
| **cdc_handshake** | Clock domain crossing | Dual-clock valid/ready handshake | [cdc_handshake.md](cdc_handshake.md) |

---

## Monitor Infrastructure

### axi_monitor_base

**Purpose:** Core AXI/AXI-Lite transaction monitoring engine

**Key Features:**
- Transaction table tracking (up to MAX_TRANSACTIONS concurrent)
- Out-of-order completion support
- Timeout detection with configurable thresholds
- Multiple packet types: error, completion, timeout, performance, debug
- Integrated with monitor_pkg for standardized events

**Parameters:**
```systemverilog
module axi_monitor_base #(
    parameter int UNIT_ID             = 9,      // 4-bit unit identifier
    parameter int AGENT_ID            = 99,     // 8-bit agent identifier
    parameter int MAX_TRANSACTIONS    = 16,     // Transaction table size
    parameter int ADDR_WIDTH          = 32,
    parameter int ID_WIDTH            = 8,      // 0 for AXI-Lite
    parameter bit IS_READ             = 1,      // 1=read, 0=write
    parameter bit IS_AXI              = 1,      // 1=AXI, 0=AXI-Lite
    parameter bit ENABLE_PERF_PACKETS = 0,
    parameter bit ENABLE_DEBUG_MODULE = 0
)
```

**Interfaces:**
- Command phase (AW/AR): addr, id, len, size, burst, valid, ready
- Data channel (W/R): id, last, resp, valid, ready
- Response channel (B): id, resp, valid, ready
- Monitor bus output: 64-bit packets

**Configuration:**
- Packet type enables: error, completion, timeout, threshold, performance, debug
- Timeout counters: addr, data, resp (0-15 ticks)
- Frequency selection for timer (0-15)
- Threshold config: active transactions, latency

**Generated Packets:**
- **ERROR**: Protocol violations, response errors
- **COMPL**: Transaction completion notifications
- **TIMEOUT**: Channel timeout events
- **THRESH**: Threshold crossings (active transactions, latency)
- **PERF**: Performance metrics
- **DEBUG**: Detailed transaction traces

**Usage:**
Used internally by all `*_mon` wrapper modules. Not typically instantiated directly.

---

### axi_monitor_filtered

**Purpose:** Wrapper for axi_monitor_base with configurable packet filtering

**Key Features:**
- 3-level filtering hierarchy:
  - Level 1: Packet type masking (drop entire types)
  - Level 2: Error routing (separate error handling)
  - Level 3: Event code masking (fine-grained filtering)
- Optional pipeline stage for timing closure
- Configuration validation with error detection

**Parameters:**
```systemverilog
module axi_monitor_filtered #(
    // All axi_monitor_base parameters, plus:
    parameter bit ENABLE_FILTERING    = 1,
    parameter bit ADD_PIPELINE_STAGE  = 0
)
```

**Filtering Configuration:**
```systemverilog
input  logic [15:0] cfg_axi_pkt_mask,      // Drop packets by type
input  logic [15:0] cfg_axi_error_mask,    // Mask specific error events
input  logic [15:0] cfg_axi_timeout_mask,  // Mask specific timeout events
input  logic [15:0] cfg_axi_compl_mask,    // Mask specific completion events
input  logic [15:0] cfg_axi_thresh_mask,   // Mask specific threshold events
input  logic [15:0] cfg_axi_perf_mask,     // Mask specific performance events
input  logic [15:0] cfg_axi_debug_mask     // Mask specific debug events
```

**Filtering Logic:**
```
Unfiltered packet → Packet type check (pkt_mask)
                  → Event code check (event_mask)
                  → Optional pipeline stage
                  → Filtered packet output
```

**Usage:**
Used by all `axi4_*_mon` and `axil4_*_mon` modules. Provides fine-grained control over which events are reported.

---

### axi_monitor_trans_mgr

**Purpose:** Transaction table management for monitor

**Key Features:**
- Tracks up to MAX_TRANSACTIONS concurrent transactions
- Maintains transaction state (idle, addr_received, data_in_progress, waiting_resp, completed)
- Out-of-order completion support
- Data-before-address handling
- Timeout detection integration

**Transaction Table Entry:**
```systemverilog
typedef struct packed {
    logic [ADDR_WIDTH-1:0] addr;
    logic [ID_WIDTH-1:0]   id;
    logic [7:0]            len;
    logic [2:0]            size;
    logic [1:0]            burst;
    logic [31:0]           timestamp;
    bus_trans_state_t      state;
    logic [7:0]            beat_count;
} bus_transaction_t;
```

**Operations:**
- **Allocate:** Find free slot for new transaction
- **Update:** Modify transaction state/beat count
- **Complete:** Mark transaction done, free slot
- **Lookup:** Find transaction by ID
- **Timeout Check:** Detect stalled transactions

**Usage:**
Instantiated within axi_monitor_base. Handles all transaction lifecycle management.

---

### axi_monitor_reporter

**Purpose:** Generate standardized 64-bit monitor bus packets

**Key Features:**
- Consolidates events from trans_mgr and timeout modules
- Formats packets according to monitor_pkg::event_packet_t
- Handles packet priorities and arbitration
- Integrates error flags, completion notifications, performance metrics

**Packet Format (64 bits):**
```
[63:60] Packet Type (4 bits)
[59:57] Protocol (3 bits)
[56:53] Event Code (4 bits)
[52:47] Channel ID (6 bits)
[46:43] Unit ID (4 bits)
[42:35] Agent ID (8 bits)
[34:0]  Event Data (35 bits)
```

**Event Data Content (depends on packet type):**
- **ERROR**: Address[34:0] or error code
- **COMPL**: Transaction ID + beat count
- **TIMEOUT**: Channel identifier + timeout count
- **THRESH**: Threshold value + current value
- **PERF**: Latency or throughput metric
- **DEBUG**: State machine info + transaction data

**Usage:**
Instantiated within axi_monitor_base. Converts internal events to standardized packets.

---

### axi_monitor_timeout

**Purpose:** Detect timeout conditions on AXI channels

**Key Features:**
- Separate counters for AR/AW, R/W, B channels
- Configurable timeout thresholds (0-15 ticks)
- Integration with timer tick for time base
- Per-transaction timeout tracking

**Configuration:**
```systemverilog
input logic [3:0] cfg_addr_cnt,  // Address channel timeout (ticks)
input logic [3:0] cfg_data_cnt,  // Data channel timeout (ticks)
input logic [3:0] cfg_resp_cnt   // Response channel timeout (ticks)
```

**Timeout Detection:**
```
Timer tick → Increment active channel counters
          → Compare with threshold
          → Generate timeout event if exceeded
          → Reset counter on channel activity
```

**Usage:**
Instantiated within axi_monitor_base. Generates timeout packets for reporter.

---

### axi_monitor_timer

**Purpose:** Frequency-invariant timer for monitor infrastructure

**Key Features:**
- Configurable frequency divider (0-15 selection)
- Generates periodic tick for timeout counters
- Independent of system clock frequency
- Low overhead implementation

**Configuration:**
```systemverilog
input logic [3:0] cfg_freq_sel   // Frequency selection (0-15)
```

**Frequency Table:**
```
cfg_freq_sel = 0  → Tick every 1 cycle
cfg_freq_sel = 1  → Tick every 2 cycles
cfg_freq_sel = 2  → Tick every 4 cycles
...
cfg_freq_sel = 15 → Tick every 32768 cycles
```

**Usage:**
Instantiated within axi_monitor_base. Provides time base for timeout detection.

---

### amba_clock_gate_ctrl

**Purpose:** Dynamic clock gating controller for AMBA modules

**Key Features:**
- Idle detection with configurable threshold
- Automatic gating after idle period
- Fast ungating on activity (0 cycles)
- Safe clock gating (glitch-free)
- Clock cycle counting for power analysis

**Parameters:**
```systemverilog
module amba_clock_gate_ctrl #(
    parameter int CG_IDLE_COUNT_WIDTH = 4  // Idle counter width
)
```

**Configuration:**
```systemverilog
input logic                       cfg_cg_enable,      // Enable gating
input logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count  // Idle cycles before gate
```

**Status:**
```systemverilog
output logic cg_gating,    // Currently gated
output logic [31:0] cg_clk_count  // Cumulative gated cycles
```

**Gating Logic:**
```
Activity detection → Reset idle counter
No activity → Increment idle counter
Idle >= threshold && enable → Gate clock
Activity detected → Ungate immediately
```

**Usage:**
Used by all `*_cg` clock-gated variants (axi4, axil4, axis, apb monitors).

---

## Arbitration

### monbus_arbiter

**Purpose:** Round-robin arbiter for monitor bus aggregation

**Key Features:**
- N-way arbitration (up to 16 agents)
- Fair round-robin scheduling
- Zero bubble overhead (back-to-back grants)
- Configurable arbiter width

**Parameters:**
```systemverilog
module monbus_arbiter #(
    parameter int N = 4,          // Number of requesters
    parameter int DATA_WIDTH = 64 // Monitor bus width
)
```

**Interfaces:**
```systemverilog
// Per-agent inputs
input  logic [N-1:0]            i_request,
input  logic [N-1:0][DATA_WIDTH-1:0] i_data,
output logic [N-1:0]            o_grant,

// Aggregated output
output logic                    o_valid,
output logic [DATA_WIDTH-1:0]   o_data
```

**Arbitration:**
```
Request[0..N-1] → Round-robin priority rotation
                → Grant highest priority requester
                → Output granted packet
                → Rotate priority for fairness
```

**Usage:**
Aggregate monitor packets from multiple AXI/APB monitors into single stream.

**Example:**
```systemverilog
// 4 AXI monitors → 1 monitor bus
monbus_arbiter #(.N(4), .DATA_WIDTH(64)) u_arb (
    .i_request({mon3_valid, mon2_valid, mon1_valid, mon0_valid}),
    .i_data({mon3_pkt, mon2_pkt, mon1_pkt, mon0_pkt}),
    .o_grant({mon3_ready, mon2_ready, mon1_ready, mon0_ready}),
    .o_valid(agg_valid),
    .o_data(agg_pkt)
);
```

---

### arbiter_monbus_common

**Purpose:** Shared arbitration logic for all monitor bus arbiters

**Key Features:**
- Reusable priority encoding
- Mask-based round-robin
- Optimized for monitor bus (64-bit packets)

**Usage:**
Base module for arbiter_rr_pwm_monbus and arbiter_wrr_pwm_monbus.

---

### arbiter_rr_pwm_monbus

**Purpose:** Round-robin arbiter with PWM output for monitor bus

**Key Features:**
- Equal priority round-robin
- PWM output mode for power management
- Optimized for packet streams

**Usage:**
Alternative to monbus_arbiter with PWM support.

---

### arbiter_wrr_pwm_monbus

**Purpose:** Weighted round-robin arbiter for monitor bus

**Key Features:**
- Configurable per-agent weights
- Weighted priority allocation
- Fair service guarantees

**Configuration:**
```systemverilog
input logic [N-1:0][7:0] cfg_weights  // Per-agent weight (0-255)
```

**Scheduling:**
```
High-weight agents get more grants
Low-weight agents get fewer grants
Maintains fairness across epochs
```

**Usage:**
Use when different monitors have different importance levels.

---

## AXI Utilities

### axi_gen_addr

**Purpose:** Generate next address for AXI burst transactions

**Key Features:**
- Supports INCR, WRAP, FIXED burst types
- Handles all AXI data widths (32-512 bits)
- Proper address alignment
- Boundary wrapping for WRAP bursts

**Parameters:**
```systemverilog
module axi_gen_addr #(
    parameter int AW = 32,    // Address width
    parameter int DW = 32,    // Data width
    parameter int ODW = 32,   // Output data width (for width conversion)
    parameter int LEN = 8     // Length field width
)
```

**Inputs:**
```systemverilog
input logic [AW-1:0] curr_addr,   // Current address
input logic [2:0]    size,        // axsize (0-7)
input logic [1:0]    burst,       // axburst (FIXED/INCR/WRAP)
input logic [LEN-1:0] len          // axlen (burst length)
```

**Outputs:**
```systemverilog
output logic [AW-1:0] next_addr,        // Next address in burst
output logic [AW-1:0] next_addr_align   // Aligned next address
```

**Address Calculation:**

**INCR (0x01):**
```
next_addr = curr_addr + (1 << size)
```

**WRAP (0x10):**
```
// Wrap at boundary = (len + 1) * (1 << size)
boundary = (len + 1) << size;
next_addr = (curr_addr + (1 << size)) & ~(boundary - 1);
```

**FIXED (0x00):**
```
next_addr = curr_addr  // Same address
```

**Usage:**
Used by axi4_to_apb_convert for burst decomposition. Also useful for any AXI address calculation.

**Example:**
```systemverilog
axi_gen_addr #(.AW(32), .DW(64), .ODW(32)) u_addr_gen (
    .curr_addr(32'h1000),
    .size(3'b010),        // 4 bytes
    .burst(2'b01),        // INCR
    .len(8'd3),           // 4 beats
    .next_addr(next_addr) // → 32'h1004, 32'h1008, 32'h100C
);
```

---

### axi_master_rd_splitter

**Purpose:** Split AXI read into separate AR and R channels

**Key Features:**
- Independent AR and R skid buffers
- Configurable buffer depths
- Zero-latency path option

**Usage:**
Decouple AR and R channels for timing closure or protocol adaptation.

---

### axi_master_wr_splitter

**Purpose:** Split AXI write into separate AW, W, and B channels

**Key Features:**
- Independent channel buffering
- AW-W synchronization
- B channel response routing

**Usage:**
Decouple write channels for complex write paths.

---

### axi_split_combi

**Purpose:** Combined read + write splitter

**Key Features:**
- Bidirectional split (all 5 AXI channels)
- Shared configuration
- Compact implementation

**Usage:**
Full AXI split for complex bridges or adapters.

---

### cdc_handshake

**Purpose:** Clock domain crossing with valid/ready handshake

**Key Features:**
- Dual-clock asynchronous CDC
- Data + control crossing
- Gray-code free pointer-based
- Safe for arbitrary clock ratios
- Zero data loss

**Parameters:**
```systemverilog
module cdc_handshake #(
    parameter int DATA_WIDTH = 8
)
```

**Interfaces:**
```systemverilog
// Source clock domain
input  logic                  clk_src,
input  logic                  rst_src_n,
input  logic                  src_valid,
output logic                  src_ready,
input  logic [DATA_WIDTH-1:0] src_data,

// Destination clock domain
input  logic                  clk_dst,
input  logic                  rst_dst_n,
output logic                  dst_valid,
input  logic                  dst_ready,
output logic [DATA_WIDTH-1:0] dst_data
```

**FSM States:**

**Source Domain:**
```
S_IDLE         → Ready for new data
S_WAIT_ACK     → Waiting for destination ack
S_WAIT_ACK_CLR → Waiting for ack to clear
```

**Destination Domain:**
```
D_IDLE         → Waiting for request
D_WAIT_READY   → Request received, waiting for ready
D_WAIT_REQ_CLR → Ack sent, waiting for request clear
```

**Timing:**
- Latency: 3-5 cycles (depends on clock ratio)
- Synchronization: 3-stage shift register
- Handshake: 4-phase (req → ack → req_clr → ack_clr)

**Usage:**
Used extensively in axi4_to_apb_shim for cmd/rsp CDC. General-purpose CDC utility.

**Example:**
```systemverilog
cdc_handshake #(.DATA_WIDTH(32)) u_cdc (
    .clk_src(clk_100mhz),
    .rst_src_n(rst_n),
    .src_valid(cmd_valid),
    .src_ready(cmd_ready),
    .src_data(cmd_data),

    .clk_dst(clk_200mhz),
    .rst_dst_n(rst_n),
    .dst_valid(req_valid),
    .dst_ready(req_ready),
    .dst_data(req_data)
);
```

---

## Testing

Shared modules are tested indirectly through higher-level protocol modules:

```bash
# Monitor infrastructure tested via monitor tests
pytest val/amba/test_axi4_*_mon.py -v
pytest val/amba/test_axil4_*_mon.py -v
pytest val/amba/test_apb_monitor.py -v

# CDC tested via shims
pytest val/integ_amba/test_axi2apb_shim.py -v

# Address generation tested via conversion
pytest val/integ_amba/test_axi2apb_shim.py -v
```

---

## Design Notes

### Monitor Infrastructure

**Architecture:**
```
Transaction → axi_monitor_trans_mgr (track state)
           → axi_monitor_timeout (detect stalls)
           → axi_monitor_reporter (generate packets)
           → axi_monitor_filtered (apply filters)
           → Monitor bus output
```

**Packet Flow:**
```
axi_monitor_base → Unfiltered packets
                 → axi_monitor_filtered (if enabled)
                 → Filtered packets
                 → FIFO/arbiter
                 → System monitor bus
```

### When to Use Each Module

**✅ Use axi_monitor_base When:**
- Creating custom monitor variants
- Need full control over filtering
- Integrating with custom infrastructure

**✅ Use axi_monitor_filtered When:**
- Standard monitor usage
- Need packet filtering
- Using with monitor bus aggregation

**✅ Use cdc_handshake When:**
- Clock domain crossing required
- Valid/ready protocol
- Arbitrary clock ratios
- Safe data transfer needed

**✅ Use axi_gen_addr When:**
- Implementing AXI bridges
- Burst address calculation
- Protocol conversion

**✅ Use monbus_arbiter When:**
- Multiple monitors on same bus
- Need fair arbitration
- Aggregating monitor streams

---

## Configuration Best Practices

### Monitor Configuration

**Functional Debug Mode (Recommended Default):**
```systemverilog
.cfg_error_enable(1'b1),        // Catch errors
.cfg_compl_enable(1'b1),        // Track completions
.cfg_timeout_enable(1'b1),      // Detect hangs
.cfg_perf_enable(1'b0),         // ⚠️ DISABLE (high traffic)
.cfg_debug_enable(1'b0)         // Only if needed
```

**Performance Analysis Mode:**
```systemverilog
.cfg_error_enable(1'b1),        // Still catch errors
.cfg_compl_enable(1'b0),        // ⚠️ DISABLE
.cfg_timeout_enable(1'b0),
.cfg_perf_enable(1'b1),         // Enable metrics
.cfg_debug_enable(1'b0)
```

**⚠️ NEVER enable cfg_compl_enable and cfg_perf_enable together!** This causes packet congestion.

### Timeout Configuration

**Conservative (Slow Peripherals):**
```systemverilog
.cfg_freq_sel(4'd8),     // Slower tick rate
.cfg_addr_cnt(4'd15),    // Long timeout
.cfg_data_cnt(4'd15),
.cfg_resp_cnt(4'd15)
```

**Aggressive (Fast Detection):**
```systemverilog
.cfg_freq_sel(4'd0),     // Fast tick rate
.cfg_addr_cnt(4'd3),     // Short timeout
.cfg_data_cnt(4'd3),
.cfg_resp_cnt(4'd3)
```

### Clock Gating Configuration

**Aggressive Gating:**
```systemverilog
.cfg_cg_enable(1'b1),
.cfg_cg_idle_count(4'd1)  // Gate after 1 idle cycle
```

**Conservative Gating:**
```systemverilog
.cfg_cg_enable(1'b1),
.cfg_cg_idle_count(4'd10) // Gate after 10 idle cycles
```

---

## Performance Characteristics

### Monitor Overhead

**Resource Usage (per monitor):**
- axi_monitor_base: ~500 LUTs, ~400 FFs
- axi_monitor_filtered: +50 LUTs, +30 FFs
- Total: ~550 LUTs, ~430 FFs per monitor

**Packet Generation Rate:**
- Completion packets: 1 per transaction
- Error packets: As needed (protocol violations)
- Timeout packets: Low frequency (cfg_freq_sel dependent)
- Performance packets: 1 per N transactions (configurable)

### CDC Latency

**cdc_handshake:**
- Minimum: 6 cycles (src → dst → src)
- Typical: 8-12 cycles
- Maximum: Depends on clock ratio

### Arbitration

**monbus_arbiter:**
- Latency: 1 cycle
- Throughput: 1 packet/cycle (no bubbles)
- Fairness: Perfect round-robin

---

## Synthesis Notes

### Clock Gating

**amba_clock_gate_ctrl:**
- Implements glitch-free clock gating
- Use vendor clock gating cells for best results
- Requires proper clock gating constraints

**Constraints (example):**
```tcl
set_clock_gating_check -setup 0.1 [get_clocks aclk]
set_dont_touch [get_cells */u_clock_gate_ctrl/*]
```

### CDC Constraints

**cdc_handshake:**
```tcl
set_false_path -from [get_clocks clk_src] -to [get_clocks clk_dst]
set_false_path -from [get_clocks clk_dst] -to [get_clocks clk_src]

# Constrain synchronizer paths
set_max_delay -from */r_req_src -to */r_req_sync[0] 10.0
set_max_delay -from */r_ack_dst -to */r_ack_sync[0] 10.0
```

---

## Related Documentation

### RTL Design Sherpa Documentation

- **[RTLAmba Overview](../overview.md)** - Complete AMBA architecture
- **[AXI4 Monitors](../axi4/README.md)** - Uses monitor infrastructure
- **[APB Monitor](../apb/README.md)** - Uses monitor infrastructure
- **[Shims](../shims/README.md)** - Uses CDC and address generation

### Monitor Package

- **[Monitor Package Spec](../includes/monitor_package_spec.md)** - Event packet format

### Source Code

- RTL: `rtl/amba/shared/`
- Monitor package: `rtl/amba/monitor_pkg.sv`
- Tests: Indirect via `val/amba/test_*_mon.py`

---

## Summary

The shared subsystem provides essential infrastructure:

**Monitor Infrastructure:**
- Complete transaction tracking and event generation
- Configurable filtering and timeout detection
- Standardized 64-bit event packets
- Multi-protocol support (AXI, APB, AXIS)

**Arbitration:**
- Fair round-robin scheduling
- Weighted priority support
- Zero-overhead aggregation

**Utilities:**
- Clock domain crossing (cdc_handshake)
- AXI address generation (axi_gen_addr)
- Channel splitting (axi_*_splitter)
- Clock gating (amba_clock_gate_ctrl)

**Usage Pattern:**
Most users interact with higher-level protocol modules (axi4_master_rd_mon, etc.) which internally use these shared components. Direct instantiation is rare except for custom implementations.

---

**Last Updated:** 2025-10-24

---

## Navigation

- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**
