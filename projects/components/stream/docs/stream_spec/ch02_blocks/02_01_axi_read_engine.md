# AXI Read Engine Specification

**Module:** `axi_read_engine.sv`
**Location:** `rtl/stream_fub/`
**Status:** To be created

---

## Overview

The AXI Read Engine autonomously executes AXI read transactions to fetch source data from system memory. It accepts requests from the Scheduler, decides burst lengths internally based on configuration and SRAM space, and reports completion back.

### Key Features

- **Autonomous burst decision:** Engine decides burst length based on internal config
- **Performance modes:** Low, Medium, High (compile-time parameter)
- **SRAM interface:** Writes fetched data to shared SRAM
- **Streaming pipeline:** No FSM in data path (arbiter-based control)
- **Completion feedback:** Reports beats moved via done_strobe

---

## Performance Modes

### Low Performance Mode (`PERFORMANCE = "LOW"`)

**Target:** Area-optimized, tutorial examples

**Characteristics:**
- Single outstanding transaction
- Minimal logic
- Simple sequential operation
- ~250 LUTs (estimate)

**Parameters:**
```systemverilog
parameter string PERFORMANCE = "LOW";
parameter int    MAX_BURST_LEN = 8;       // Fixed 8-beat bursts
parameter int    MAX_OUTSTANDING = 1;     // Single transaction
parameter bit    ENABLE_PIPELINE = 0;     // No pipelining
```

### Medium Performance Mode (`PERFORMANCE = "MEDIUM"`)

**Target:** Balanced area/performance for typical FPGA

**Characteristics:**
- 2-4 outstanding transactions
- Basic pipelining
- Adaptive burst sizing
- ~400 LUTs (estimate)

**Parameters:**
```systemverilog
parameter string PERFORMANCE = "MEDIUM";
parameter int    MAX_BURST_LEN = 16;      // Up to 16-beat bursts
parameter int    MAX_OUTSTANDING = 4;     // 4 outstanding
parameter bit    ENABLE_PIPELINE = 1;     // Basic pipelining
```

### High Performance Mode (`PERFORMANCE = "HIGH"`)

**Target:** Maximum throughput for ASIC or high-end FPGA

**Characteristics:**
- 8+ outstanding transactions
- Full pipelining
- Dynamic burst optimization
- ~600 LUTs (estimate)

**Parameters:**
```systemverilog
parameter string PERFORMANCE = "HIGH";
parameter int    MAX_BURST_LEN = 256;     // Up to 256-beat bursts
parameter int    MAX_OUTSTANDING = 16;    // 16 outstanding
parameter bit    ENABLE_PIPELINE = 1;     // Full pipelining
```

---

## Interface

### Parameters

```systemverilog
parameter string PERFORMANCE = "LOW";      // "LOW", "MEDIUM", "HIGH"
parameter int    ADDR_WIDTH = 64;          // Address bus width
parameter int    DATA_WIDTH = 512;         // Data bus width
parameter int    MAX_BURST_LEN = 8;        // Max burst length (perf-dependent)
parameter int    MAX_OUTSTANDING = 1;      // Max outstanding transactions
parameter bit    ENABLE_PIPELINE = 0;      // Pipeline enable
parameter int    SRAM_DEPTH = 1024;        // SRAM depth (for space check)
```

### Ports

**Clock and Reset:**
```systemverilog
input  logic                    aclk;
input  logic                    aresetn;
```

**Configuration:**
```systemverilog
input  logic [7:0]              cfg_burst_len;     // Configured burst length
input  logic                    cfg_enable;        // Engine enable
```

**Scheduler Request Interface:**
```systemverilog
input  logic                    datard_valid;           // Scheduler requests read
output logic                    datard_ready;           // Engine grants access
input  logic [ADDR_WIDTH-1:0]   datard_addr;            // Start address
input  logic [31:0]             datard_beats_remaining; // Total beats to read
input  logic [3:0]              datard_channel_id;      // Channel ID

// Completion feedback
output logic                    datard_done_strobe;     // Burst completed
output logic [31:0]             datard_beats_done;      // Beats actually moved
output logic                    datard_error;           // Error occurred
```

**AXI Master Interface:**
```systemverilog
// AXI AR (Address Read) Channel
output logic [ADDR_WIDTH-1:0]   m_axi_araddr;
output logic [7:0]              m_axi_arlen;      // Burst length - 1
output logic [2:0]              m_axi_arsize;     // Beat size
output logic [1:0]              m_axi_arburst;    // INCR
output logic [AXI_ID_WIDTH-1:0] m_axi_arid;       // Transaction ID
output logic                    m_axi_arvalid;
input  logic                    m_axi_arready;

// AXI R (Read Data) Channel
input  logic [AXI_ID_WIDTH-1:0] m_axi_rid;        // Transaction ID
input  logic [DATA_WIDTH-1:0]   m_axi_rdata;
input  logic [1:0]              m_axi_rresp;
input  logic                    m_axi_rlast;
input  logic                    m_axi_rvalid;
output logic                    m_axi_rready;
```

**Critical AXI ID Requirement:**

The lower bits of `m_axi_arid` **MUST** contain the channel ID from the arbiter:

```systemverilog
// Lower bits = channel ID (from arbiter grant)
// Upper bits = transaction counter (for multiple outstanding)
assign m_axi_arid = {transaction_counter, datard_channel_id[3:0]};
```

**Rationale:**
- Allows responses to be routed back to correct channel
- Enables MonBus packet generation with channel ID
- Critical for debugging and transaction tracking
- Channel ID comes from arbiter (whichever scheduler won arbitration)

**SRAM Write Interface:**
```systemverilog
output logic                    sram_wr_en;
output logic [ADDR_WIDTH-1:0]   sram_wr_addr;
output logic [DATA_WIDTH-1:0]   sram_wr_data;
input  logic [31:0]             sram_wr_space;    // Available space in beats
```

**MonBus Output:**
```systemverilog
output logic                    monbus_valid;
input  logic                    monbus_ready;
output logic [63:0]             monbus_packet;
```

---

## Operation

### Burst Decision Logic

**Critical:** Engine decides burst length autonomously, NOT from scheduler interface.

```systemverilog
// Determine burst length based on:
// 1. Performance mode configuration (MAX_BURST_LEN)
// 2. Runtime configuration (cfg_burst_len)
// 3. Remaining beats (datard_beats_remaining)
// 4. SRAM space available (sram_wr_space)

function automatic logic [7:0] calculate_burst_len();
    logic [31:0] max_possible;

    // Start with configured burst length
    max_possible = cfg_burst_len;

    // Limit to MAX_BURST_LEN (performance mode)
    if (max_possible > MAX_BURST_LEN)
        max_possible = MAX_BURST_LEN;

    // Limit to remaining beats
    if (max_possible > datard_beats_remaining)
        max_possible = datard_beats_remaining;

    // Limit to SRAM space
    if (max_possible > sram_wr_space)
        max_possible = sram_wr_space;

    return max_possible[7:0];
endfunction
```

### Transaction Flow

**Low Performance (Sequential):**
```
1. Wait for datard_valid && SRAM space available
2. Calculate burst length (limited by config, remaining, SRAM)
3. Issue AXI AR transaction
4. Wait for all R beats (rlast)
5. Assert datard_done_strobe with beats_done count
6. Repeat until datard_beats_remaining == 0
```

**Medium/High Performance (Pipelined):**
```
1. Accept datard_valid && track outstanding transactions
2. Issue multiple AXI AR transactions (up to MAX_OUTSTANDING)
3. Pipeline R data into SRAM
4. Assert datard_done_strobe for each completed burst
5. Dynamically adjust burst sizes based on SRAM space
```

### SRAM Write

**All Performance Modes:**
```systemverilog
// On AXI R data valid
always_ff @(posedge aclk) begin
    if (m_axi_rvalid && m_axi_rready) begin
        sram_wr_en <= 1'b1;
        sram_wr_data <= m_axi_rdata;
        sram_wr_addr <= r_sram_wr_ptr;
        r_sram_wr_ptr <= r_sram_wr_ptr + 1;
    end else begin
        sram_wr_en <= 1'b0;
    end
end
```

---

## Architecture by Performance Mode

**IMPORTANT:** This engine uses **STREAMING PIPELINE architecture**, NOT FSM!

See `puml/axi_read_engine_pipeline.puml` for detailed pipeline flow diagram.

### Low Performance Implementation (v1 - ACTUAL RTL)

**Flag-Based Control (NO state machine):**

```systemverilog
// Control flags (NOT FSM states!)
logic r_ar_inflight;     // Transaction in flight
logic r_ar_valid;        // AR channel has valid data
logic [7:0] r_beats_received;
logic [7:0] r_expected_beats;

// Ready signal - can accept new request when:
assign datard_ready = !r_ar_inflight && !r_ar_valid;

// Streaming pipeline operation:
// 1. Accept request → set r_ar_inflight
// 2. Issue AR → clear r_ar_valid when handshake
// 3. Stream R data → sram_wr_en = m_axi_rvalid && m_axi_rready
// 4. On rlast → clear r_ar_inflight, assert done_strobe
// 5. Immediately ready for next request (ZERO bubbles!)

// Actual implementation (axi_read_engine.sv:161-189):
if (datard_valid && datard_ready) begin
    r_ar_addr <= datard_addr;
    r_ar_len <= w_capped_burst_len;
    r_ar_channel_id <= datard_channel_id;
    r_ar_valid <= 1'b1;
    r_ar_inflight <= 1'b1;  // Mark transaction active
end

// AXI AR handshake
if (r_ar_valid && m_axi_arready) begin
    r_ar_valid <= 1'b0;
end

// Clear inflight when last beat received
if (m_axi_rvalid && m_axi_rready && m_axi_rlast) begin
    r_ar_inflight <= 1'b0;
end
```

**Streaming Data Path:**
- `assign m_axi_rready = sram_wr_ready;` (direct passthrough!)
- `assign sram_wr_en = m_axi_rvalid && m_axi_rready;` (no FSM overhead!)
- `assign sram_wr_data = m_axi_rdata;` (continuous streaming!)

**Performance Advantage:** Zero-bubble operation by eliminating state machine transitions.

### Medium Performance Implementation (Future)

- Outstanding transaction counter (track multiple AR/R pairs)
- Basic AR/R channel decoupling
- Adaptive burst sizing based on SRAM fullness
- Still NO FSM - uses enhanced flag-based control

### High Performance Implementation (Future)

- Full AR/R channel pipelining
- Transaction ID tracking (out-of-order completion)
- Dynamic burst optimization
- Prefetch lookahead
- Still NO FSM - uses credit-based streaming control

---

## Error Handling

### AXI Errors

```systemverilog
// On RRESP != OKAY
if (m_axi_rvalid && m_axi_rresp != 2'b00) begin
    datard_error <= 1'b1;
    // Generate MonBus error packet
end
```

### Timeout Detection

```systemverilog
// Timeout if no progress for cfg_timeout cycles
if (datard_valid && !transaction_progress) begin
    r_timeout_counter <= r_timeout_counter + 1;
    if (r_timeout_counter >= cfg_timeout) begin
        datard_error <= 1'b1;
    end
end
```

---

## Testing

**Test Location:** `projects/components/stream/dv/tests/fub_tests/axi_engines/`

**Test Scenarios (per performance mode):**
1. Single burst read
2. Multi-burst transfer (beats > MAX_BURST_LEN)
3. SRAM backpressure handling
4. Variable burst sizing
5. AXI error response
6. Timeout detection
7. Outstanding transaction limits (Medium/High)

---

## Performance Comparison

| Metric | Low | Medium | High |
|--------|-----|--------|------|
| **Area (LUTs)** | ~250 | ~400 | ~600 |
| **Max Throughput** | 50% | 75% | 95% |
| **Outstanding Txns** | 1 | 4 | 16 |
| **Burst Length** | 8 | 16 | 256 |
| **Pipelining** | None | Basic | Full |
| **Use Case** | Tutorial | Typical | High-perf |

---

## Related Documentation

- **Scheduler:** `02_scheduler.md` - Interface contract
- **Architecture:** `docs/ARCHITECTURAL_NOTES.md` - Separation of concerns
- **AXI4 Protocol:** ARM IHI0022E

---

**Last Updated:** 2025-10-17
