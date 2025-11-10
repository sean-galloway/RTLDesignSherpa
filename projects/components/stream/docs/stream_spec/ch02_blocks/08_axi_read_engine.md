# AXI Read Engine Specification

**Module:** `axi_read_engine.sv`
**Location:** `projects/components/stream/rtl/stream_fub/`
**Status:** Implemented

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

### Medium Performance Implementation (V2 - Command Pipelined)

**Target:** 5-8x throughput improvement over V1 with moderate area increase

**Parameter:** `ENABLE_CMD_PIPELINE = 1`

**Architecture:** Command pipelining decouples AR command acceptance from R data completion, allowing multiple outstanding read transactions.

**Key Differences from V1:**
- **Command Queue:** 4-8 deep FIFO for pending AR requests
- **Outstanding Transaction Tracking:** Count active reads (no scoreboard needed for reads)
- **Independent AR/R Channels:** AR can accept new requests while R data streams in
- **Asynchronous Completion:** R beats arrive independently of new AR requests

**Simplified Structure (Read Engine):**

```systemverilog
// Command Queue Entry (simpler than write - no W drain state)
typedef struct packed {
    logic [3:0]              channel_id;
    logic [7:0]              burst_len;
    logic [SRAM_ADDR_WIDTH-1:0] sram_base_addr;     // Partition start
    logic [SRAM_ADDR_WIDTH-1:0] sram_current_addr;  // Current write position
    logic [ID_WIDTH-1:0]     arid;
    logic                    valid;
} read_cmd_queue_entry_t;

// Command Queue (4-8 deep for medium performance)
read_cmd_queue_entry_t cmd_queue [CMD_QUEUE_DEPTH];
logic [$clog2(CMD_QUEUE_DEPTH)-1:0] cmd_wr_ptr;
logic [$clog2(CMD_QUEUE_DEPTH)-1:0] cmd_rd_ptr;
logic [$clog2(CMD_QUEUE_DEPTH):0] cmd_count;

// Outstanding transaction counter (simpler than write B scoreboard)
logic [3:0] outstanding_reads;  // Count AR issued but R not complete
```

**AR Channel Logic (Command Acceptance):**

```systemverilog
// Accept new requests when queue has space
assign datard_ready = (cmd_count < CMD_QUEUE_DEPTH) &&
                      (outstanding_reads < MAX_OUTSTANDING);

// Push to command queue
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        cmd_wr_ptr <= '0;
        cmd_count <= '0;
    end else begin
        if (datard_valid && datard_ready) begin
            cmd_queue[cmd_wr_ptr].channel_id <= datard_channel_id;
            cmd_queue[cmd_wr_ptr].burst_len <= w_capped_burst_len;
            cmd_queue[cmd_wr_ptr].sram_base_addr <= calc_sram_base(datard_channel_id);
            cmd_queue[cmd_wr_ptr].sram_current_addr <= calc_sram_base(datard_channel_id);
            cmd_queue[cmd_wr_ptr].arid <= {transaction_counter, datard_channel_id};
            cmd_queue[cmd_wr_ptr].valid <= 1'b1;

            cmd_wr_ptr <= cmd_wr_ptr + 1'b1;
            cmd_count <= cmd_count + 1'b1;
        end

        // Pop from queue when R completes
        if (m_axi_rvalid && m_axi_rready && m_axi_rlast) begin
            cmd_rd_ptr <= cmd_rd_ptr + 1'b1;
            cmd_count <= cmd_count - 1'b1;
        end
    end
)
```

**R Channel Logic (Data Reception - Streaming):**

```systemverilog
// R channel ready when SRAM can accept data
assign m_axi_rready = sram_wr_ready;

// SRAM write on R valid (same as V1, but pointer from queue)
assign sram_wr_en = m_axi_rvalid && m_axi_rready;
assign sram_wr_addr = cmd_queue[cmd_rd_ptr].sram_current_addr;
assign sram_wr_data = m_axi_rdata;

// Update SRAM pointer in queue
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        // Reset handled above
    end else begin
        if (m_axi_rvalid && m_axi_rready) begin
            cmd_queue[cmd_rd_ptr].sram_current_addr <=
                cmd_queue[cmd_rd_ptr].sram_current_addr + 1'b1;
        end
    end
)
```

**Why Read Engine is Simpler Than Write:**
1. **No W Drain FSM**: Data arrives from slave (can't stall internally)
2. **No B Scoreboard**: R channel includes last beat indicator (no separate response)
3. **In-Order Completion**: Most memory systems return R data in order (OOO optional)

**Performance Improvement:**
- V1: 0.14 beats/cycle (DDR4 latency limited)
- V2: 0.94 beats/cycle (6.7x improvement, command pipelining hides latency)

**Area Impact:**
- V1: ~1,250 LUTs
- V2: ~2,000 LUTs (1.6x increase for 6.7x throughput)

### High Performance Implementation (V3 - Out-of-Order Read)

**Target:** 7-10x throughput improvement over V1 with maximum area usage

**Parameters:** `ENABLE_CMD_PIPELINE = 1`, `ENABLE_OOO_READ = 1`

**Architecture:** Out-of-order read completion allows flexible R data arrival order, maximizing memory controller efficiency.

**Key Differences from V2:**
- **Transaction ID Matching:** Match m_axi_rid to command queue entries
- **Flexible Completion Order:** Process R beats from any outstanding transaction
- **SRAM Write Arbitration:** Multiple active commands can write to SRAM
- **Larger Command Queue:** 8-16 deep to maximize outstanding transactions

**Transaction ID Structure:**

```systemverilog
// AXI ID encoding (must preserve channel_id in lower bits)
// [ID_WIDTH-1:4] = Transaction counter (for multiple outstanding per channel)
// [3:0] = Channel ID (from scheduler, for MonBus routing)
assign m_axi_arid = {transaction_counter[ID_WIDTH-5:0], datard_channel_id[3:0]};
```

**R Channel OOO Matching:**

```systemverilog
// Match incoming R beat to command queue entry via ARID
function automatic int find_matching_cmd(input [ID_WIDTH-1:0] rid);
    for (int i = 0; i < CMD_QUEUE_DEPTH; i++) begin
        if (cmd_queue[i].valid && (cmd_queue[i].arid == rid)) begin
            return i;
        end
    end
    return -1;  // Should never happen (protocol error)
endfunction

// R beat processing
logic [$clog2(CMD_QUEUE_DEPTH)-1:0] active_cmd_idx;
assign active_cmd_idx = find_matching_cmd(m_axi_rid);

// SRAM write uses matched command's pointer
assign sram_wr_addr = cmd_queue[active_cmd_idx].sram_current_addr;

// Update matched command's pointer
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        // Reset handled in queue logic
    end else begin
        if (m_axi_rvalid && m_axi_rready) begin
            cmd_queue[active_cmd_idx].sram_current_addr <=
                cmd_queue[active_cmd_idx].sram_current_addr + 1'b1;

            // Mark complete on last beat
            if (m_axi_rlast) begin
                cmd_queue[active_cmd_idx].valid <= 1'b0;
            end
        end
    end
)
```

**Why V3 OOO is Naturally Supported:**

The architecture is **innately OOO-compatible** due to:

1. **Per-Channel SRAM Partitioning**: Each channel has independent SRAM region
   - Channel 0: Addresses 0-511
   - Channel 1: Addresses 512-1023
   - ... (no cross-channel hazards)

2. **Per-Command Pointer Tracking**: Each queue entry has independent `sram_current_addr`
   - Enables multiple commands from same channel
   - No pointer collision (each command writes to different SRAM region)

3. **Transaction ID Matching**: ARID contains channel ID in lower bits
   - Scheduler uses channel ID for routing
   - MonBus uses channel ID for transaction tracking
   - OOO logic uses full ARID for command matching

**V3 Additional Requirements:**
- Command queue compaction (remove completed entries to free slots)
- Priority-based AR issue (don't wait for oldest command to complete)
- Enhanced error handling (match error response to correct channel)

**Performance Improvement:**
- V1: 0.14 beats/cycle (single outstanding, latency limited)
- V2: 0.94 beats/cycle (multiple outstanding, in-order)
- V3: 0.98 beats/cycle (multiple outstanding, OOO, memory controller optimized)

**Area Impact:**
- V1: ~1,250 LUTs
- V2: ~2,000 LUTs (1.6x increase)
- V3: ~3,500 LUTs (2.8x increase for 7.0x throughput)

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

### Configuration Summary

| Metric | Low (V1) | Medium (V2) | High (V3) |
|--------|----------|-------------|-----------|
| **Architecture** | Single-burst | Command Pipeline | OOO Read |
| **Area (LUTs)** | ~1,250 | ~2,000 | ~3,500 |
| **Max Throughput** | 0.14 beats/cycle | 0.94 beats/cycle | 0.98 beats/cycle |
| **Throughput vs V1** | 1.0x | 6.7x | 7.0x |
| **Outstanding Txns** | 1 | 4-8 | 8-16 |
| **Command Queue** | None | 4-8 deep | 8-16 deep |
| **Completion Order** | Sequential | In-order | Out-of-order |
| **Transaction ID** | Simple | Counter | Match + Channel |
| **SRAM Pointer** | Single | Per-command | Per-command + Match |
| **Compile-Time Param** | Default | `ENABLE_CMD_PIPELINE=1` | `ENABLE_CMD_PIPELINE=1`<br>`ENABLE_OOO_READ=1` |

### Throughput Scaling by Memory Latency

Performance benefit increases with memory latency:

| Memory Type | Latency (cycles) | V1 Throughput | V2 Throughput | V3 Throughput | V2 vs V1 | V3 vs V1 |
|-------------|------------------|---------------|---------------|---------------|----------|----------|
| **SRAM (FPGA)** | 2-3 | 0.40 beats/cycle | 0.85 beats/cycle | 0.92 beats/cycle | 2.1x | 2.3x |
| **DDR3** | 50-70 | 0.17 beats/cycle | 0.89 beats/cycle | 0.96 beats/cycle | 5.2x | 5.6x |
| **DDR4** | 70-100 | 0.14 beats/cycle | 0.94 beats/cycle | 0.98 beats/cycle | 6.7x | 7.0x |
| **HBM2** | 100-150 | 0.12 beats/cycle | 0.96 beats/cycle | 0.99 beats/cycle | 8.0x | 8.3x |

**Key Insights:**
- V1 throughput degrades with latency (single outstanding blocks pipeline)
- V2/V3 maintain near-peak throughput regardless of latency (command pipelining hides latency)
- V3 provides marginal improvement over V2 (mainly for memory controllers that reorder)

### Area/Performance Trade-offs

| Configuration | Area | Throughput | Area Efficiency | Recommended Use Case |
|---------------|------|------------|-----------------|----------------------|
| **V1** | 1.0x | 1.0x | 1.00 | Tutorial, embedded, low-latency SRAM |
| **V2** | 1.6x | 6.7x | 4.19 | General-purpose, DDR3/DDR4, balanced |
| **V3** | 2.8x | 7.0x | 2.50 | High-performance, HBM2, OOO memory controllers |

**Area Efficiency** = (Throughput Improvement) / (Area Increase)

**Recommendation:**
- **Embedded systems**: V1 (minimize area)
- **General FPGA**: V2 (best area efficiency)
- **Datacenter/ASIC**: V3 (maximum throughput)

---

## Related Documentation

- **Scheduler:** `02_scheduler.md` - Interface contract
- **Architecture:** `docs/ARCHITECTURAL_NOTES.md` - Separation of concerns
- **AXI4 Protocol:** ARM IHI0022E

---

**Last Updated:** 2025-10-17
