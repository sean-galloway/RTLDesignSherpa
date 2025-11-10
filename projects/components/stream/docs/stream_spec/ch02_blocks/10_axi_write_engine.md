# AXI Write Engine Specification

**Module:** `axi_write_engine.sv`
**Location:** `rtl/stream_fub/`
**Status:** To be created

---

## Overview

The AXI Write Engine autonomously executes AXI write transactions to store data to system memory. It accepts requests from the Scheduler, decides burst lengths internally based on configuration and SRAM data availability, and reports completion back.

### Key Features

- **Autonomous burst decision:** Engine decides burst length based on internal config
- **Performance modes:** Low, Medium, High (compile-time parameter)
- **SRAM interface:** Reads data from shared SRAM
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
parameter int    MAX_BURST_LEN = 16;      // Fixed 16-beat bursts
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
parameter int    MAX_BURST_LEN = 32;      // Up to 32-beat bursts
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
parameter int    AXI_ID_WIDTH = 8;         // AXI ID width
parameter int    MAX_BURST_LEN = 16;       // Max burst length (perf-dependent)
parameter int    MAX_OUTSTANDING = 1;      // Max outstanding transactions
parameter bit    ENABLE_PIPELINE = 0;      // Pipeline enable
parameter int    SRAM_DEPTH = 1024;        // SRAM depth (for data check)
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
input  logic                    datawr_valid;           // Scheduler requests write
output logic                    datawr_ready;           // Engine grants access
input  logic [ADDR_WIDTH-1:0]   datawr_addr;            // Start address
input  logic [31:0]             datawr_beats_remaining; // Total beats to write
input  logic [3:0]              datawr_channel_id;      // Channel ID

// Completion feedback
output logic                    datawr_done_strobe;     // Burst completed
output logic [31:0]             datawr_beats_done;      // Beats actually moved
output logic                    datawr_error;           // Error occurred
```

**AXI Master Interface:**
```systemverilog
// AXI AW (Address Write) Channel
output logic [ADDR_WIDTH-1:0]   m_axi_awaddr;
output logic [7:0]              m_axi_awlen;      // Burst length - 1
output logic [2:0]              m_axi_awsize;     // Beat size
output logic [1:0]              m_axi_awburst;    // INCR
output logic [AXI_ID_WIDTH-1:0] m_axi_awid;       // Transaction ID
output logic                    m_axi_awvalid;
input  logic                    m_axi_awready;

// AXI W (Write Data) Channel
output logic [DATA_WIDTH-1:0]   m_axi_wdata;
output logic [DATA_WIDTH/8-1:0] m_axi_wstrb;
output logic                    m_axi_wlast;
output logic                    m_axi_wvalid;
input  logic                    m_axi_wready;

// AXI B (Write Response) Channel
input  logic [AXI_ID_WIDTH-1:0] m_axi_bid;        // Transaction ID
input  logic [1:0]              m_axi_bresp;
input  logic                    m_axi_bvalid;
output logic                    m_axi_bready;
```

**Critical AXI ID Requirement:**

The lower bits of `m_axi_awid` **MUST** contain the channel ID from the arbiter:

```systemverilog
// Lower bits = channel ID (from arbiter grant)
// Upper bits = transaction counter (for multiple outstanding)
assign m_axi_awid = {transaction_counter, datawr_channel_id[3:0]};
```

**Rationale:**
- Allows responses to be routed back to correct channel
- Enables MonBus packet generation with channel ID
- Critical for debugging and transaction tracking
- Channel ID comes from arbiter (whichever scheduler won arbitration)

**SRAM Read Interface:**
```systemverilog
output logic                    sram_rd_en;
output logic [ADDR_WIDTH-1:0]   sram_rd_addr;
input  logic [DATA_WIDTH-1:0]   sram_rd_data;
input  logic [31:0]             sram_rd_avail;    // Available data in beats
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
// 3. Remaining beats (datawr_beats_remaining)
// 4. SRAM data available (sram_rd_avail)

function automatic logic [7:0] calculate_burst_len();
    logic [31:0] max_possible;

    // Start with configured burst length
    max_possible = cfg_burst_len;

    // Limit to MAX_BURST_LEN (performance mode)
    if (max_possible > MAX_BURST_LEN)
        max_possible = MAX_BURST_LEN;

    // Limit to remaining beats
    if (max_possible > datawr_beats_remaining)
        max_possible = datawr_beats_remaining;

    // Limit to SRAM data availability
    if (max_possible > sram_rd_avail)
        max_possible = sram_rd_avail;

    return max_possible[7:0];
endfunction
```

### Transaction Flow

**Low Performance (Sequential):**
```
1. Wait for datawr_valid && SRAM data available
2. Calculate burst length (limited by config, remaining, SRAM data)
3. Issue AXI AW transaction
4. Stream W data from SRAM (assert wlast on final beat)
5. Wait for B response
6. Assert datawr_done_strobe with beats_done count
7. Repeat until datawr_beats_remaining == 0
```

**Medium/High Performance (Pipelined):**
```
1. Accept datawr_valid && track outstanding transactions
2. Issue multiple AXI AW transactions (up to MAX_OUTSTANDING)
3. Pipeline W data from SRAM
4. Process B responses asynchronously
5. Assert datawr_done_strobe for each completed burst
6. Dynamically adjust burst sizes based on SRAM data availability
```

### SRAM Read

**All Performance Modes:**
```systemverilog
// Read data from SRAM for AXI W channel
always_ff @(posedge aclk) begin
    if (m_axi_wvalid && m_axi_wready) begin
        sram_rd_en <= 1'b1;
        sram_rd_addr <= r_sram_rd_ptr;
        r_sram_rd_ptr <= r_sram_rd_ptr + 1;
    end else begin
        sram_rd_en <= 1'b0;
    end
end

// Pipeline SRAM data to AXI W
always_ff @(posedge aclk) begin
    if (sram_rd_en) begin
        m_axi_wdata <= sram_rd_data;
        m_axi_wstrb <= {(DATA_WIDTH/8){1'b1}};  // Full strobes
    end
end
```

---

## Architecture by Performance Mode

**IMPORTANT:** This engine uses **STREAMING PIPELINE architecture**, NOT FSM!

See `puml/axi_write_engine_pipeline.puml` for detailed pipeline flow diagram.

### Low Performance Implementation (v1 - ACTUAL RTL)

**Flag-Based Control (NO state machine):**

```systemverilog
// Control flags (NOT FSM states!)
logic r_aw_inflight;     // Transaction in flight
logic r_aw_valid;        // AW channel has valid data
logic r_w_active;        // W channel streaming
logic r_b_pending;       // B response pending
logic [7:0] r_beats_sent;
logic [7:0] r_expected_beats;

// Ready signal - can accept new request when:
assign datawr_ready = !r_aw_inflight && !r_aw_valid && !r_b_pending;

// Streaming pipeline operation:
// 1. Accept request → set r_aw_inflight
// 2. Issue AW → clear r_aw_valid when handshake, activate W channel
// 3. Stream W data → m_axi_wvalid = r_w_active && sram_rd_valid
// 4. On wlast → set r_b_pending
// 5. On B response → clear all flags, assert done_strobe
// 6. Immediately ready for next request (ZERO bubbles!)

// Actual implementation (axi_write_engine.sv:171-200):
if (datawr_valid && datawr_ready) begin
    r_aw_addr <= datawr_addr;
    r_aw_len <= w_capped_burst_len;
    r_aw_channel_id <= datawr_channel_id;
    r_aw_valid <= 1'b1;
    r_aw_inflight <= 1'b1;  // Mark transaction active
end

// AXI AW handshake
if (r_aw_valid && m_axi_awready) begin
    r_aw_valid <= 1'b0;
    r_expected_beats <= r_aw_len + 8'h1;
    r_w_active <= 1'b1;     // Start W streaming
end

// Clear inflight when B response received
if (m_axi_bvalid && m_axi_bready) begin
    r_aw_inflight <= 1'b0;
    r_b_pending <= 1'b0;
end
```

**Streaming Data Path (axi_write_engine.sv:255-258):**
- `assign m_axi_wvalid = r_w_active && sram_rd_valid;` (direct gating!)
- `assign m_axi_wdata = sram_rd_data;` (passthrough!)
- `assign m_axi_wstrb = {(DATA_WIDTH/8){1'b1}};` (full strobes!)
- `assign m_axi_wlast = (r_beats_sent == (r_expected_beats - 8'h1));`

**Performance Advantage:** Zero-bubble operation with AW/W/B channel pipelining.

### Medium Performance Implementation (V2 - Command Pipelined)

**Architecture: Command Pipeline with In-Order Drain**

**Key Innovation:** Decouple AW command acceptance from W/B completion

**Command Queue:**
```systemverilog
// Queue entry structure
typedef struct packed {
    logic [3:0]              channel_id;
    logic [7:0]              burst_len;
    logic [SRAM_ADDR_WIDTH-1:0] sram_base_addr;     // Partition start
    logic [SRAM_ADDR_WIDTH-1:0] sram_current_addr;  // Current read position
    logic [ID_WIDTH-1:0]     awid;
    logic                    valid;
} cmd_queue_entry_t;

cmd_queue_entry_t cmd_queue [CMD_QUEUE_DEPTH];  // Typical depth: 4-8
```

**W Data Drain FSM:**
```systemverilog
typedef enum logic [1:0] {
    DRAIN_IDLE   = 2'b00,  // No pending commands
    DRAIN_ACTIVE = 2'b01,  // Actively draining W data
    DRAIN_WAIT   = 2'b10   // Waiting for SRAM data
} drain_state_t;

// Drain in FIFO order from command queue
// Use per-command sram_current_addr for SRAM reads
```

**B Response Scoreboard:**
```systemverilog
typedef struct packed {
    logic        outstanding;
    logic [7:0]  burst_len;
    logic        error;
    logic [1:0]  error_resp;
    logic        done;
} scoreboard_entry_t;

scoreboard_entry_t scoreboard [8];  // One per channel
```

**Performance Improvement:**
- **5-8x throughput** vs V1 (hides B response latency)
- Accept multiple AW commands before W drain starts
- B responses processed asynchronously
- Continuous streaming without blocking on B

**SRAM Pointer Management:**
- Each command queue entry stores independent `sram_current_addr`
- Enables multiple commands from same channel (no pointer collision)
- Foundation for V3 out-of-order drain

**Parameterization:**
```systemverilog
parameter bit ENABLE_CMD_PIPELINE = 1'b1;     // Enable V2 features
parameter int CMD_QUEUE_DEPTH = 4;            // 2-8 typical
parameter int MAX_OUTSTANDING = 4;            // Track inflight AWs
```

**Area Impact:** ~2x V1 (command queue + scoreboard + FSM)
**Timing Impact:** ~10-15% FMax reduction (acceptable trade-off)

### High Performance Implementation (V3 - Out-of-Order Drain)

**Architecture: Command Pipeline with Priority-Based Drain**

**Key Enhancement:** W drain can service commands out-of-order based on SRAM data availability

**OOO Command Selection:**
```systemverilog
// Select highest-priority ready command (not just FIFO head)
function automatic int select_ooo_cmd();
    for (int i = 0; i < CMD_QUEUE_DEPTH; i++) begin
        if (cmd_queue[i].valid &&
            sram_has_data(cmd_queue[i].channel_id, cmd_queue[i].burst_len) &&
            !cmd_queue[i].draining) begin
            return i;  // First ready command
        end
    end
    return -1;  // None ready
endfunction
```

**Additional V3 State:**
```systemverilog
typedef struct packed {
    // V2 fields...
    logic draining;  // Currently being drained (prevent re-selection)
} cmd_queue_entry_t;
```

**SRAM Data Availability Check:**
```systemverilog
// Query SRAM controller: Does channel X have Y beats ready?
function automatic logic sram_has_data(input [3:0] ch_id, input [7:0] needed);
    logic [12:0] ch_count;
    ch_count = sram_wr_count[ch_id];  // From SRAM controller
    return (ch_count >= needed);
endfunction
```

**Benefits:**
- **8-10x throughput** vs V1 (hide SRAM fill latency too)
- Skip stalled commands (SRAM empty)
- Service channels with ready data first
- True multi-channel parallelism

**Innate OOO Compatibility:**
- Per-channel SRAM partitioning (no cross-channel hazards)
- Per-command pointer tracking (no interference)
- Independent channel state (scheduler BFM already tracks)
- Minimal V3 changes needed (add draining flag + select function)

**Parameterization:**
```systemverilog
parameter bit ENABLE_CMD_PIPELINE = 1'b1;     // Enable V2 features
parameter bit ENABLE_OOO_DRAIN = 1'b1;        // Enable V3 OOO
parameter int CMD_QUEUE_DEPTH = 8;            // 8-16 for deep pipelining
parameter int MAX_OUTSTANDING = 16;           // Higher for OOO
```

**Area Impact:** ~3-4x V1 (V2 + priority logic + SRAM status tracking)
**Timing Impact:** ~15-20% FMax reduction (still net positive throughput)

---

## Asymmetric Burst Lengths

**Note:** Write engine can use different burst lengths than read engine.

**Example Configuration:**
```systemverilog
// Read engine: 8 beats per burst
axi_read_engine #(.MAX_BURST_LEN(8)) u_rd_engine (...);

// Write engine: 16 beats per burst (2x read)
axi_write_engine #(.MAX_BURST_LEN(16)) u_wr_engine (...);
```

**Why This Works:**
- SRAM buffer decouples read and write rates
- Scheduler doesn't care about burst sizing differences
- Each engine optimizes independently

---

## Error Handling

### AXI Errors

```systemverilog
// On BRESP != OKAY
if (m_axi_bvalid && m_axi_bresp != 2'b00) begin
    datawr_error <= 1'b1;
    // Generate MonBus error packet
end
```

### Timeout Detection

```systemverilog
// Timeout if no progress for cfg_timeout cycles
if (datawr_valid && !transaction_progress) begin
    r_timeout_counter <= r_timeout_counter + 1;
    if (r_timeout_counter >= cfg_timeout) begin
        datawr_error <= 1'b1;
    end
end
```

---

## Testing

**Test Location:** `projects/components/stream/dv/tests/fub_tests/axi_engines/`

**Test Scenarios (per performance mode):**
1. Single burst write
2. Multi-burst transfer (beats > MAX_BURST_LEN)
3. SRAM data availability backpressure
4. Variable burst sizing
5. AXI error response
6. Timeout detection
7. Outstanding transaction limits (Medium/High)
8. Asymmetric burst lengths with read engine

---

## Performance Comparison

| Metric | Low (V1) | Medium (V2) | High (V3) |
|--------|----------|-------------|-----------|
| **Architecture** | Single-burst | Command Pipeline | OOO Drain |
| **Area (LUTs)** | ~1,250 | ~2,500 | ~4,000 |
| **Max Throughput** | 0.14 beats/cycle | 0.94 beats/cycle | 0.98 beats/cycle |
| **Throughput vs V1** | 1.0x | 6.7x | 7.0x |
| **Outstanding Txns** | 1 | 4-8 | 8-16 |
| **Command Queue** | None | 4-8 deep | 8-16 deep |
| **Burst Length** | 16 | 16-32 | 16-256 |
| **Pipelining** | AW→W→B serial | AW/W/B decoupled | Full OOO |
| **B Response Handling** | Blocking | Async scoreboard | Async scoreboard |
| **SRAM Pointer Mgmt** | Single global | Per-command | Per-command |
| **Use Case** | Tutorial/embedded | Balanced FPGA | Datacenter/ASIC |
| **Typical Memory** | SRAM | DDR3/DDR4 | DDR4/HBM |

**Performance Scaling with Memory Latency:**

| Memory Type | B Response | V1 Throughput | V2 Throughput | Improvement |
|-------------|-----------|---------------|---------------|-------------|
| Embedded SRAM | 5-10 cycles | 0.43 beats/cycle | 0.85 beats/cycle | 2.0x |
| DDR3 SDRAM | 40-60 cycles | 0.18 beats/cycle | 0.92 beats/cycle | 5.1x |
| DDR4 SDRAM | 60-100 cycles | 0.14 beats/cycle | 0.94 beats/cycle | 6.7x |
| PCIe Gen3 | 30-50 cycles | 0.22 beats/cycle | 0.90 beats/cycle | 4.1x |

**Key Observation:** V2/V3 benefit scales with memory latency - the higher the latency, the greater the improvement.

---

## Related Documentation

- **Scheduler:** `02_scheduler.md` - Interface contract
- **Read Engine:** `03_axi_read_engine.md` - Companion read engine
- **Architecture:** `docs/ARCHITECTURAL_NOTES.md` - Separation of concerns
- **AXI4 Protocol:** ARM IHI0022E

---

**Last Updated:** 2025-10-17
