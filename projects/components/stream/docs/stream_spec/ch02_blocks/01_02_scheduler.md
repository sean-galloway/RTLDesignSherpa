# Scheduler Specification

**Module:** `scheduler.sv`
**Location:** `rtl/stream_fub/`
**Based On:** RAPIDS scheduler (simplified)

---

## Overview

The Scheduler coordinates descriptor-to-data-transfer flow for a single STREAM channel. It tracks total beats remaining and requests access to data engines via simplified interfaces.

### Key Simplifications from RAPIDS

- [No] No credit management (removed exponential encoding)
- [No] No control read/write engines (direct APB only)
- [No] No network interfaces (pure memory-to-memory)
- [Done] Simpler FSM (6 states vs RAPIDS 12+ states)
- [Done] Aligned addresses only (no fixup logic)
- [Done] Length in beats (not chunks)

### Critical Architecture

**[WARNING] RIGID SEPARATION OF CONCERNS:**

- **Scheduler (Coordinator):** Tracks total work, requests access to engines
- **Engines (Autonomous Workers):** Decide burst lengths, execute transactions, report completion

**Interface Contract:**
- Scheduler provides: `beats_remaining` (total work)
- Engines report back: `beats_done` (work completed)
- Scheduler does **NOT** specify burst lengths

---

## Interface

### Parameters

```systemverilog
parameter int CHANNEL_ID = 0;         // Channel ID (0-7)
parameter int ADDR_WIDTH = 64;        // Address bus width
parameter int DATA_WIDTH = 512;       // Data bus width
```

### Ports

**Clock and Reset:**
```systemverilog
input  logic                    aclk;
input  logic                    aresetn;
```

**Configuration:**
```systemverilog
input  logic                    cfg_enable;        // Channel enable
input  logic [31:0]             cfg_timeout;       // Timeout threshold
```

**Descriptor Input (from Descriptor Engine):**
```systemverilog
input  logic                    desc_valid;
output logic                    desc_ready;
input  descriptor_t             desc_packet;
```

**Descriptor Request (to Descriptor Engine):**
```systemverilog
output logic                    desc_req_valid;
input  logic                    desc_req_ready;
output logic [ADDR_WIDTH-1:0]   desc_req_addr;
```

**Data Read Interface (to AXI Read Engine via Arbiter):**
```systemverilog
output logic                    datard_valid;           // Request read access
input  logic                    datard_ready;           // Engine grants access
output logic [63:0]             datard_addr;            // Source address
output logic [31:0]             datard_beats_remaining; // Total beats to read
output logic [3:0]              datard_channel_id;      // Channel ID

// Completion feedback
input  logic                    datard_done_strobe;     // Read completed
input  logic [31:0]             datard_beats_done;      // Beats actually moved
input  logic                    datard_error;           // Read error
```

**Data Write Interface (to AXI Write Engine via Arbiter):**
```systemverilog
output logic                    datawr_valid;           // Request write access
input  logic                    datawr_ready;           // Engine grants access
output logic [63:0]             datawr_addr;            // Destination address
output logic [31:0]             datawr_beats_remaining; // Total beats to write
output logic [3:0]              datawr_channel_id;      // Channel ID

// Completion feedback
input  logic                    datawr_done_strobe;     // Write completed
input  logic [31:0]             datawr_beats_done;      // Beats actually moved
input  logic                    datawr_error;           // Write error
```

**Status Outputs:**
```systemverilog
output logic                    ch_idle;               // Channel idle
output logic                    ch_error;              // Channel error
output logic [31:0]             ch_bytes_xfered;       // Bytes transferred
```

**MonBus Output:**
```systemverilog
output logic                    monbus_valid;
input  logic                    monbus_ready;
output logic [63:0]             monbus_packet;
```

---

## State Machine

### States

```systemverilog
typedef enum logic [3:0] {
    CH_IDLE         = 4'h0,  // Waiting for descriptor
    CH_FETCH_DESC   = 4'h1,  // Fetching next descriptor
    CH_READ_DATA    = 4'h2,  // Reading source data
    CH_WRITE_DATA   = 4'h3,  // Writing destination data
    CH_COMPLETE     = 4'h4,  // Transfer complete
    CH_NEXT_DESC    = 4'h5,  // Check for chained descriptor
    CH_ERROR        = 4'hF   // Error state
} channel_state_t;
```

### State Transitions

```
IDLE -> FETCH_DESC:  cfg_enable && initial descriptor request
FETCH_DESC -> READ_DATA:  Descriptor received, valid
READ_DATA -> WRITE_DATA:  All reads complete (read_beats_remaining == 0)
WRITE_DATA -> COMPLETE:  All writes complete (write_beats_remaining == 0)
COMPLETE -> NEXT_DESC:  Check next_descriptor_ptr
NEXT_DESC -> FETCH_DESC:  next_descriptor_ptr != 0 (chain)
NEXT_DESC -> IDLE:  next_descriptor_ptr == 0 || last flag set
ANY -> ERROR:  Timeout or engine error
ERROR -> IDLE:  Software reset
```

---

## Operation

### Transfer Flow

1. **IDLE:** Wait for `cfg_enable` and initial descriptor
2. **FETCH_DESC:** Request descriptor via `desc_req_valid`
3. **READ_DATA:**
   - Assert `datard_valid` with `datard_beats_remaining` = descriptor.length
   - Wait for `datard_ready` (arbiter grants access)
   - Monitor `datard_done_strobe` and decrement `read_beats_remaining` by `datard_beats_done`
   - Continue until `read_beats_remaining == 0`
4. **WRITE_DATA:**
   - Assert `datawr_valid` with `datawr_beats_remaining` = descriptor.length
   - Wait for `datawr_ready` (arbiter grants access)
   - Monitor `datawr_done_strobe` and decrement `write_beats_remaining` by `datawr_beats_done`
   - Continue until `write_beats_remaining == 0`
5. **COMPLETE:** Generate MonBus completion packet
6. **NEXT_DESC:** Check `next_descriptor_ptr`:
   - If != 0: Loop to FETCH_DESC with new address
   - If == 0 or `last` flag: Return to IDLE

### Beat Tracking

**Critical:** Scheduler tracks **total beats remaining**, NOT burst sizes.

```systemverilog
// On descriptor receive
r_read_beats_remaining <= descriptor.length;
r_write_beats_remaining <= descriptor.length;

// On read completion strobe
if (datard_done_strobe) begin
    r_read_beats_remaining <= r_read_beats_remaining - datard_beats_done;
end

// On write completion strobe
if (datawr_done_strobe) begin
    r_write_beats_remaining <= r_write_beats_remaining - datawr_beats_done;
end
```

**Engines decide burst size internally!** Scheduler just tracks total progress.

---

## Key Differences from RAPIDS

| Feature | RAPIDS | STREAM |
|---------|--------|--------|
| **Credit Management** | Exponential encoding | None (removed) |
| **Control Engines** | ctrlrd, ctrlwr | None (direct APB) |
| **Address Fixup** | Complex alignment | Aligned only |
| **Length Units** | Chunks (4 bytes) | Beats (DATA_WIDTH) |
| **Network** | Network master/slave | None |
| **States** | 12+ states | 6 states |
| **Burst Config** | Via interface signals | Engine-internal only |

---

## Error Handling

### Timeout Detection

```systemverilog
// Increment timeout counter when waiting for engine
if ((r_current_state == CH_READ_DATA && !datard_ready) ||
    (r_current_state == CH_WRITE_DATA && !datawr_ready)) begin
    r_timeout_counter <= r_timeout_counter + 1;
    if (r_timeout_counter >= cfg_timeout) begin
        w_next_state = CH_ERROR;
    end
end
```

### Engine Errors

```systemverilog
// Transition to error on engine error
if (datard_error || datawr_error) begin
    w_next_state = CH_ERROR;
end
```

### MonBus Error Reporting

All errors generate MonBus packets with error codes.

---

## Testing

**Test Location:** `projects/components/stream/dv/tests/fub_tests/scheduler/`

**Test Scenarios:**
1. Single descriptor transfer (read -> write)
2. Chained descriptors (2-3 deep)
3. Engine backpressure handling
4. Timeout detection
5. Engine error propagation
6. Beat counter accuracy (variable burst sizes from engines)

---

## Related Documentation

- **RAPIDS Scheduler:** `projects/components/rapids/docs/rapids_spec/ch02_blocks/01_01_scheduler.md`
- **Architecture:** `docs/ARCHITECTURAL_NOTES.md` - Separation of concerns
- **Source:** `rtl/stream_fub/scheduler.sv`

---

**Last Updated:** 2025-10-17
