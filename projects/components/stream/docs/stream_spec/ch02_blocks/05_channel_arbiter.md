# Channel Arbiter Specification

**Module:** `channel_arbiter.sv`
**Location:** `rtl/stream_macro/`
**Status:** To be created

---

## Overview

The Channel Arbiter manages access to shared resources (descriptor fetch, data read, data write AXI masters) across 8 independent STREAM channels. It implements priority-based arbitration with round-robin fairness within the same priority level.

### Key Features

- **8 channels:** Fixed maximum (configurable via parameter)
- **Priority-based:** Uses descriptor priority field (8-bit)
- **Round-robin:** Within same priority level
- **Timeout protection:** Prevents starvation
- **Separate arbiters:** Independent for descriptor, read, write paths

---

## Arbitration Scheme

### Priority Levels

**Descriptor priority field:** 8-bit value from descriptor
- **Higher value = higher priority**
- **Range:** 0 (lowest) to 255 (highest)

### Round-Robin Within Priority

```
Channels with same priority rotate fairly:
  Priority 7: CH0 -> CH3 -> CH0 -> CH3 -> ...
  Priority 5: CH1 -> CH2 -> CH1 -> CH2 -> ...

Between priorities: Higher always wins
  Priority 7 CH0 > Priority 5 CH1
```

### Timeout/Starvation Prevention

```systemverilog
// If a channel waits too long, boost priority temporarily
if (r_wait_cycles[ch_id] > cfg_timeout_threshold) begin
    effective_priority = MAX_PRIORITY;
end
```

---

## Interface

### Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;          // Fixed at 8 for STREAM
parameter int PRIORITY_WIDTH = 8;        // Priority field width
```

### Ports

**Clock and Reset:**
```systemverilog
input  logic                        aclk;
input  logic                        aresetn;
```

**Configuration:**
```systemverilog
input  logic [31:0]                 cfg_timeout_threshold;
```

**Channel Requests (Descriptor Path):**
```systemverilog
input  logic [NUM_CHANNELS-1:0]     desc_req;           // Request signals
input  logic [NUM_CHANNELS-1:0][PRIORITY_WIDTH-1:0]
                                    desc_priority;      // Priority per channel
output logic [NUM_CHANNELS-1:0]     desc_grant;         // Grant signals
output logic [$clog2(NUM_CHANNELS)-1:0]
                                    desc_grant_id;      // Granted channel ID
output logic                        desc_grant_valid;   // Grant valid
```

**Channel Requests (Data Read Path):**
```systemverilog
input  logic [NUM_CHANNELS-1:0]     datard_req;
input  logic [NUM_CHANNELS-1:0][PRIORITY_WIDTH-1:0]
                                    datard_priority;
output logic [NUM_CHANNELS-1:0]     datard_grant;
output logic [$clog2(NUM_CHANNELS)-1:0]
                                    datard_grant_id;
output logic                        datard_grant_valid;
```

**Channel Requests (Data Write Path):**
```systemverilog
input  logic [NUM_CHANNELS-1:0]     datawr_req;
input  logic [NUM_CHANNELS-1:0][PRIORITY_WIDTH-1:0]
                                    datawr_priority;
output logic [NUM_CHANNELS-1:0]     datawr_grant;
output logic [$clog2(NUM_CHANNELS)-1:0]
                                    datawr_grant_id;
output logic                        datawr_grant_valid;
```

---

## Arbitration Algorithm

### Priority Encoder with Round-Robin

```systemverilog
function automatic logic [$clog2(NUM_CHANNELS)-1:0]
    arbitrate(
        logic [NUM_CHANNELS-1:0] requests,
        logic [NUM_CHANNELS-1:0][PRIORITY_WIDTH-1:0] priorities,
        logic [$clog2(NUM_CHANNELS)-1:0] last_grant
    );

    logic [PRIORITY_WIDTH-1:0] max_priority;
    logic [NUM_CHANNELS-1:0] max_priority_mask;
    logic [$clog2(NUM_CHANNELS)-1:0] grant_id;

    // Find maximum priority among requesters
    max_priority = 0;
    for (int i = 0; i < NUM_CHANNELS; i++) begin
        if (requests[i] && priorities[i] > max_priority) begin
            max_priority = priorities[i];
        end
    end

    // Mask channels with max priority
    for (int i = 0; i < NUM_CHANNELS; i++) begin
        max_priority_mask[i] = requests[i] && (priorities[i] == max_priority);
    end

    // Round-robin among max priority channels
    grant_id = round_robin_select(max_priority_mask, last_grant);

    return grant_id;
endfunction
```

### Round-Robin Selection

```systemverilog
function automatic logic [$clog2(NUM_CHANNELS)-1:0]
    round_robin_select(
        logic [NUM_CHANNELS-1:0] candidates,
        logic [$clog2(NUM_CHANNELS)-1:0] last_grant
    );

    // Start searching from last_grant + 1
    for (int offset = 1; offset <= NUM_CHANNELS; offset++) begin
        int idx = (last_grant + offset) % NUM_CHANNELS;
        if (candidates[idx]) begin
            return idx;
        end
    end

    // Fallback (shouldn't reach here if candidates != 0)
    return 0;
endfunction
```

---

## Operation

### Grant Cycle

```
1. All channels assert request signals with priority
2. Arbiter determines winner based on:
   a. Highest priority wins
   b. Among same priority: round-robin from last grant
3. Arbiter asserts grant for one cycle
4. Winning channel captures grant and proceeds
5. Arbiter ready for next arbitration
```

### Timeout Boost

```systemverilog
// Track wait time per channel
always_ff @(posedge aclk) begin
    for (int i = 0; i < NUM_CHANNELS; i++) begin
        if (desc_req[i] && !desc_grant[i]) begin
            r_desc_wait_cycles[i] <= r_desc_wait_cycles[i] + 1;
        end else begin
            r_desc_wait_cycles[i] <= 0;
        end
    end
end

// Boost priority if timeout
logic [NUM_CHANNELS-1:0][PRIORITY_WIDTH-1:0] effective_priority;
always_comb begin
    for (int i = 0; i < NUM_CHANNELS; i++) begin
        if (r_desc_wait_cycles[i] > cfg_timeout_threshold) begin
            effective_priority[i] = {PRIORITY_WIDTH{1'b1}};  // Max priority
        end else begin
            effective_priority[i] = desc_priority[i];
        end
    end
end
```

---

## Example Scenarios

### Scenario 1: Simple Priority

```
Requests:
  CH0: priority=7, waiting
  CH1: priority=5, waiting
  CH2: priority=5, waiting

Result: CH0 granted (highest priority)
```

### Scenario 2: Round-Robin

```
Requests (all priority=5):
  CH1: waiting
  CH2: waiting
  CH4: waiting

Last grant: CH4
Result: CH1 granted (round-robin from CH4+1)
```

### Scenario 3: Timeout Boost

```
Initial:
  CH0: priority=7, just requested
  CH3: priority=3, waiting 1000 cycles (> timeout)

Timeout boost: CH3 effective priority = 255
Result: CH3 granted (timeout boost to max priority)
```

---

## Integration Pattern

### Connecting to Schedulers

```systemverilog
// Instantiate arbiter
channel_arbiter #(
    .NUM_CHANNELS(8)
) u_arbiter (
    .aclk(aclk),
    .aresetn(aresetn),

    // Descriptor path
    .desc_req({ch7_desc_req, ch6_desc_req, ..., ch0_desc_req}),
    .desc_priority({ch7_priority, ch6_priority, ..., ch0_priority}),
    .desc_grant({ch7_desc_grant, ch6_desc_grant, ..., ch0_desc_grant}),

    // Data read path
    .datard_req({ch7_datard_valid, ..., ch0_datard_valid}),
    .datard_priority({ch7_priority, ..., ch0_priority}),
    .datard_grant({ch7_datard_ready, ..., ch0_datard_ready}),

    // Data write path
    .datawr_req({ch7_datawr_valid, ..., ch0_datawr_valid}),
    .datawr_priority({ch7_priority, ..., ch0_priority}),
    .datawr_grant({ch7_datawr_ready, ..., ch0_datawr_ready})
);
```

### Multiplexing Granted Channel

```systemverilog
// Descriptor fetch address mux
always_comb begin
    case (desc_grant_id)
        3'd0: desc_fetch_addr = ch0_desc_addr;
        3'd1: desc_fetch_addr = ch1_desc_addr;
        // ...
        3'd7: desc_fetch_addr = ch7_desc_addr;
    endcase
end
```

---

## Testing

**Test Location:** `projects/components/stream/dv/tests/integration_tests/`

**Test Scenarios:**
1. Single channel (no arbitration needed)
2. Two channels, different priorities
3. Multiple channels, same priority (verify round-robin)
4. Timeout boost triggering
5. All 8 channels active simultaneously
6. Priority changes during operation

---

## Performance

**Arbitration Latency:** 1 cycle (registered output)

**Area Estimate:** ~150 LUTs per arbiter   3 arbiters = ~450 LUTs

---

## Related Documentation

- **Scheduler:** `02_scheduler.md` - Requesters
- **Top-Level:** `09_stream_top.md` - Integration

---

**Last Updated:** 2025-10-17
