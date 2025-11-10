# APB-to-Descriptor Router (apbtodescr)

## Overview

The `apbtodescr` module is a lightweight address-decode router that connects the APB configuration slave to the descriptor engines' APB kick-off ports. It translates APB register writes into descriptor engine start commands.

**Key Characteristics:**
- **No internal registers** - Pure combinational decode + FSM control
- **Parameterized base address** - Flexible placement in address space
- **Back-pressure handling** - Delays APB response if descriptor engine busy
- **8-channel routing** - One register per channel (0x00 through 0x1C)

## Block Diagram

```
Software APB Write          apbtodescr Router               Descriptor Engines
┌────────────────┐         ┌──────────────────┐           ┌──────────────────┐
│                │         │                  │           │                  │
│  Write         │  CMD    │  Address Decode  │           │  desc_apb_valid  │
│  0x1000_0000   │────────▶│  relative_addr   │──────────▶│  desc_apb_ready  │
│  to BASE+0x00  │         │  [4:2] = ch_id   │           │  desc_apb_addr   │
│                │         │                  │           │                  │
│                │  RSP    │  FSM:            │           │  CH0: 0x1000_0000│
│  (blocks until │◀────────│  IDLE→ROUTE→     │           │  CH1: <ready>    │
│   ready)       │         │  RESPOND         │           │  ...             │
│                │         │                  │           │  CH7: <ready>    │
└────────────────┘         └──────────────────┘           └──────────────────┘
```

## Address Map

Relative to `BASE_ADDR` parameter (default: 0x0000_0000):

| Offset | Register     | Channel | Description                           |
|--------|--------------|---------|---------------------------------------|
| 0x00   | CH0_CTRL     | 0       | Channel 0 descriptor address kick-off |
| 0x04   | CH1_CTRL     | 1       | Channel 1 descriptor address kick-off |
| 0x08   | CH2_CTRL     | 2       | Channel 2 descriptor address kick-off |
| 0x0C   | CH3_CTRL     | 3       | Channel 3 descriptor address kick-off |
| 0x10   | CH4_CTRL     | 4       | Channel 4 descriptor address kick-off |
| 0x14   | CH5_CTRL     | 5       | Channel 5 descriptor address kick-off |
| 0x18   | CH6_CTRL     | 6       | Channel 6 descriptor address kick-off |
| 0x1C   | CH7_CTRL     | 7       | Channel 7 descriptor address kick-off |

**Address Decode:**
```
relative_addr = apb_cmd_addr - BASE_ADDR
channel_id = relative_addr[4:2]  // Bits [4:2] select channel 0-7
                                 // Bits [1:0] ignored (word-aligned)
```

**Valid Range:** `BASE_ADDR + 0x00` to `BASE_ADDR + 0x1F` (32 bytes, 8 channels)

## Write Transaction Flow

### Normal Write (No Back-pressure)

```
Software → APB Slave → apbtodescr → Descriptor Engine

1. Software writes 0x1000_0000 to BASE+0x00 (Channel 0)
2. APB slave presents:
   - apb_cmd_valid = 1
   - apb_cmd_addr = BASE+0x00
   - apb_cmd_wdata = 0x1000_0000
   - apb_cmd_write = 1
3. apbtodescr decodes:
   - channel_id = 0
   - FSM: IDLE → ROUTE
4. apbtodescr routes to descriptor engine:
   - desc_apb_valid[0] = 1
   - desc_apb_addr[0] = 0x1000_0000
5. Descriptor engine accepts (has space in skid buffer):
   - desc_apb_ready[0] = 1
6. apbtodescr completes:
   - FSM: ROUTE → RESPOND
   - apb_rsp_valid = 1
   - apb_rsp_error = 0
7. APB slave completes write transaction

Duration: 3-4 cycles (typical)
```

### Write with Back-pressure

```
Software → APB Slave → apbtodescr → Descriptor Engine (busy)

1. Software writes 0x2000_0000 to BASE+0x04 (Channel 1)
2. APB slave presents command (same as above)
3. apbtodescr decodes channel_id = 1, enters ROUTE state
4. Descriptor engine NOT ready (skid buffer full):
   - desc_apb_ready[1] = 0
5. apbtodescr WAITS in ROUTE state:
   - desc_apb_valid[1] stays asserted
   - apb_rsp_valid stays low
   - APB transaction blocked
6. ... N cycles later ...
7. Descriptor engine becomes ready:
   - desc_apb_ready[1] = 1
8. apbtodescr completes:
   - FSM: ROUTE → RESPOND
   - apb_rsp_valid = 1
9. Transaction completes

Duration: 3 + N cycles (N = back-pressure cycles)
```

## FSM States

### State Diagram

```
        ┌─────────────────────────────────────────────┐
        │                                             │
        │                 IDLE                        │
        │  • apb_cmd_ready = 1                        │
        │  • Waiting for command                      │
        │                                             │
        └──────────────┬──────────────────────────────┘
                       │
                       │ apb_cmd_valid && apb_cmd_write
                       │ (latch: channel_id, wdata, error)
                       ▼
        ┌─────────────────────────────────────────────┐
        │                                             │
        │                ROUTE                        │
        │  • desc_apb_valid[ch] = 1                   │
        │  • Waiting for descriptor engine            │
        │                                             │
        └──────────────┬──────────────────────────────┘
                       │
                       │ desc_apb_ready[ch] || r_error
                       │
                       ▼
        ┌─────────────────────────────────────────────┐
        │                                             │
        │               RESPOND                       │
        │  • apb_rsp_valid = 1                        │
        │  • apb_rsp_error = r_error                  │
        │                                             │
        └──────────────┬──────────────────────────────┘
                       │
                       │ apb_rsp_ready
                       │
                       └──────────────▶ (back to IDLE)
```

### State Descriptions

| State   | Description                                    | Exit Condition              |
|---------|------------------------------------------------|-----------------------------|
| IDLE    | Waiting for APB command, ready to accept       | `apb_cmd_valid`             |
| ROUTE   | Routing to descriptor engine, waiting for ack  | `desc_apb_ready[ch]` or error |
| RESPOND | Sending APB response, waiting for ack          | `apb_rsp_ready`             |

## Error Handling

### Supported Errors

| Error Condition          | Detection Point | Response                |
|--------------------------|-----------------|-------------------------|
| Read request             | IDLE state      | `apb_rsp_error = 1`     |
| Address out of range     | IDLE state      | `apb_rsp_error = 1`     |
| (Future: channel disabled)| ROUTE state    | `apb_rsp_error = 1`     |

### Error Flow

```
1. Software reads from BASE+0x00 (read not supported)
   OR
   Software writes to BASE+0x100 (out of range)

2. apbtodescr IDLE state:
   - Latches r_error = 1
   - FSM: IDLE → ROUTE (briefly) → RESPOND

3. ROUTE state:
   - Skips descriptor engine routing (r_error asserted)
   - Immediately transitions to RESPOND

4. RESPOND state:
   - apb_rsp_valid = 1
   - apb_rsp_error = 1  ← Error flagged

5. APB slave returns error to software

Duration: 2-3 cycles (faster than normal write)
```

## Parameters

| Parameter      | Type             | Default      | Description                              |
|----------------|------------------|--------------|------------------------------------------|
| ADDR_WIDTH     | int              | 32           | APB address bus width                    |
| DATA_WIDTH     | int              | 32           | APB data bus width                       |
| NUM_CHANNELS   | int              | 8            | Number of descriptor engine channels     |
| BASE_ADDR      | logic[31:0]      | 0x0000_0000  | Base address for channel registers       |

## Interface Details

### APB CMD/RSP Interface (Slave Side)

**From PeakRDL APB Slave:**

| Signal           | Width        | Direction | Description                          |
|------------------|--------------|-----------|--------------------------------------|
| apb_cmd_valid    | 1            | Input     | Command valid from APB slave         |
| apb_cmd_ready    | 1            | Output    | Ready to accept command (IDLE state) |
| apb_cmd_addr     | ADDR_WIDTH   | Input     | Target address                       |
| apb_cmd_wdata    | DATA_WIDTH   | Input     | Write data (descriptor address)      |
| apb_cmd_write    | 1            | Input     | 1=write, 0=read                      |

| Signal           | Width        | Direction | Description                          |
|------------------|--------------|-----------|--------------------------------------|
| apb_rsp_valid    | 1            | Output    | Response valid to APB slave          |
| apb_rsp_ready    | 1            | Input     | APB slave ready to accept response   |
| apb_rsp_rdata    | DATA_WIDTH   | Output    | Read data (always 0 - writes only)   |
| apb_rsp_error    | 1            | Output    | Transaction error flag               |

### Descriptor Engine APB Interface (Master Side)

**To descriptor_engine[0..7] APB ports:**

| Signal           | Width                | Direction | Description                          |
|------------------|----------------------|-----------|--------------------------------------|
| desc_apb_valid   | [NUM_CHANNELS-1:0]   | Output    | Per-channel valid (one-hot)          |
| desc_apb_ready   | [NUM_CHANNELS-1:0]   | Input     | Per-channel ready from desc engine   |
| desc_apb_addr    | [NUM_CHANNELS-1:0][63:0] | Output | Descriptor address (zero-extended)  |

**Notes:**
- Only one `desc_apb_valid[ch]` asserted at a time (one-hot)
- All channels receive same address data (only selected channel's valid asserted)
- 32-bit APB write data zero-extended to 64-bit descriptor address
- Upper 32 bits always 0 (assumes descriptors in lower 4GB address space)

### Integration Control Signal

**For parent module response muxing:**

| Signal                       | Width | Direction | Description                          |
|------------------------------|-------|-----------|--------------------------------------|
| apb_descriptor_kickoff_hit   | 1     | Output    | This block handling kick-off transaction |

**Behavior:**
- Asserted when: `(state == ROUTE || state == RESPOND) && !r_error`
- Indicates apbtodescr is actively handling a valid kick-off write
- Parent module should route `apb_rsp_*` from this block when asserted
- Deasserted for error cases (read requests, out-of-range addresses)

**Usage:**
```systemverilog
// Parent module muxing APB responses
assign apb_rsp_valid = apb_descriptor_kickoff_hit ?
                       apbtodescr_rsp_valid :
                       register_file_rsp_valid;

assign apb_rsp_error = apb_descriptor_kickoff_hit ?
                       apbtodescr_rsp_error :
                       register_file_rsp_error;
```

## Timing Diagrams

### Normal Write Transaction

```
Cycle:      0      1      2      3      4
           ___    ___    ___    ___    ___
clk       _/ \_  / \_  / \_  / \_  / \_

           ─┐     ┌─────────────────────
apb_cmd_   _│_____│_____________________ valid

           ────────────────┐
apb_cmd_   ________________│____________ ready

FSM:        IDLE   ROUTE  RESPOND IDLE

           ___________┐           ┌─────
desc_apb_  ___________│___________│_____ valid[0]

           ___________┐           ┌─────
desc_apb_  ___________│___________│_____ ready[0]

           ________________┐     ┌──────
apb_rsp_   ________________│_____│______ valid

Latched:           [CH0]  [0x1000_0000]
```

### Write with Back-pressure (3 cycle stall)

```
Cycle:      0      1      2      3      4      5      6      7
           ___    ___    ___    ___    ___    ___    ___    ___
clk       _/ \_  / \_  / \_  / \_  / \_  / \_  / \_  / \_

           ─┐     ┌────────────────────────────────────────────
apb_cmd_   _│_____│____________________________________________ valid

           ────────────────────────────────────────────────┐
apb_cmd_   ______________________________________________ ┐__│ ready

FSM:        IDLE   ROUTE  ROUTE  ROUTE  ROUTE  RESPOND IDLE

           ___________┐                              ┌─────────
desc_apb_  ___________│______________________________│_________ valid[1]

           ______________________________┐           ┌─────────
desc_apb_  ______________________________│___________│_________ ready[1]
                                         ▲ (ready after 3 cycles)

           ___________________________________________┐    ┌────
apb_rsp_   ___________________________________________│____│____ valid

Note: ROUTE state extends until desc_apb_ready[1] asserts (3 cycle back-pressure)
```

## Design Rationale

### Why No Internal Registers?

**Advantages:**
1. **Zero latency** - Descriptor address passes directly through (no buffering delay)
2. **Simplicity** - FSM only, no FIFO management
3. **Area efficient** - Minimal logic (address decode + 3-state FSM)
4. **Natural back-pressure** - APB transaction blocks if descriptor engine busy

**Trade-offs:**
- APB master (software) must wait if descriptor engine skid buffer full
- Acceptable: Descriptor fetch is infrequent (only at transfer start)

### Why Zero-extend to 64-bit?

**Rationale:**
- Descriptor addresses are 64-bit in STREAM architecture
- APB data width is 32-bit (standard config bus width)
- Assume descriptors reside in lower 4GB physical address space
- Upper 32 bits hardcoded to 0 (physical address constraint)

**Future Enhancement:**
- Add second register for upper 32 bits if full 64-bit addressing needed
- Example: CH0_CTRL_LO (0x00), CH0_CTRL_HI (0x04), CH1_CTRL_LO (0x08), etc.

### Why FSM vs Combinational?

**FSM Benefits:**
1. **Explicit state visibility** - Clear transaction phases for debug
2. **Clean handshaking** - Well-defined valid/ready protocol timing
3. **Error handling** - Centralized error response generation
4. **Timing closure** - Registered paths avoid long combinational chains

## Integration Example

### Typical System Integration

```systemverilog
// PeakRDL APB slave (register interface)
apb_slave #(
    .BASE_ADDR(32'h4000_0000)
) u_apb_slave (
    .s_apb_*(...),          // System APB bus
    .reg_cmd_valid(apb_cmd_valid),
    .reg_cmd_ready(apb_cmd_ready),
    .reg_cmd_addr(apb_cmd_addr),
    .reg_cmd_wdata(apb_cmd_wdata),
    .reg_cmd_write(apb_cmd_write),

    .reg_rsp_valid(apb_rsp_valid_muxed),  // After mux
    .reg_rsp_ready(apb_rsp_ready),
    .reg_rsp_rdata(apb_rsp_rdata_muxed),  // After mux
    .reg_rsp_error(apb_rsp_error_muxed)   // After mux
);

// APB-to-Descriptor router (handles 0x00-0x1C)
apbtodescr #(
    .NUM_CHANNELS(8),
    .BASE_ADDR(32'h4000_0000)  // Match slave base
) u_apbtodescr (
    .clk(clk),
    .rst_n(rst_n),

    // APB slave interface
    .apb_cmd_valid(apb_cmd_valid),
    .apb_cmd_ready(apb_cmd_ready),
    .apb_cmd_addr(apb_cmd_addr),
    .apb_cmd_wdata(apb_cmd_wdata),
    .apb_cmd_write(apb_cmd_write),

    .apb_rsp_valid(apbtodescr_rsp_valid),
    .apb_rsp_ready(apb_rsp_ready),
    .apb_rsp_rdata(apbtodescr_rsp_rdata),
    .apb_rsp_error(apbtodescr_rsp_error),

    // Descriptor engine connections
    .desc_apb_valid(desc_apb_valid[7:0]),
    .desc_apb_ready(desc_apb_ready[7:0]),
    .desc_apb_addr(desc_apb_addr[7:0]),

    // Integration control
    .apb_descriptor_kickoff_hit(kickoff_hit)
);

// Register file (handles 0x100+)
stream_reg_file #(...) u_reg_file (
    .clk(clk),
    .rst_n(rst_n),

    .apb_cmd_valid(apb_cmd_valid),
    .apb_cmd_ready(),  // Not used - always ready
    .apb_cmd_addr(apb_cmd_addr),
    .apb_cmd_wdata(apb_cmd_wdata),
    .apb_cmd_write(apb_cmd_write),

    .apb_rsp_valid(regfile_rsp_valid),
    .apb_rsp_ready(apb_rsp_ready),
    .apb_rsp_rdata(regfile_rsp_rdata),
    .apb_rsp_error(regfile_rsp_error)
);

// Response muxing: Select between kick-off and register responses
assign apb_rsp_valid_muxed = kickoff_hit ? apbtodescr_rsp_valid : regfile_rsp_valid;
assign apb_rsp_rdata_muxed = kickoff_hit ? apbtodescr_rsp_rdata : regfile_rsp_rdata;
assign apb_rsp_error_muxed = kickoff_hit ? apbtodescr_rsp_error : regfile_rsp_error;

// Scheduler group array (contains 8 descriptor engines)
scheduler_group_array #(...) u_scheduler_groups (
    .apb_valid(desc_apb_valid),
    .apb_ready(desc_apb_ready),
    .apb_addr(desc_apb_addr),
    // ...
);
```

**Key Integration Points:**

1. **Command Distribution:** Both apbtodescr and register file receive same CMD interface
   - apbtodescr handles 0x00-0x1C (kick-off registers)
   - Register file handles 0x100+ (config/status registers)

2. **Response Muxing:** `apb_descriptor_kickoff_hit` selects response source
   - When HIGH: Route apbtodescr responses (kick-off transaction active)
   - When LOW: Route register file responses (config access)

3. **Address Decode:** apbtodescr internally decodes its range, asserts hit signal
   - Parent module doesn't need address decode logic
   - Clean separation of concerns

## Verification Considerations

### Testbench Focus Areas

1. **Address Decode**
   - All 8 channels addressable
   - Out-of-range addresses flagged as error
   - Channel ID extraction correct

2. **Back-pressure Handling**
   - Transaction blocks when `desc_apb_ready = 0`
   - Multiple cycle stalls handled correctly
   - No protocol violations during back-pressure

3. **Error Cases**
   - Read requests return error
   - Out-of-range writes return error
   - Error response faster than normal write

4. **Concurrent Operations**
   - Sequential writes to different channels
   - Verify no crosstalk between channels

### Key Assertions

```systemverilog
// Only one channel valid at a time
assert property (@(posedge clk) $onehot0(desc_apb_valid));

// Valid only in ROUTE state
assert property (@(posedge clk) |desc_apb_valid |-> (state == ROUTE));

// No simultaneous cmd_ready and rsp_valid
assert property (@(posedge clk) !(apb_cmd_ready && apb_rsp_valid));
```

## Performance Characteristics

| Metric                    | Value          | Notes                              |
|---------------------------|----------------|------------------------------------|
| Latency (no back-pressure)| 3 cycles       | IDLE → ROUTE → RESPOND             |
| Latency (with back-pressure)| 3 + N cycles | N = descriptor engine ready delay  |
| Throughput               | 1 write/3 cyc   | Sequential writes to same channel  |
| Area                     | ~500 gates      | Estimate: FSM + decode logic       |
| Max Frequency            | System clock    | Single-cycle paths, no timing issues|

## Related Modules

- **descriptor_engine** - Receives kick-off via `desc_apb_*` interface
- **scheduler_group_array** - Contains 8 descriptor engines
- **apb_slave** (PeakRDL) - Upstream APB register interface

## Revision History

| Version | Date       | Author         | Description                    |
|---------|------------|----------------|--------------------------------|
| 1.0     | 2025-10-20 | sean galloway  | Initial creation               |

---

**File:** `projects/components/stream/rtl/stream_macro/apbtodescr.sv`
**Documentation:** `projects/components/stream/docs/stream_spec/ch02_blocks/02_apbtodescr.md`
