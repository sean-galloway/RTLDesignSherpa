# CDC Handshake Module

## Overview

The `cdc_handshake` module is a specialized synchronization circuit designed to safely transfer data across different clock domains (Clock Domain Crossing or CDC). It implements a robust request-acknowledge handshaking protocol with metastability protection to ensure reliable data transfer between asynchronous clock domains.

## Features

- **Parameterizable Data Width**: Configurable data bus width via the `DATA_WIDTH` parameter.
- **Robust Handshaking Protocol**: Full request-acknowledge handshaking for safe transfers.
- **Metastability Protection**: Three-stage synchronizers to prevent metastability issues.
- **Safe Data Transfer**: Handles the complete lifecycle of cross-domain data transfer.
- **Comprehensive FSMs**: Separate state machines for source and destination domains.

## Module Parameters

| Parameter Name | Description | Default |
|----------------|-------------|---------|
| `DATA_WIDTH`   | Width of the data bus for transfer | 8 |

## Port Descriptions

### Source Clock Domain Signals

| Port Name    | Direction | Width         | Description |
|--------------|-----------|---------------|-------------|
| `clk_src`    | input     | 1             | Source domain clock |
| `rst_src_n`  | input     | 1             | Source domain asynchronous reset (active low) |
| `valid_src`  | input     | 1             | Source indicates data is valid for transfer |
| `ready_src`  | output    | 1             | Handshake ready signal back to source |
| `data_src`   | input     | `DATA_WIDTH`  | Data from source domain to be transferred |

### Destination Clock Domain Signals

| Port Name    | Direction | Width         | Description |
|--------------|-----------|---------------|-------------|
| `clk_dst`    | input     | 1             | Destination domain clock |
| `rst_dst_n`  | input     | 1             | Destination domain asynchronous reset (active low) |
| `valid_dst`  | output    | 1             | Indicates valid data to the receiver in destination domain |
| `ready_dst`  | input     | 1             | Receiver ready signal in destination domain |
| `data_dst`   | output    | `DATA_WIDTH`  | Data transferred to destination domain |

## Internal Signals and Registers

### Handshake Signals

| Signal Name  | Width | Domain  | Description |
|--------------|-------|---------|-------------|
| `r_req_src`  | 1     | src     | Request flag (source domain) - asserted when a new data transfer starts |
| `r_ack_dst`  | 1     | dst     | Acknowledge flag (destination domain) - asserted when transfer is accepted |

### Data Storage

| Signal Name     | Width        | Domain | Description |
|-----------------|--------------|--------|-------------|
| `r_async_data`  | `DATA_WIDTH` | src    | Holds the data word during transfer (latched in source domain) |
| `r_data_dst`    | `DATA_WIDTH` | dst    | Latched data in destination domain (to drive data_dst) |

### Synchronizers

| Signal Name   | Width | Domain | Description |
|---------------|-------|--------|-------------|
| `r_req_sync`  | 3     | dst    | 3-stage synchronizer for request signal (src→dst) |
| `r_ack_sync`  | 3     | src    | 3-stage synchronizer for acknowledge signal (dst→src) |
| `w_req_sync`  | 1     | dst    | Final synchronized request in destination domain |
| `w_ack_sync`  | 1     | src    | Final synchronized acknowledge in source domain |

### State Machines

| Signal Name     | Width | Domain | Description |
|-----------------|-------|--------|-------------|
| `r_src_state`   | 2     | src    | Current state of source domain FSM |
| `r_dst_state`   | 2     | dst    | Current state of destination domain FSM |

## FSM State Definitions

### Source Domain States (`src_state_t`)

| State Name        | Value | Description |
|-------------------|-------|-------------|
| `S_IDLE`          | 2'b00 | Source idle (ready for new data) |
| `S_WAIT_ACK`      | 2'b01 | Waiting for destination acknowledgment (data in flight) |
| `S_WAIT_ACK_CLR`  | 2'b10 | Waiting for acknowledgment to clear (handshake completion) |

### Destination Domain States (`dst_state_t`)

| State Name        | Value | Description |
|-------------------|-------|-------------|
| `D_IDLE`          | 2'b00 | Destination idle (waiting for request) |
| `D_WAIT_READY`    | 2'b01 | Received request, waiting for destination ready |
| `D_WAIT_REQ_CLR`  | 2'b10 | Acknowledgment sent, waiting for request to clear |

## Detailed Operation

### Synchronization Mechanism

The module employs a 3-stage synchronizer design to safely transfer control signals between clock domains:

1. **Request Signal Path (Source → Destination)**:
   - `r_req_src` (source domain) → `r_req_sync[0:2]` (3-stage sync) → `w_req_sync` (destination domain)

2. **Acknowledge Signal Path (Destination → Source)**:
   - `r_ack_dst` (destination domain) → `r_ack_sync[0:2]` (3-stage sync) → `w_ack_sync` (source domain)

The 3-stage synchronizer provides robust metastability protection, ensuring safe CDC operation even with completely asynchronous clocks.

### Source Domain Handshake FSM

The source domain state machine handles the following responsibilities:
- Data capture from the source
- Request generation and propagation
- Acknowledgment detection and handling
- Ready signal generation back to the source

#### State Transition Diagram

```
                            valid_src 
                                │
                                ▼
                ┌─────────┐ capture & ┌─────────────┐
                │  IDLE   │───────────►  WAIT_ACK   │
                └─────────┘ req=1     └─────────────┘
                   ▲                         │
                   │                         │ w_ack_sync
                   │                         ▼
                   │                ┌─────────────────┐
                   └────────────────┤ WAIT_ACK_CLR    │
                    !w_ack_sync     └─────────────────┘
```

#### State Behaviors

1. **S_IDLE**:
   - Sets `ready_src = 1` (ready for new transfer)
   - When `valid_src = 1`, captures `data_src` into `r_async_data`
   - Asserts `r_req_src = 1` to initiate transfer
   - Deasserts `ready_src = 0` to indicate busy
   - Transitions to `S_WAIT_ACK`

2. **S_WAIT_ACK**:
   - Maintains `r_req_src = 1` and `ready_src = 0`
   - When `w_ack_sync = 1` (ack received), deasserts `r_req_src = 0`
   - Transitions to `S_WAIT_ACK_CLR`

3. **S_WAIT_ACK_CLR**:
   - Maintains `r_req_src = 0` and `ready_src = 0`
   - When `w_ack_sync = 0` (ack cleared), sets `ready_src = 1`
   - Transitions back to `S_IDLE`

### Destination Domain Handshake FSM

The destination domain state machine handles:
- Request detection
- Data latching
- Handshaking with the destination receiver
- Acknowledgment generation back to source

#### State Transition Diagram

```
                        w_req_sync
                            │
                            ▼
            ┌─────────┐  latch   ┌─────────────┐
            │  IDLE   │─────────►│ WAIT_READY  │
            └─────────┘  data    └─────────────┘
                ▲                      │
                │                      │ ready_dst
                │                      ▼
                │               ┌─────────────────┐
                └───────────────┤  WAIT_REQ_CLR   │
                 !w_req_sync    └─────────────────┘
```

#### State Behaviors

1. **D_IDLE**:
   - Sets `r_ack_dst = 0` and waits for request
   - When `w_req_sync = 1` (request received):
     - Latches `r_async_data` into `r_data_dst`
     - Asserts `valid_dst = 1`
     - If `ready_dst = 1` already, sets `r_ack_dst = 1` and transitions to `D_WAIT_REQ_CLR`
     - Otherwise transitions to `D_WAIT_READY`

2. **D_WAIT_READY**:
   - Maintains `valid_dst = 1`
   - When `ready_dst = 1`, sets `r_ack_dst = 1` and `valid_dst = 0`
   - Transitions to `D_WAIT_REQ_CLR`
   - If request is withdrawn (`w_req_sync = 0`), returns to `D_IDLE`

3. **D_WAIT_REQ_CLR**:
   - Maintains `r_ack_dst = 1` and `valid_dst = 0`
   - When `w_req_sync = 0` (request cleared), sets `r_ack_dst = 0`
   - Transitions back to `D_IDLE`

## Complete Handshake Protocol Timing

The complete handshake protocol follows this timing sequence:

1. **Source Initiates Transfer**:
   - Source asserts `valid_src` with valid `data_src`
   - Module captures data, asserts `r_req_src`, deasserts `ready_src`

2. **Request Synchronization**:
   - `r_req_src` propagates through 3-stage synchronizer to destination domain

3. **Destination Processes Request**:
   - Destination detects `w_req_sync`, latches data, asserts `valid_dst`
   - Waits for receiver to assert `ready_dst`
   - Once `ready_dst` detected, asserts `r_ack_dst`, deasserts `valid_dst`

4. **Acknowledge Synchronization**:
   - `r_ack_dst` propagates through 3-stage synchronizer to source domain

5. **Source Detects Acknowledgment**:
   - Source detects `w_ack_sync`, deasserts `r_req_src`
   - Waits for `w_ack_sync` to clear

6. **Handshake Completion**:
   - Destination detects `w_req_sync` deasserted, deasserts `r_ack_dst`
   - Source detects `w_ack_sync` deasserted, asserts `ready_src`
   - System returns to idle state, ready for next transfer

## Key Design Considerations

### Metastability Protection

Metastability occurs when a flip-flop samples an input signal that is changing too close to the clock edge, potentially causing indeterminate states that can cascade into system failures. The CDC handshake mitigates this risk through:

1. **Triple-Stage Synchronizers**: Three consecutive flip-flops in the synchronizer chains provide sufficient time for metastable states to resolve (with extremely low probability of failure).

2. **Separate Control Paths**: Request and acknowledge signals have independent synchronizer chains.

3. **Stable Data Capture**: Data is captured in the source domain and held stable during the entire handshaking process, ensuring it is stable when sampled in the destination domain.

### Handshake Protocol Safety

The design ensures reliable data transfer through these safety mechanisms:

1. **Full Four-Phase Handshake**: A complete request-acknowledge-derequest-deacknowledge sequence ensures proper synchronization.

2. **Source-Side Data Stability**: Data is captured and held stable in `r_async_data` for the entire transfer duration.

3. **Destination-Side Data Latching**: Data is latched in the destination domain immediately upon detecting a valid request.

4. **Valid/Ready Handshaking**: Standard AXI-like valid/ready handshaking in both domains ensures proper flow control.

5. **Safe State Transitions**: The FSMs are designed to handle all edge cases, including signal withdrawals and reset conditions.

## Timing Diagrams

### Successful Transfer Sequence

```
                   Source Domain                 |             Destination Domain
                                                 |
clk_src        ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐  | clk_dst   ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
              _| |_| |_| |_| |_| |_| |_| |_| |_ |          _| |_| |_| |_| |_| |_| |_| |_| |_
                                                 |
valid_src     ┌───┐                              |
              |   |______________________________ |
                                                 |
data_src      ┌───────┐                          |
              |  Data |__________________________ |
                                                 |
ready_src     _______|┌─────────────────────┐    |
                      |                     |____ |
                                                 |
r_req_src     ________┌───────────┐              |
                      |           |______________ |
                                                 |
r_async_data  ________┌─────────────────────┐    | r_data_dst ________┌─────────────────┐
                      |     Data            |____ |                    |     Data        |____
                                                 |
w_ack_sync    ____________________┌───┐          | w_req_sync ____________┌───────┐
                                  |   |__________ |                        |       |__________
                                                 |
r_src_state   IDLE───WAIT_ACK───WAIT_ACK_CLR──IDLE | r_dst_state IDLE───WAIT_READY───WAIT_REQ_CLR──IDLE
                                                 |
                                                 | valid_dst  ______________┌───┐
                                                 |                          |   |______________
                                                 |
                                                 | ready_dst  ________________┌─┐
                                                 |                            | |______________
                                                 |
                                                 | r_ack_dst  ________________┌───────┐
                                                 |                            |       |________
```

## Usage Considerations

### Reset Strategy

The module uses asynchronous active-low reset inputs for both clock domains:

- `rst_src_n`: Resets the source domain logic
- `rst_dst_n`: Resets the destination domain logic

Both reset signals should be properly synchronized to their respective clock domains. Since each domain has its own reset, they can be reset independently or together, depending on system requirements.

### Clock Frequency Relationship

This CDC handshake works with any clock frequency relationship:

- Source clock can be faster than destination clock
- Destination clock can be faster than source clock
- Clocks can be completely asynchronous (no fixed relationship)

The handshake mechanism adapts to the relative speeds automatically.

### Transfer Rate Considerations

The maximum transfer rate is limited by:

1. **Synchronizer Latency**: Typically 3 clock cycles in each direction, leading to a minimum of 6 clock cycles for a complete handshake.

2. **Downstream Ready Timing**: Any delays in the destination asserting `ready_dst` will extend the transfer time.

3. **Clock Frequency Relationship**: The slower of the two clocks typically dominates the overall transfer rate.

### Integration Examples

#### Basic Usage Pattern

```systemverilog
// Source domain logic
logic [7:0] source_data;
logic source_valid, source_ready;

// Destination domain logic
logic [7:0] dest_data;
logic dest_valid, dest_ready;

// Instantiate CDC handshake
cdc_handshake #(
    .DATA_WIDTH(8)
) cdc_inst (
    .clk_src     (clk_a),
    .rst_src_n   (rst_a_n),
    .valid_src   (source_valid),
    .ready_src   (source_ready),
    .data_src    (source_data),
    
    .clk_dst     (clk_b),
    .rst_dst_n   (rst_b_n),
    .valid_dst   (dest_valid),
    .ready_dst   (dest_ready),
    .data_dst    (dest_data)
);

// Source domain process
always_ff @(posedge clk_a or negedge rst_a_n) begin
    if (!rst_a_n) begin
        source_valid <= 1'b0;
    end else begin
        if (source_ready && !source_valid) begin
            // Prepare new data for transfer
            source_data <= new_data;
            source_valid <= 1'b1;
        end else if (source_ready && source_valid) begin
            // Transfer accepted, clear valid
            source_valid <= 1'b0;
        end
    end
end

// Destination domain process
always_ff @(posedge clk_b or negedge rst_b_n) begin
    if (!rst_b_n) begin
        dest_ready <= 1'b0;
    end else begin
        if (dest_valid && !dest_ready) begin
            // Process the received data
            process_data(dest_data);
            dest_ready <= 1'b1;
        end else if (!dest_valid) begin
            // No data to process, clear ready
            dest_ready <= 1'b0;
        end
    end
end
```

#### AXI Stream Integration

The module can be used to bridge AXI Stream interfaces across clock domains:

```systemverilog
// AXI Stream interfaces
interface axi_stream_if #(
    parameter int DATA_WIDTH = 8
) (
    input logic clk,
    input logic rst_n
);
    logic [DATA_WIDTH-1:0] tdata;
    logic tvalid;
    logic tready;
    // Additional AXI Stream signals if needed
    // (tlast, tkeep, etc.)
endinterface

// Source and destination AXI Stream interfaces
axi_stream_if #(.DATA_WIDTH(8)) axi_src  (.clk(clk_a), .rst_n(rst_a_n));
axi_stream_if #(.DATA_WIDTH(8)) axi_dest (.clk(clk_b), .rst_n(rst_b_n));

// CDC Handshake to bridge the interfaces
cdc_handshake #(
    .DATA_WIDTH(8)
) axi_cdc_bridge (
    .clk_src    (clk_a),
    .rst_src_n  (rst_a_n),
    .valid_src  (axi_src.tvalid),
    .ready_src  (axi_src.tready),
    .data_src   (axi_src.tdata),
    
    .clk_dst    (clk_b),
    .rst_dst_n  (rst_b_n),
    .valid_dst  (axi_dest.tvalid),
    .ready_dst  (axi_dest.tready),
    .data_dst   (axi_dest.tdata)
);
```

## Verification Strategies

### Functional Verification

To verify correct operation of the CDC handshake module:

1. **Basic Handshake Test**: Verify basic data transfer with both sides ready.

2. **Back-to-Back Transfers**: Test multiple transfers in quick succession.

3. **Flow Control Testing**: 
   - Delay `ready_dst` assertion to test flow control
   - Test with variable delays between transfers

4. **Edge Cases**:
   - Reset during transfer
   - Reset of individual domains
   - Valid withdrawn before transfer completion

5. **Metastability Injection**: 
   - Introduce timing violations in simulation
   - Verify synchronizers handle metastability correctly

### Formal Verification

Key properties to verify formally:

1. **Data Integrity**: Data received matches data sent.

2. **Protocol Safety**: Handshake sequence always completes correctly.

3. **Deadlock Freedom**: System cannot enter deadlock states.

4. **Reset Behavior**: Module recovers properly from reset in any state.

5. **CDC Safety**: All cross-domain signals properly synchronized.

## Implementation and Optimization

### Area Considerations

The module's area is primarily determined by:

1. **Data Width**: The `DATA_WIDTH` parameter directly impacts register usage.

2. **Synchronizer Depth**: The 3-stage synchronizers use six flip-flops for control signals.

3. **State Machines**: Two small state machines (2 bits each).

### Timing Considerations

1. **Clock Domain Crossing**: The synchronizers create well-defined CDC paths.

2. **Critical Paths**: Generally non-critical, as each domain operates within its own clock.

3. **Timing Constraints**: Each domain should be constrained appropriately, with CDC paths identified as asynchronous crossings.

## Related Modules

- **gaxi_fifo_async**: Asynchronous FIFO implementation for larger data buffering needs.
- **gaxi_skid_buffer_async**: Asynchronous skid buffer with integrated CDC support.
- **glitch_free_n_dff_arn**: Multi-stage synchronizer for clock domain crossing.

## Summary

The CDC handshake module provides a robust, metastability-protected mechanism for transferring data between asynchronous clock domains. It implements a complete four-phase handshake protocol with separate state machines in each domain to manage the request-acknowledge cycle. The design ensures data integrity across any clock frequency relationship while providing proper flow control through standard valid-ready handshaking.
