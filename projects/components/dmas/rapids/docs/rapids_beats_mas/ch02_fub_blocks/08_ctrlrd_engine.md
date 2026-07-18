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

# Control-Read Engine Specification

**Module:** `ctrlrd_engine.sv`
**Location:** `projects/components/dmas/rapids/rtl/fub/`
**Status:** Implemented
**Last Updated:** 2026-07-12

---

## Overview

The Control-Read Engine implements the `CTRL_READ` descriptor opcode (`DESC_OP_CTRL_READ = 2'b01`) as a **consumer gate**. When the scheduler decodes a `CTRL_READ` descriptor, it hands the engine a poll address, an expected value, and a compare mask. The engine issues an AXI4 read to the poll address, applies the mask to the returned data, and compares `(read_data & mask)` against the expected value. If they match, the gate is satisfied and the descriptor chain proceeds; if not, the engine retries. Retries are bounded so a gate that never matches cannot hang the channel.

One Control-Read Engine is instantiated per channel in `scheduler_group_beats.sv` (`u_ctrlrd_engine`), configured for 32-bit AXI reads.

### Key Features

- **Consumer Gate Semantics:** Polls memory until `(read_data & mask) == expected`
- **Masked Comparison:** Only the masked bits of the polled word participate in the match
- **Bounded Retry:** `cfg_ctrlrd_max_try` (0-511) caps the number of poll attempts
- **1 microsecond Retry Pacing:** Retries wait for `tick_1us` from the scheduler group
- **Error on Exhaustion:** Asserts `ctrlrd_error` if the gate never matches within budget
- **Null Address Fast-Path:** A poll address of zero completes immediately as a match
- **Channel Reset Support:** Drains cleanly on `cfg_channel_reset`
- **MonBus Integration:** Completion, retry, and error events

### Block Diagram

### Figure 2.8.1: Control-Read Engine Block Diagram

```
                        +---------------------------+
    ctrlrd_valid     -->|                           |--> ar_valid
    ctrlrd_ready     <--|                           |--> ar_addr
    ctrlrd_pkt_addr  -->|                           |<-- ar_ready
    ctrlrd_pkt_data  -->|   CONTROL-READ ENGINE     |
    ctrlrd_pkt_mask  -->|                           |<-- r_valid
                        |   poll: (rd & mask)       |<-- r_data
    cfg_ctrlrd_max_try->|          == expected ?    |--> r_ready
    tick_1us         -->|                           |<-- r_resp
                        |                           |
    ctrlrd_error     <--|                           |
    ctrlrd_result    <--|                           |--> mon_valid
    ctrlrd_engine_idle<-|                           |--> mon_packet
                        +---------------------------+
```

**Source:** [08_ctrlrd_engine_block.mmd](../assets/mermaid/08_ctrlrd_engine_block.mmd)

---

## Parameters

```systemverilog
parameter int CHANNEL_ID = 0;                    // Channel identifier
parameter int NUM_CHANNELS = 32;                 // Total channels
parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS); // Channel index width (derived)
parameter int ADDR_WIDTH = 64;                   // Address bus width
parameter int AXI_DATA_WIDTH = 64;               // AXI read data width (>= 32)
parameter int AXI_ID_WIDTH = 8;                  // AXI ID width (>= CHAN_WIDTH)

// Monitor Bus Parameters
parameter logic [15:0] MON_AGENT_ID  = 16'h0030; // Control-Read Engine Agent ID
parameter logic [7:0]  MON_UNIT_ID   = 8'h02;    // Unit identifier
parameter logic [8:0]  MON_CHANNEL_ID = 9'h000;  // Base channel ID
```

: Table 2.8.1: Control-Read Engine Parameters

Parameter validation enforces `AXI_ID_WIDTH >= CHAN_WIDTH` and `AXI_DATA_WIDTH >= 32`
(the engine consumes only the lower 32 bits of the read data). The per-channel
instance in `scheduler_group_beats.sv` overrides `AXI_DATA_WIDTH` to 32.

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low asynchronous reset |

: Table 2.8.2: Clock and Reset

### Scheduler Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `ctrlrd_valid` | input | 1 | Gate request valid from scheduler |
| `ctrlrd_ready` | output | 1 | Engine ready to accept a request |
| `ctrlrd_pkt_addr` | input | AW | Poll address (descriptor `poll_addr[63:0]`) |
| `ctrlrd_pkt_data` | input | 32 | Expected value (descriptor `expected[95:64]`) |
| `ctrlrd_pkt_mask` | input | 32 | Compare mask (descriptor `mask[127:96]`) |
| `ctrlrd_error` | output | 1 | Gate failed (retries exhausted or AXI error) |
| `ctrlrd_result` | output | 32 | Last read value (lower 32 bits) |
| `ctrlrd_engine_idle` | output | 1 | Engine idle (post-issue completion indicator) |

: Table 2.8.3: Scheduler Interface

### Configuration Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_ctrlrd_max_try` | input | 9 | Poll retry budget, 0-511 (from `CTRL_CONFIG.CTRLRD_MAX_TRY`) |
| `cfg_channel_reset` | input | 1 | Per-channel reset request |
| `tick_1us` | input | 1 | 1 microsecond tick that paces retries |

: Table 2.8.4: Configuration Interface

### AXI4 Read Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `ar_valid` | output | 1 | Read address valid |
| `ar_ready` | input | 1 | Read address ready |
| `ar_addr` | output | AW | Read address (poll address) |
| `ar_len` | output | 8 | Burst length (`8'h00`, single beat) |
| `ar_size` | output | 3 | Burst size (`3'b010`, 4 bytes) |
| `ar_burst` | output | 2 | Burst type (`2'b01`, INCR) |
| `ar_id` | output | ID | Transaction ID (channel-derived) |
| `ar_lock` | output | 1 | Lock (`1'b0`, normal access) |
| `ar_cache` | output | 4 | Cache (`4'b0010`, non-cacheable bufferable) |
| `ar_prot` | output | 3 | Protection (`3'b000`) |
| `ar_qos` | output | 4 | Quality of service (`4'h0`) |
| `ar_region` | output | 4 | Region (`4'h0`) |
| `r_valid` | input | 1 | Read data valid (shared channel) |
| `r_ready` | output | 1 | Read data ready |
| `r_data` | input | ADW | Read data (lower 32 bits used) |
| `r_id` | input | ID | Read response ID (matched to our request) |
| `r_resp` | input | 2 | Read response |
| `r_last` | input | 1 | Read last beat |

: Table 2.8.5: AXI4 Read Master Interface

### MonBus Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `i_mon_time` | input | 64 | Side-band monitor timestamp |
| `mon_valid` | output | 1 | Monitor packet valid |
| `mon_ready` | input | 1 | Monitor consumer ready |
| `mon_packet` | output | 128 | Monitor packet (`monitor_packet_t`) |
| `mon_timestamp` | output | 64 | Monitor packet timestamp |

: Table 2.8.6: MonBus Interface

---

## FSM States

### Figure 2.8.2: Control-Read Engine FSM

```
                    +-----------+
        rst_n=0 --> | READ_IDLE |<-------------------+
                    +-----+-----+                    |
                          |                          |
                  request accepted                   |
                          |                          |
                          v                          |
                 +-----------------+                 |
                 | READ_ISSUE_ADDR |                 |
                 +--------+--------+                 |
                          |                          |
              null addr   | ar_ready handshake       |
              +-----------+-----------+              |
              |                       |              |
              v                       v              |
        +------------+       +----------------+      |
        | READ_MATCH |       | READ_WAIT_DATA |      |
        +-----+------+       +--------+-------+      |
              |                       |              |
              |               r_valid (our ID)       |
              |                       v              |
              |              +--------------+        |
              |              | READ_COMPARE |        |
              |              +------+-------+        |
              |                     |                |
              |   +-----------------+-------------+  |
              |   |         |                     |  |
              |  match   retry left           no retry / AXI err
              |   |         |                     |  |
              |   |         v                     v  |
              |   |  +-----------------+   +------------+
              |   |  | READ_RETRY_WAIT |   | READ_ERROR |
              |   |  +--------+--------+   +-----+------+
              |   |           |                  |
              |   |     tick_1us -> reissue      |
              |   +-----------> READ_ISSUE_ADDR  |
              |                                  |
              +----------------------------------+
```

**Source:** [08_ctrlrd_engine_fsm.mmd](../assets/mermaid/08_ctrlrd_engine_fsm.mmd)

State summary:

- **READ_IDLE:** Waits for a request from the scheduler (via a two-deep skid buffer). Latches poll address, expected value, mask, and the AXI ID; initializes the retry counter from `cfg_ctrlrd_max_try`.
- **READ_ISSUE_ADDR:** Drives `ar_valid`. A null address (`64'h0`) shortcuts to `READ_MATCH`; otherwise, once `ar_ready` handshakes, advances to `READ_WAIT_DATA`.
- **READ_WAIT_DATA:** Accepts the read response whose `r_id` matches the channel ID, capturing the lower 32 bits and the response code.
- **READ_COMPARE:** On an AXI error response, goes to `READ_ERROR`. On a masked match, goes to `READ_MATCH`. Otherwise, if retries remain, decrements the counter and goes to `READ_RETRY_WAIT`; if the budget is exhausted, goes to `READ_ERROR`.
- **READ_RETRY_WAIT:** Waits for `tick_1us`, then reissues the read.
- **READ_MATCH:** Gate satisfied. Clears the error flag and returns to `READ_IDLE`.
- **READ_ERROR:** Sets `ctrlrd_error` and returns to `READ_IDLE`.

---

## Operation

### Masked Compare

The engine gates on a masked equality check:

```
w_masked_expected = ctrlrd_pkt_data & ctrlrd_pkt_mask
w_masked_actual   = r_data[31:0]    & ctrlrd_pkt_mask
w_data_match      = (w_masked_expected == w_masked_actual)
```

Only the bits set in `mask` participate. A mask of `32'hFFFFFFFF` compares the full
word; a mask of a single bit turns the gate into a flag-poll.

### Retry Budget and Pacing

The retry counter is loaded from `cfg_ctrlrd_max_try` when the request is accepted.
On each non-matching, non-error compare with retries remaining, the counter
decrements and the engine parks in `READ_RETRY_WAIT` until the next `tick_1us`,
which paces successive polls at roughly 1 microsecond intervals. When the counter
reaches zero without a match, the engine transitions to `READ_ERROR` and asserts
`ctrlrd_error`, so a never-matching gate cannot stall the channel indefinitely.

`cfg_ctrlrd_max_try` is driven by the `CTRL_CONFIG` register at offset `0x240`,
field `CTRLRD_MAX_TRY[8:0]` (0-511, reset 16).

### Null Address Fast-Path

If the latched poll address is `64'h0`, the engine treats the gate as already
satisfied: `READ_ISSUE_ADDR` transitions directly to `READ_MATCH` without issuing
an AXI read. This lets software emit an unconditional (no-op) gate.

### AXI Read Transaction

Polls are single-beat, 4-byte INCR reads (`ar_len = 0`, `ar_size = 3'b010`,
`ar_burst = 2'b01`). The `ar_id` is derived from `CHANNEL_ID`, and only responses
whose `r_id` matches are consumed on the shared read data channel. `ctrlrd_result`
exposes the last captured 32-bit value; in the per-channel instantiation the
scheduler gates on match/error rather than the raw value, so `ctrlrd_result` is
left unconnected there.

### Channel Reset

`cfg_channel_reset` is registered into `r_channel_reset_active`. While asserted, the
engine refuses new requests (`ctrlrd_ready` is forced low), any in-flight state is
cleared, and the FSM is driven back to `READ_IDLE`. `ctrlrd_engine_idle` asserts
only in `READ_IDLE` with no pending request and no active channel reset.

---

## MonBus Reporting

The engine emits monitor packets on notable events:

| Event | Packet Type | Code | Payload |
|-------|-------------|------|---------|
| Gate satisfied (non-null) | `PktTypeCompletion` | `CORE_COMPL_CTRLRD_COMPLETED` | Poll address |
| Retry attempt | `PktTypePerf` | `CORE_PERF_CTRLRD_RETRY` | Remaining retry count |
| Retries exhausted | `PktTypeError` | `CORE_ERR_CTRLRD_MAX_RETRIES` | Poll address |
| AXI error response | `PktTypeError` | `AXI_ERR_RESP_SLVERR` / `AXI_ERR_RESP_DECERR` | Response code |

: Table 2.8.7: MonBus Events

All packets carry `MON_AGENT_ID`, `MON_UNIT_ID`, and `MON_CHANNEL_ID`, and are
timestamped from `i_mon_time`.

---

## Descriptor Field Mapping

The `CTRL_READ` opcode reinterprets the shared 256-bit descriptor (the descriptor
engine's existing field extraction is reused):

| Descriptor Field | Bits | Engine Port |
|------------------|------|-------------|
| `poll_addr` | `[63:0]` | `ctrlrd_pkt_addr` |
| `expected` | `[95:64]` | `ctrlrd_pkt_data` |
| `mask` | `[127:96]` | `ctrlrd_pkt_mask` |
| `max_try` | `[143:128]` | Per-descriptor budget (0 = use `cfg_ctrlrd_max_try` default) |

: Table 2.8.8: CTRL_READ Descriptor Field Mapping

---

**Last Updated:** 2026-07-12
