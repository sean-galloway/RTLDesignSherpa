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

# AMBA4 Event Code Reference

This is the per-protocol event-code reference for the AMBA4 family — AXI4 /
AXI4-Lite, APB4, and AXI4-Stream. The 8-bit `event_code` field of every
monbus packet sourced by an AMBA4 monitor takes its value from one of the
enums defined in `rtl/amba/includes/monitor_amba4_pkg.sv` and listed below.
For the universal packet layout, `protocol` / `packet_type` enums, and
helper functions see
[`monitor_package_spec.md`](./monitor_package_spec.md).

Each enum is 8 bits wide. Slots `8'h0`–`8'hE` are reserved for predefined
codes (with `_RESERVED_*` placeholders absorbing unused indices) and slot
`8'hF` is always the `*_USER_DEFINED` escape hatch.

---

## AXI4 Event Codes

Seven categories cover the AXI4 / AXI4-Lite monitor surface: error, timeout,
completion, threshold, performance, address-match, and debug. The
`protocol` field for every code in this section is `PROTOCOL_AXI` (4'h0).

### `axi_error_code_t`

**Packet context:** `packet_type = PktTypeError`, `protocol = PROTOCOL_AXI`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0 | `AXI_ERR_RESP_SLVERR`       | Slave error response |
| 8'h1 | `AXI_ERR_RESP_DECERR`       | Decode error response |
| 8'h2 | `AXI_ERR_DATA_ORPHAN`       | Data without command |
| 8'h3 | `AXI_ERR_RESP_ORPHAN`       | Response without transaction |
| 8'h4 | `AXI_ERR_PROTOCOL`          | Protocol violation |
| 8'h5 | `AXI_ERR_BURST_LENGTH`      | Invalid burst length |
| 8'h6 | `AXI_ERR_BURST_SIZE`        | Invalid burst size |
| 8'h7 | `AXI_ERR_BURST_TYPE`        | Invalid burst type |
| 8'h8 | `AXI_ERR_ID_COLLISION`      | ID collision detected |
| 8'h9 | `AXI_ERR_WRITE_BEFORE_ADDR` | Write data before address |
| 8'hA | `AXI_ERR_RESP_BEFORE_DATA`  | Response before data complete |
| 8'hB | `AXI_ERR_LAST_MISSING`      | Missing LAST signal |
| 8'hC | `AXI_ERR_STROBE_ERROR`      | Write strobe error |
| 8'hD | `AXI_ERR_ADDR_RANGE`        | Address-range violation (from `axi_monitor_addr_check`) |
| 8'hE | _(reserved)_                | _Reserved for future use_ |
| 8'hF | `AXI_ERR_USER_DEFINED`      | User-defined error |

### `axi_timeout_code_t`

**Packet context:** `packet_type = PktTypeTimeout`, `protocol = PROTOCOL_AXI`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXI_TIMEOUT_CMD`          | Command/Address timeout |
| 8'h1      | `AXI_TIMEOUT_DATA`         | Data timeout |
| 8'h2      | `AXI_TIMEOUT_RESP`         | Response timeout |
| 8'h3      | `AXI_TIMEOUT_HANDSHAKE`    | Handshake timeout |
| 8'h4      | `AXI_TIMEOUT_BURST`        | Burst completion timeout |
| 8'h5      | `AXI_TIMEOUT_EXCLUSIVE`    | Exclusive access timeout |
| 8'h6–8'hE | _(reserved)_               | _Reserved for future use_ |
| 8'hF      | `AXI_TIMEOUT_USER_DEFINED` | User-defined timeout |

### `axi_completion_code_t`

**Packet context:** `packet_type = PktTypeCompletion`, `protocol = PROTOCOL_AXI`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXI_COMPL_TRANS_COMPLETE` | Transaction completed successfully |
| 8'h1      | `AXI_COMPL_READ_COMPLETE`  | Read transaction complete |
| 8'h2      | `AXI_COMPL_WRITE_COMPLETE` | Write transaction complete |
| 8'h3      | `AXI_COMPL_BURST_COMPLETE` | Burst transaction complete |
| 8'h4      | `AXI_COMPL_EXCLUSIVE_OK`   | Exclusive access completed |
| 8'h5      | `AXI_COMPL_EXCLUSIVE_FAIL` | Exclusive access failed |
| 8'h6      | `AXI_COMPL_ATOMIC_OK`      | Atomic operation completed |
| 8'h7      | `AXI_COMPL_ATOMIC_FAIL`    | Atomic operation failed |
| 8'h8–8'hE | _(reserved)_               | _Reserved for future use_ |
| 8'hF      | `AXI_COMPL_USER_DEFINED`   | User-defined completion |

### `axi_threshold_code_t`

**Packet context:** `packet_type = PktTypeThreshold`, `protocol = PROTOCOL_AXI`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXI_THRESH_ACTIVE_COUNT` | Active transaction count threshold |
| 8'h1      | `AXI_THRESH_LATENCY`      | Latency threshold |
| 8'h2      | `AXI_THRESH_ERROR_RATE`   | Error rate threshold |
| 8'h3      | `AXI_THRESH_THROUGHPUT`   | Throughput threshold |
| 8'h4      | `AXI_THRESH_QUEUE_DEPTH`  | Queue depth threshold |
| 8'h5      | `AXI_THRESH_BANDWIDTH`    | Bandwidth utilization threshold |
| 8'h6      | `AXI_THRESH_OUTSTANDING`  | Outstanding transactions threshold |
| 8'h7      | `AXI_THRESH_BURST_SIZE`   | Average burst size threshold |
| 8'h8–8'hE | _(reserved)_              | _Reserved for future use_ |
| 8'hF      | `AXI_THRESH_USER_DEFINED` | User-defined threshold |

### `axi_performance_code_t`

**Packet context:** `packet_type = PktTypePerf`, `protocol = PROTOCOL_AXI`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXI_PERF_ADDR_LATENCY`     | Address phase latency |
| 8'h1      | `AXI_PERF_DATA_LATENCY`     | Data phase latency |
| 8'h2      | `AXI_PERF_RESP_LATENCY`     | Response phase latency |
| 8'h3      | `AXI_PERF_TOTAL_LATENCY`    | Total transaction latency |
| 8'h4      | `AXI_PERF_THROUGHPUT`       | Transaction throughput |
| 8'h5      | `AXI_PERF_ERROR_RATE`       | Error rate |
| 8'h6      | `AXI_PERF_ACTIVE_COUNT`     | Current active transaction count |
| 8'h7      | `AXI_PERF_COMPLETED_COUNT`  | Total completed transaction count |
| 8'h8      | `AXI_PERF_ERROR_COUNT`      | Total error transaction count |
| 8'h9      | `AXI_PERF_BANDWIDTH_UTIL`   | Bandwidth utilization |
| 8'hA      | `AXI_PERF_QUEUE_DEPTH`      | Average queue depth |
| 8'hB      | `AXI_PERF_BURST_EFFICIENCY` | Burst efficiency metric |
| 8'hC–8'hD | _(reserved)_                | _Reserved for future use_ |
| 8'hE      | `AXI_PERF_READ_WRITE_RATIO` | Read/Write transaction ratio |
| 8'hF      | `AXI_PERF_USER_DEFINED`     | User-defined performance |

### `axi_addr_match_code_t`

**Packet context:** `packet_type = PktTypeAddrMatch`, `protocol = PROTOCOL_AXI`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXI_ADDR_EXACT_MATCH`   | Exact address match |
| 8'h1      | `AXI_ADDR_RANGE_MATCH`   | Address within range |
| 8'h2      | `AXI_ADDR_MASK_MATCH`    | Address mask match |
| 8'h3      | `AXI_ADDR_PATTERN_MATCH` | Address pattern match |
| 8'h4      | `AXI_ADDR_SEQUENTIAL`    | Sequential address access |
| 8'h5      | `AXI_ADDR_STRIDE_MATCH`  | Stride pattern match |
| 8'h6      | `AXI_ADDR_HOTSPOT`       | Address hotspot detected |
| 8'h7      | `AXI_ADDR_CONFLICT`      | Address conflict detected |
| 8'h8–8'hE | _(reserved)_             | _Reserved for future use_ |
| 8'hF      | `AXI_ADDR_USER_DEFINED`  | User-defined address match |

### `axi_debug_code_t`

**Packet context:** `packet_type = PktTypeDebug`, `protocol = PROTOCOL_AXI`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXI_DEBUG_STATE_CHANGE`   | AXI state machine change |
| 8'h1      | `AXI_DEBUG_PIPELINE_STALL` | Pipeline stall event |
| 8'h2      | `AXI_DEBUG_BACKPRESSURE`   | Backpressure event |
| 8'h3      | `AXI_DEBUG_OUTSTANDING`    | Outstanding transaction count |
| 8'h4      | `AXI_DEBUG_REORDER_BUFFER` | Reorder buffer status |
| 8'h5      | `AXI_DEBUG_ID_ALLOCATION`  | Transaction ID allocation |
| 8'h6      | `AXI_DEBUG_QOS_ESCALATION` | QoS escalation event |
| 8'h7      | `AXI_DEBUG_HANDSHAKE`      | Handshake timing event |
| 8'h8      | `AXI_DEBUG_QUEUE_STATUS`   | Queue status change |
| 8'h9      | `AXI_DEBUG_COUNTER`        | Counter snapshot |
| 8'hA      | `AXI_DEBUG_FIFO_STATUS`    | FIFO status |
| 8'hB–8'hE | _(reserved)_               | _Reserved for future use_ |
| 8'hF      | `AXI_DEBUG_USER_DEFINED`   | User-defined debug |

---

## APB4 Event Codes

Six categories cover the APB4 monitor surface: error, timeout, completion,
threshold, performance, and debug. The `protocol` field for every code in
this section is `PROTOCOL_APB` (4'h2).

### `apb_error_code_t`

**Packet context:** `packet_type = PktTypeError`, `protocol = PROTOCOL_APB`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `APB_ERR_PSLVERR`          | Peripheral slave error |
| 8'h1      | `APB_ERR_SETUP_VIOLATION`  | Setup phase protocol violation |
| 8'h2      | `APB_ERR_ACCESS_VIOLATION` | Access phase protocol violation |
| 8'h3      | `APB_ERR_STROBE_ERROR`     | Write strobe error |
| 8'h4      | `APB_ERR_ADDR_DECODE`      | Address decode error |
| 8'h5      | `APB_ERR_PROT_VIOLATION`   | Protection violation (PPROT) |
| 8'h6      | `APB_ERR_ENABLE_ERROR`     | Enable phase error |
| 8'h7      | `APB_ERR_READY_ERROR`      | PREADY protocol error |
| 8'h8      | `APB_ERR_ADDR_RANGE`       | Address-range violation (from `apb_monitor_addr_check`) |
| 8'h9–8'hE | _(reserved)_               | _Reserved for future use_ |
| 8'hF      | `APB_ERR_USER_DEFINED`     | User-defined error |

### `apb_timeout_code_t`

**Packet context:** `packet_type = PktTypeTimeout`, `protocol = PROTOCOL_APB`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `APB_TIMEOUT_SETUP`        | Setup phase timeout |
| 8'h1      | `APB_TIMEOUT_ACCESS`       | Access phase timeout |
| 8'h2      | `APB_TIMEOUT_ENABLE`       | Enable phase timeout (PREADY stuck) |
| 8'h3      | `APB_TIMEOUT_PREADY_STUCK` | PREADY stuck low |
| 8'h4      | `APB_TIMEOUT_TRANSFER`     | Overall transfer timeout |
| 8'h5–8'hE | _(reserved)_               | _Reserved for future use_ |
| 8'hF      | `APB_TIMEOUT_USER_DEFINED` | User-defined timeout |

### `apb_completion_code_t`

**Packet context:** `packet_type = PktTypeCompletion`, `protocol = PROTOCOL_APB`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `APB_COMPL_TRANS_COMPLETE` | Transaction completed |
| 8'h1      | `APB_COMPL_READ_COMPLETE`  | Read transaction complete |
| 8'h2      | `APB_COMPL_WRITE_COMPLETE` | Write transaction complete |
| 8'h3–8'hE | _(reserved)_               | _Reserved for future use_ |
| 8'hF      | `APB_COMPL_USER_DEFINED`   | User-defined completion |

### `apb_threshold_code_t`

**Packet context:** `packet_type = PktTypeThreshold`, `protocol = PROTOCOL_APB`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `APB_THRESH_LATENCY`      | Transaction latency threshold |
| 8'h1      | `APB_THRESH_ERROR_RATE`   | Error rate threshold |
| 8'h2      | `APB_THRESH_ACTIVE_COUNT` | Active transaction count threshold |
| 8'h3      | `APB_THRESH_THROUGHPUT`   | Throughput threshold |
| 8'h4–8'hE | _(reserved)_              | _Reserved for future use_ |
| 8'hF      | `APB_THRESH_USER_DEFINED` | User-defined threshold |

### `apb_performance_code_t`

**Packet context:** `packet_type = PktTypePerf`, `protocol = PROTOCOL_APB`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `APB_PERF_READ_LATENCY`    | Read transaction latency |
| 8'h1      | `APB_PERF_WRITE_LATENCY`   | Write transaction latency |
| 8'h2      | `APB_PERF_THROUGHPUT`      | Transaction throughput |
| 8'h3      | `APB_PERF_ERROR_RATE`      | Error rate |
| 8'h4      | `APB_PERF_ACTIVE_COUNT`    | Active transaction count |
| 8'h5      | `APB_PERF_COMPLETED_COUNT` | Completed transaction count |
| 8'h6–8'hE | _(reserved)_               | _Reserved for future use_ |
| 8'hF      | `APB_PERF_USER_DEFINED`    | User-defined performance |

### `apb_debug_code_t`

**Packet context:** `packet_type = PktTypeDebug`, `protocol = PROTOCOL_APB`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `APB_DEBUG_STATE_CHANGE`  | APB state changed |
| 8'h1      | `APB_DEBUG_SETUP_PHASE`   | Setup phase event |
| 8'h2      | `APB_DEBUG_ACCESS_PHASE`  | Access phase event |
| 8'h3      | `APB_DEBUG_ENABLE_PHASE`  | Enable phase event |
| 8'h4      | `APB_DEBUG_PSEL_TRACE`    | PSEL trace |
| 8'h5      | `APB_DEBUG_PENABLE_TRACE` | PENABLE trace |
| 8'h6      | `APB_DEBUG_PREADY_TRACE`  | PREADY trace |
| 8'h7      | `APB_DEBUG_PPROT_TRACE`   | PPROT trace |
| 8'h8      | `APB_DEBUG_PSTRB_TRACE`   | PSTRB trace |
| 8'h9–8'hE | _(reserved)_              | _Reserved for future use_ |
| 8'hF      | `APB_DEBUG_USER_DEFINED`  | User-defined debug |

---

## AXIS4 Event Codes

Six categories cover the AXI4-Stream monitor surface: error, timeout,
completion, credit, channel, and stream. The `protocol` field for every
code in this section is `PROTOCOL_AXIS` (4'h1).

### `axis_error_code_t`

**Packet context:** `packet_type = PktTypeError`, `protocol = PROTOCOL_AXIS`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXIS_ERR_PROTOCOL`       | Protocol violation |
| 8'h1      | `AXIS_ERR_READY_TIMING`   | TREADY timing violation |
| 8'h2      | `AXIS_ERR_VALID_TIMING`   | TVALID timing violation |
| 8'h3      | `AXIS_ERR_LAST_MISSING`   | Missing TLAST signal |
| 8'h4      | `AXIS_ERR_LAST_ORPHAN`    | Orphaned TLAST signal |
| 8'h5      | `AXIS_ERR_STRB_INVALID`   | Invalid TSTRB pattern |
| 8'h6      | `AXIS_ERR_KEEP_INVALID`   | Invalid TKEEP pattern |
| 8'h7      | `AXIS_ERR_DATA_ALIGNMENT` | Data alignment error |
| 8'h8      | `AXIS_ERR_ID_VIOLATION`   | TID violation |
| 8'h9      | `AXIS_ERR_DEST_VIOLATION` | TDEST violation |
| 8'hA      | `AXIS_ERR_USER_VIOLATION` | TUSER violation |
| 8'hB–8'hE | _(reserved)_              | _Reserved for future use_ |
| 8'hF      | `AXIS_ERR_USER_DEFINED`   | User-defined error |

### `axis_timeout_code_t`

**Packet context:** `packet_type = PktTypeTimeout`, `protocol = PROTOCOL_AXIS`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXIS_TIMEOUT_HANDSHAKE`    | TVALID/TREADY handshake timeout |
| 8'h1      | `AXIS_TIMEOUT_STREAM`       | Stream completion timeout |
| 8'h2      | `AXIS_TIMEOUT_PACKET`       | Packet timeout (TLAST) |
| 8'h3      | `AXIS_TIMEOUT_BACKPRESSURE` | Backpressure timeout |
| 8'h4      | `AXIS_TIMEOUT_BUFFER`       | Buffer drain timeout |
| 8'h5      | `AXIS_TIMEOUT_STALL`        | Stream stall timeout |
| 8'h6–8'hE | _(reserved)_                | _Reserved for future use_ |
| 8'hF      | `AXIS_TIMEOUT_USER_DEFINED` | User-defined timeout |

### `axis_completion_code_t`

**Packet context:** `packet_type = PktTypeCompletion`, `protocol = PROTOCOL_AXIS`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXIS_COMPL_STREAM_END`   | Stream completed (TLAST) |
| 8'h1      | `AXIS_COMPL_PACKET_SENT`  | Packet sent successfully |
| 8'h2      | `AXIS_COMPL_TRANSFER`     | Data transfer completed |
| 8'h3      | `AXIS_COMPL_BURST_END`    | Burst completed |
| 8'h4      | `AXIS_COMPL_HANDSHAKE`    | Successful handshake |
| 8'h5–8'hE | _(reserved)_              | _Reserved for future use_ |
| 8'hF      | `AXIS_COMPL_USER_DEFINED` | User-defined completion |

### `axis_credit_code_t`

**Packet context:** `packet_type = PktTypeCredit`, `protocol = PROTOCOL_AXIS`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXIS_CREDIT_READY_ASSERT`     | TREADY asserted |
| 8'h1      | `AXIS_CREDIT_READY_DEASSERT`   | TREADY deasserted |
| 8'h2      | `AXIS_CREDIT_BUFFER_AVAILABLE` | Buffer space available |
| 8'h3      | `AXIS_CREDIT_BUFFER_FULL`      | Buffer full |
| 8'h4      | `AXIS_CREDIT_FLOW_CONTROL`     | Flow control event |
| 8'h5      | `AXIS_CREDIT_BACKPRESSURE`     | Backpressure applied |
| 8'h6      | `AXIS_CREDIT_THROUGHPUT`       | Throughput event |
| 8'h7      | `AXIS_CREDIT_EFFICIENCY`       | Transfer efficiency |
| 8'h8–8'hE | _(reserved)_                   | _Reserved for future use_ |
| 8'hF      | `AXIS_CREDIT_USER_DEFINED`     | User-defined credit event |

### `axis_channel_code_t`

**Packet context:** `packet_type = PktTypeChannel`, `protocol = PROTOCOL_AXIS`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXIS_CHAN_CONNECT`       | Channel connected |
| 8'h1      | `AXIS_CHAN_DISCONNECT`    | Channel disconnected |
| 8'h2      | `AXIS_CHAN_STALL`         | Channel stalled |
| 8'h3      | `AXIS_CHAN_RESUME`        | Channel resumed |
| 8'h4      | `AXIS_CHAN_CONGESTION`    | Channel congestion |
| 8'h5      | `AXIS_CHAN_ID_CHANGE`     | TID change detected |
| 8'h6      | `AXIS_CHAN_DEST_CHANGE`   | TDEST change detected |
| 8'h7      | `AXIS_CHAN_CONFIG_CHANGE` | Channel configuration change |
| 8'h8–8'hE | _(reserved)_              | _Reserved for future use_ |
| 8'hF      | `AXIS_CHAN_USER_DEFINED`  | User-defined channel event |

### `axis_stream_code_t`

**Packet context:** `packet_type = PktTypeStream`, `protocol = PROTOCOL_AXIS`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXIS_STREAM_START`        | Stream started |
| 8'h1      | `AXIS_STREAM_END`          | Stream ended (TLAST) |
| 8'h2      | `AXIS_STREAM_PAUSE`        | Stream paused |
| 8'h3      | `AXIS_STREAM_RESUME`       | Stream resumed |
| 8'h4      | `AXIS_STREAM_OVERFLOW`     | Stream buffer overflow |
| 8'h5      | `AXIS_STREAM_UNDERFLOW`    | Stream buffer underflow |
| 8'h6      | `AXIS_STREAM_TRANSFER`     | Active data transfer |
| 8'h7      | `AXIS_STREAM_IDLE`         | Stream idle |
| 8'h8–8'hE | _(reserved)_               | _Reserved for future use_ |
| 8'hF      | `AXIS_STREAM_USER_DEFINED` | User-defined stream event |

---

## Unified Event Code Union

`monitor_amba4_pkg` also exports a `unified_event_code_t` packed union that
overlays every enum in this document onto a single 8-bit field, plus a
`raw` view for direct 8-bit access. Helper functions `create_axi_*_event`,
`create_apb_*_event`, and `create_axis_*_event` (one per enum) construct
the union from a typed enum value — use these from any wrapper that needs
to publish a protocol-tagged event_code without manual bit packing.

---

## Related

- **[`monitor_package_spec.md`](./monitor_package_spec.md)** — Universal types, packet layout, helper functions.
- **[`monitor_amba5_pkg.md`](./monitor_amba5_pkg.md)** — AXI5 / APB5 / AXIS5 extended event codes.
- **[`monitor_arbiter_pkg.md`](./monitor_arbiter_pkg.md)** — ARB and CORE event codes.
- **[`monitor_system_whitepaper.md`](../monitor_system_whitepaper.md)** — Design-surface view of the monitor system.

---

## Navigation

- **[← Back to Includes Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
