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

# ARB and CORE Event Code Reference

This is the per-protocol event-code reference for the two non-AMBA monbus
protocols: **ARB** (arbiter monitoring — fairness, starvation, weighted
round-robin, ACK protocol) and **CORE** (internal accelerator / DMA-engine
monitoring — descriptor fetch, credit cycles, sub-engine state). Both
sets follow the same packet layout as the AMBA monitors; only the
`protocol` and `event_code` fields differ. For the universal packet
layout and helper functions see
[`monitor_package_spec.md`](./monitor_package_spec.md).

Source: `rtl/amba/includes/monitor_arbiter_pkg.sv`. Each enum is 8 bits
wide; slot `8'hF` is the `*_USER_DEFINED` escape hatch. ARB codes carry
`PROTOCOL_ARB` (4'h3); CORE codes carry `PROTOCOL_CORE` (4'h4).

---

## ARB Event Codes

Six categories cover the arbiter monitor surface: error, timeout,
completion, threshold, performance, and debug. The `protocol` field for
every code in this section is `PROTOCOL_ARB` (4'h3).

### `arb_error_code_t`

**Packet context:** `packet_type = PktTypeError`, `protocol = PROTOCOL_ARB`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `ARB_ERR_STARVATION`         | Client request starvation |
| 8'h1      | `ARB_ERR_ACK_TIMEOUT`        | Grant ACK timeout |
| 8'h2      | `ARB_ERR_PROTOCOL_VIOLATION` | ACK protocol violation |
| 8'h3      | `ARB_ERR_CREDIT_VIOLATION`   | Credit system violation |
| 8'h4      | `ARB_ERR_FAIRNESS_VIOLATION` | Weighted fairness violation |
| 8'h5      | `ARB_ERR_WEIGHT_UNDERFLOW`   | Weight credit underflow |
| 8'h6      | `ARB_ERR_CONCURRENT_GRANTS`  | Multiple simultaneous grants |
| 8'h7      | `ARB_ERR_INVALID_GRANT_ID`   | Invalid grant ID detected |
| 8'h8      | `ARB_ERR_ORPHAN_ACK`         | ACK without pending grant |
| 8'h9      | `ARB_ERR_GRANT_OVERLAP`      | Overlapping grant periods |
| 8'hA      | `ARB_ERR_MASK_ERROR`         | Round-robin mask error |
| 8'hB      | `ARB_ERR_STATE_MACHINE`      | FSM state error |
| 8'hC      | `ARB_ERR_CONFIGURATION`      | Invalid configuration |
| 8'hD–8'hE | _(reserved)_                 | _Reserved for future use_ |
| 8'hF      | `ARB_ERR_USER_DEFINED`       | User-defined error |

### `arb_timeout_code_t`

**Packet context:** `packet_type = PktTypeTimeout`, `protocol = PROTOCOL_ARB`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `ARB_TIMEOUT_GRANT_ACK`     | Grant ACK timeout |
| 8'h1      | `ARB_TIMEOUT_REQUEST_HOLD`  | Request held too long |
| 8'h2      | `ARB_TIMEOUT_WEIGHT_UPDATE` | Weight update timeout |
| 8'h3      | `ARB_TIMEOUT_BLOCK_RELEASE` | Block release timeout |
| 8'h4      | `ARB_TIMEOUT_CREDIT_UPDATE` | Credit update timeout |
| 8'h5      | `ARB_TIMEOUT_STATE_CHANGE`  | State machine timeout |
| 8'h6–8'hE | _(reserved)_                | _Reserved for future use_ |
| 8'hF      | `ARB_TIMEOUT_USER_DEFINED`  | User-defined timeout |

### `arb_completion_code_t`

**Packet context:** `packet_type = PktTypeCompletion`, `protocol = PROTOCOL_ARB`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `ARB_COMPL_GRANT_ISSUED`    | Grant successfully issued |
| 8'h1      | `ARB_COMPL_ACK_RECEIVED`    | ACK successfully received |
| 8'h2      | `ARB_COMPL_TRANSACTION`     | Complete transaction (grant+ack) |
| 8'h3      | `ARB_COMPL_WEIGHT_UPDATE`   | Weight update completed |
| 8'h4      | `ARB_COMPL_CREDIT_CYCLE`    | Credit cycle completed |
| 8'h5      | `ARB_COMPL_FAIRNESS_PERIOD` | Fairness analysis period |
| 8'h6      | `ARB_COMPL_BLOCK_PERIOD`    | Block period completed |
| 8'h7–8'hE | _(reserved)_                | _Reserved for future use_ |
| 8'hF      | `ARB_COMPL_USER_DEFINED`    | User-defined completion |

### `arb_threshold_code_t`

**Packet context:** `packet_type = PktTypeThreshold`, `protocol = PROTOCOL_ARB`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `ARB_THRESH_REQUEST_LATENCY`  | Request-to-grant latency threshold |
| 8'h1      | `ARB_THRESH_ACK_LATENCY`      | Grant-to-ACK latency threshold |
| 8'h2      | `ARB_THRESH_FAIRNESS_DEV`     | Fairness deviation threshold |
| 8'h3      | `ARB_THRESH_ACTIVE_REQUESTS`  | Active request count threshold |
| 8'h4      | `ARB_THRESH_GRANT_RATE`       | Grant rate threshold |
| 8'h5      | `ARB_THRESH_EFFICIENCY`       | Grant efficiency threshold |
| 8'h6      | `ARB_THRESH_CREDIT_LOW`       | Low credit threshold |
| 8'h7      | `ARB_THRESH_WEIGHT_IMBALANCE` | Weight imbalance threshold |
| 8'h8      | `ARB_THRESH_STARVATION_TIME`  | Starvation time threshold |
| 8'h9–8'hE | _(reserved)_                  | _Reserved for future use_ |
| 8'hF      | `ARB_THRESH_USER_DEFINED`     | User-defined threshold |

### `arb_performance_code_t`

**Packet context:** `packet_type = PktTypePerf`, `protocol = PROTOCOL_ARB`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `ARB_PERF_GRANT_ISSUED`       | Grant issued event |
| 8'h1      | `ARB_PERF_ACK_RECEIVED`       | ACK received event |
| 8'h2      | `ARB_PERF_GRANT_EFFICIENCY`   | Grant completion efficiency |
| 8'h3      | `ARB_PERF_FAIRNESS_METRIC`    | Fairness compliance metric |
| 8'h4      | `ARB_PERF_THROUGHPUT`         | Arbitration throughput |
| 8'h5      | `ARB_PERF_LATENCY_AVG`        | Average latency measurement |
| 8'h6      | `ARB_PERF_WEIGHT_COMPLIANCE`  | Weight compliance metric |
| 8'h7      | `ARB_PERF_CREDIT_UTILIZATION` | Credit utilization efficiency |
| 8'h8      | `ARB_PERF_CLIENT_ACTIVITY`    | Per-client activity metric |
| 8'h9      | `ARB_PERF_STARVATION_COUNT`   | Starvation event count |
| 8'hA      | `ARB_PERF_BLOCK_EFFICIENCY`   | Block/unblock efficiency |
| 8'hB–8'hE | _(reserved)_                  | _Reserved for future use_ |
| 8'hF      | `ARB_PERF_USER_DEFINED`       | User-defined performance |

### `arb_debug_code_t`

**Packet context:** `packet_type = PktTypeDebug`, `protocol = PROTOCOL_ARB`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `ARB_DEBUG_STATE_CHANGE`     | Arbiter state machine change |
| 8'h1      | `ARB_DEBUG_MASK_UPDATE`      | Round-robin mask update |
| 8'h2      | `ARB_DEBUG_WEIGHT_CHANGE`    | Weight configuration change |
| 8'h3      | `ARB_DEBUG_CREDIT_UPDATE`    | Credit level update |
| 8'h4      | `ARB_DEBUG_CLIENT_MASK`      | Client enable/disable mask |
| 8'h5      | `ARB_DEBUG_PRIORITY_CHANGE`  | Priority level change |
| 8'h6      | `ARB_DEBUG_BLOCK_EVENT`      | Block/unblock event |
| 8'h7      | `ARB_DEBUG_QUEUE_STATUS`     | Request queue status |
| 8'h8      | `ARB_DEBUG_COUNTER_SNAPSHOT` | Counter values snapshot |
| 8'h9      | `ARB_DEBUG_FIFO_STATUS`      | FIFO status change |
| 8'hA      | `ARB_DEBUG_FAIRNESS_STATE`   | Fairness tracking state |
| 8'hB      | `ARB_DEBUG_ACK_STATE`        | ACK protocol state |
| 8'hC–8'hE | _(reserved)_                 | _Reserved for future use_ |
| 8'hF      | `ARB_DEBUG_USER_DEFINED`     | User-defined debug |

---

## CORE Event Codes

Six categories cover the core/accelerator monitor surface: error, timeout,
completion, threshold, performance, and debug. The `protocol` field for
every code in this section is `PROTOCOL_CORE` (4'h4). These codes are
used by custom DMA / accelerator subsystems (descriptor engines, control
read/write engines, credit-based flow control).

### `core_error_code_t`

**Packet context:** `packet_type = PktTypeError`, `protocol = PROTOCOL_CORE`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0 | `CORE_ERR_DESCRIPTOR_MALFORMED` | Missing magic number (0x900dc0de) |
| 8'h1 | `CORE_ERR_DESCRIPTOR_BAD_ADDR`  | Invalid descriptor address |
| 8'h2 | `CORE_ERR_DATA_BAD_ADDR`        | Invalid data address (fetch or runtime) |
| 8'h3 | `CORE_ERR_FLAG_COMPARISON`      | Flag mask/compare mismatch |
| 8'h4 | `CORE_ERR_CREDIT_UNDERFLOW`     | Credit system violation |
| 8'h5 | `CORE_ERR_STATE_MACHINE`        | Invalid FSM state transition |
| 8'h6 | `CORE_ERR_DESCRIPTOR_ENGINE`    | Descriptor engine FSM error |
| 8'h7 | `CORE_ERR_FLAG_ENGINE`          | Flag engine FSM error (legacy — pre-ctrlrd) |
| 8'h8 | `CORE_ERR_CTRLWR_ENGINE`        | Control write engine FSM error |
| 8'h9 | `CORE_ERR_DATA_ENGINE`          | Data engine error |
| 8'hA | `CORE_ERR_CHANNEL_INVALID`      | Invalid channel ID |
| 8'hB | `CORE_ERR_CONTROL_VIOLATION`    | Control register violation |
| 8'hC | `CORE_ERR_OVERFLOW`             | Overflow |
| 8'hD | `CORE_ERR_CTRLRD_MAX_RETRIES`   | Control read max retries exceeded |
| 8'hE | `CORE_ERR_CTRLRD_ENGINE`        | Control read engine FSM error |
| 8'hF | `CORE_ERR_USER_DEFINED`         | User-defined error |

### `core_timeout_code_t`

**Packet context:** `packet_type = PktTypeTimeout`, `protocol = PROTOCOL_CORE`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `CORE_TIMEOUT_DESCRIPTOR_FETCH` | Descriptor fetch timeout |
| 8'h1      | `CORE_TIMEOUT_CTRLRD_RETRY`     | Control read retry timeout |
| 8'h2      | `CORE_TIMEOUT_CTRLWR_WRITE`     | Control write timeout |
| 8'h3      | `CORE_TIMEOUT_DATA_TRANSFER`    | Data transfer timeout |
| 8'h4      | `CORE_TIMEOUT_CREDIT_WAIT`      | Credit wait timeout |
| 8'h5      | `CORE_TIMEOUT_CONTROL_WAIT`     | Control enable wait timeout |
| 8'h6      | `CORE_TIMEOUT_ENGINE_RESPONSE`  | Sub-engine response timeout |
| 8'h7      | `CORE_TIMEOUT_STATE_TRANSITION` | FSM state transition timeout |
| 8'h8–8'hE | _(reserved)_                    | _Reserved for future use_ |
| 8'hF      | `CORE_TIMEOUT_USER_DEFINED`     | User-defined timeout |

### `core_completion_code_t`

**Packet context:** `packet_type = PktTypeCompletion`, `protocol = PROTOCOL_CORE`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `CORE_COMPL_DESCRIPTOR_LOADED` | Descriptor successfully loaded |
| 8'h1      | `CORE_COMPL_DESCRIPTOR_CHAIN`  | Descriptor chain completed |
| 8'h2      | `CORE_COMPL_CTRLRD_COMPLETED`  | Control read completed (with match) |
| 8'h3      | `CORE_COMPL_CTRLWR_COMPLETED`  | Control write completed |
| 8'h4      | `CORE_COMPL_DATA_TRANSFER`     | Data transfer completed |
| 8'h5      | `CORE_COMPL_CREDIT_CYCLE`      | Credit cycle completed |
| 8'h6      | `CORE_COMPL_CHANNEL_COMPLETE`  | Channel processing complete |
| 8'h7      | `CORE_COMPL_ENGINE_READY`      | Sub-engine ready |
| 8'h8–8'hE | _(reserved)_                   | _Reserved for future use_ |
| 8'hF      | `CORE_COMPL_USER_DEFINED`      | User-defined completion |

### `core_threshold_code_t`

**Packet context:** `packet_type = PktTypeThreshold`, `protocol = PROTOCOL_CORE`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `CORE_THRESH_DESCRIPTOR_QUEUE` | Descriptor queue depth threshold |
| 8'h1      | `CORE_THRESH_CREDIT_LOW`       | Credit low threshold |
| 8'h2      | `CORE_THRESH_FLAG_RETRY_COUNT` | Flag retry count threshold |
| 8'h3      | `CORE_THRESH_LATENCY`          | Processing latency threshold |
| 8'h4      | `CORE_THRESH_ERROR_RATE`       | Error rate threshold |
| 8'h5      | `CORE_THRESH_THROUGHPUT`       | Throughput threshold |
| 8'h6      | `CORE_THRESH_ACTIVE_CHANNELS`  | Active channel count threshold |
| 8'h7      | `CORE_THRESH_PROGRAM_LATENCY`  | Program write latency threshold |
| 8'h8      | `CORE_THRESH_DATA_RATE`        | Data transfer rate threshold |
| 8'h9–8'hE | _(reserved)_                   | _Reserved for future use_ |
| 8'hF      | `CORE_THRESH_USER_DEFINED`     | User-defined threshold |

### `core_performance_code_t`

**Packet context:** `packet_type = PktTypePerf`, `protocol = PROTOCOL_CORE`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `CORE_PERF_END_OF_DATA`        | Stream continuation signal |
| 8'h1      | `CORE_PERF_END_OF_STREAM`      | Stream termination signal |
| 8'h2      | `CORE_PERF_ENTERING_IDLE`      | FSM returning to idle |
| 8'h3      | `CORE_PERF_CREDIT_INCREMENTED` | Credit added by software |
| 8'h4      | `CORE_PERF_CREDIT_EXHAUSTED`   | Credit blocking execution |
| 8'h5      | `CORE_PERF_STATE_TRANSITION`   | FSM state change |
| 8'h6      | `CORE_PERF_DESCRIPTOR_ACTIVE`  | Data processing started |
| 8'h7      | `CORE_PERF_CTRLRD_RETRY`       | Control read retry attempt |
| 8'h8      | `CORE_PERF_CHANNEL_ENABLE`     | Channel enabled by software |
| 8'h9      | `CORE_PERF_CHANNEL_DISABLE`    | Channel disabled by software |
| 8'hA      | `CORE_PERF_CREDIT_UTILIZATION` | Credit utilization metric |
| 8'hB      | `CORE_PERF_PROCESSING_LATENCY` | Total processing latency |
| 8'hC      | `CORE_PERF_QUEUE_DEPTH`        | Current queue depth |
| 8'hD–8'hE | _(reserved)_                   | _Reserved for future use_ |
| 8'hF      | `CORE_PERF_USER_DEFINED`       | User-defined performance |

### `core_debug_code_t`

**Packet context:** `packet_type = PktTypeDebug`, `protocol = PROTOCOL_CORE`

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `CORE_DEBUG_FSM_STATE_CHANGE`    | Descriptor FSM state change |
| 8'h1      | `CORE_DEBUG_DESCRIPTOR_CONTENT`  | Descriptor content trace |
| 8'h2      | `CORE_DEBUG_CTRLRD_ENGINE_STATE` | Control read engine state trace |
| 8'h3      | `CORE_DEBUG_CTRLWR_ENGINE_STATE` | Control write engine state trace |
| 8'h4      | `CORE_DEBUG_CREDIT_OPERATION`    | Credit system operation |
| 8'h5      | `CORE_DEBUG_CONTROL_REGISTER`    | Control register access |
| 8'h6      | `CORE_DEBUG_ENGINE_HANDSHAKE`    | Engine handshake trace |
| 8'h7      | `CORE_DEBUG_QUEUE_STATUS`        | Queue status change |
| 8'h8      | `CORE_DEBUG_COUNTER_SNAPSHOT`    | Counter values snapshot |
| 8'h9      | `CORE_DEBUG_ADDRESS_TRACE`       | Address progression trace |
| 8'hA      | `CORE_DEBUG_PAYLOAD_TRACE`       | Payload content trace |
| 8'hB–8'hE | _(reserved)_                     | _Reserved for future use_ |
| 8'hF      | `CORE_DEBUG_USER_DEFINED`        | User-defined debug |

---

## Unified Event Code Union (`arb_core_event_code_t`)

`monitor_arbiter_pkg` exports a single `arb_core_event_code_t` packed
union that overlays all twelve enums (six ARB + six CORE) plus a `raw`
8-bit view onto a single field. Use this when a wrapper carries event
codes from either protocol on a shared bus — the `protocol` field of the
monbus packet disambiguates which enum interpretation applies.

```systemverilog
typedef union packed {
    arb_error_code_t        arb_error;
    arb_timeout_code_t      arb_timeout;
    arb_completion_code_t   arb_completion;
    arb_threshold_code_t    arb_threshold;
    arb_performance_code_t  arb_performance;
    arb_debug_code_t        arb_debug;

    core_error_code_t       core_error;
    core_timeout_code_t     core_timeout;
    core_completion_code_t  core_completion;
    core_threshold_code_t   core_threshold;
    core_performance_code_t core_performance;
    core_debug_code_t       core_debug;

    logic [7:0]             raw;
} arb_core_event_code_t;
```

Helper constructors `create_arb_error_event`, `create_arb_timeout_event`,
`create_arb_completion_event`, `create_arb_threshold_event`,
`create_arb_performance_event`, and `create_arb_debug_event` build the
union from a typed ARB enum value. (Equivalent CORE constructors are not
exported by the package — code producing CORE codes assigns the union
field directly.)

---

## Related

- **[`monitor_package_spec.md`](./monitor_package_spec.md)** — Universal types, packet layout, helper functions.
- **[`monitor_amba4_pkg.md`](./monitor_amba4_pkg.md)** — AXI4 / APB4 / AXIS4 event codes.
- **[`monitor_amba5_pkg.md`](./monitor_amba5_pkg.md)** — AXI5 / APB5 / AXIS5 extended event codes.
- **[`monitor_system_whitepaper.md`](../monitor_system_whitepaper.md)** — Design-surface view of the monitor system.

---

## Navigation

- **[← Back to Includes Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
