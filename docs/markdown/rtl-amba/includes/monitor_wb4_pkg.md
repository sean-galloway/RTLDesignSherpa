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

# Wishbone B4 Event Code Reference

The per-protocol event-code reference for Wishbone B4. The 8-bit
`event_code` field of every monbus packet sourced by
[`wb4_monitor`](../wb4/wb4_monitor.md) takes its value from one of the enums
declared in `rtl/amba/includes/monitor_wb4_pkg.sv` and listed below. For the
universal packet layout, the `protocol` and `packet_type` enums and the
helper functions, see [`monitor_package_spec.md`](./monitor_package_spec.md).

Each event-code enum is 8 bits. Slots `8'h0`–`8'hE` hold predefined codes,
with `_RESERVED_*` placeholders absorbing the unused indices, and slot `8'hF`
is the `*_USER_DEFINED` escape hatch, matching the AMBA4 and AMBA5 packages.

---

## Design Notes

**This is a package, not a module.** No ports, no clock. It declares the
event encodings the Wishbone monitor emits so that each one has exactly one
definition.

**Deliberately NOT re-exported by `monitor_pkg`.** The aggregating wrapper
re-exports the AMBA4, AMBA5 and arbiter packages, but not this one. Only
`wb4_monitor`'s filelist includes it, so adding Wishbone to the monitor
family changed no existing consumer's compile closure. If a future block
needs both, include the package directly rather than widening the
aggregator.

**`PROTOCOL_WB` lives elsewhere.** The protocol id `4'h5` is an additive
entry in `monitor_common_pkg`'s `protocol_type_t`, alongside AXI, AXIS, APB,
ARB and CORE, because the protocol enum is universal. Only the event codes
are Wishbone-specific and live here.

**Address-range violations share APB's code.** `apb_monitor_addr_check` is
reused by `wb4_monitor` through its `PROTOCOL` parameter. The checker emits
event code `8'h08`, which is `APB_ERR_ADDR_RANGE` in the AMBA4 package and
`WB_ERR_ADDR_RANGE` here; the two agree by construction so one checker can
serve both protocols.

**No test of its own, and none expected.** A package has no behaviour to
simulate. It is verified by `wb4_monitor` failing to elaborate if a
declaration is wrong, and by `val/amba/test_wb4_monitor.py` decoding the
codes through `TBClasses.monbus`, whose Python enums mirror this file.

---

### `wb_error_code_t`

**Packet context:** `packet_type = PktTypeError`, `protocol = PROTOCOL_WB`

| Value | Name | Description |
|---|---|---|
| 8'h0      | `WB_ERR_ERR`         | Slave terminated the transfer with `ERR` |
| 8'h1      | `WB_ERR_ORPHAN_RSP`  | A response arrived with no request outstanding |
| 8'h2      | `WB_ERR_TRACK_LOST`  | Request accepted with no free tracking slot; the transfer is untracked and its response will read as an orphan |
| 8'h3–8'h7 | _(reserved)_         | _Reserved for future use_ |
| 8'h8      | `WB_ERR_ADDR_RANGE`  | Address-range violation (from `apb_monitor_addr_check`, tagged `PROTOCOL_WB`) |
| 8'h9–8'hE | _(reserved)_         | _Reserved for future use_ |
| 8'hF      | `WB_ERR_USER_DEFINED`| User-defined error |

### `wb_timeout_code_t`

**Packet context:** `packet_type = PktTypeTimeout`, `protocol = PROTOCOL_WB`

| Value | Name | Description |
|---|---|---|
| 8'h0      | `WB_TIMEOUT_CMD`         | A request sat on `cmd_valid` without `cmd_ready` for `cfg_cmd_timeout_cnt` clocks |
| 8'h1      | `WB_TIMEOUT_RSP`         | The oldest open transfer went unterminated for `cfg_rsp_timeout_cnt` clocks |
| 8'h2–8'hE | _(reserved)_             | _Reserved for future use_ |
| 8'hF      | `WB_TIMEOUT_USER_DEFINED`| User-defined timeout |

Each fires once: the command timeout re-arms when the request is taken or
withdrawn, the response timeout is flagged per queue entry.

### `wb_completion_code_t`

**Packet context:** `packet_type = PktTypeCompletion`, `protocol = PROTOCOL_WB`

| Value | Name | Description |
|---|---|---|
| 8'h0      | `WB_COMPL_ACK`          | Terminated `ACK` (direction in `aux_data`) |
| 8'h1      | `WB_COMPL_READ`         | Read terminated `ACK` |
| 8'h2      | `WB_COMPL_WRITE`        | Write terminated `ACK` |
| 8'h3      | `WB_COMPL_RTY`          | Terminated `RTY`. A completion, not an error: the FUB decides whether to retry |
| 8'h4–8'hE | _(reserved)_            | _Reserved for future use_ |
| 8'hF      | `WB_COMPL_USER_DEFINED` | User-defined completion |

`RTY` sits here rather than in the error enum on purpose. A retry is the
slave asking for the transfer again, not a failure, and
[`wb4_retry`](../wb4/wb4_retry.md) may absorb it before the FUB ever sees it.

### `wb_perf_code_t`

**Packet context:** `packet_type = PktTypePerf`, `protocol = PROTOCOL_WB`

| Value | Name | Description |
|---|---|---|
| 8'h0      | `WB_PERF_READ_LATENCY`  | A read's latency crossed `cfg_latency_threshold` |
| 8'h1      | `WB_PERF_WRITE_LATENCY` | A write's latency crossed `cfg_latency_threshold` |
| 8'h2–8'hE | _(reserved)_            | _Reserved for future use_ |
| 8'hF      | `WB_PERF_USER_DEFINED`  | User-defined performance event |

### `wb_debug_code_t`

**Packet context:** `packet_type = PktTypeDebug`, `protocol = PROTOCOL_WB`

| Value | Name | Description |
|---|---|---|
| 8'h0      | `WB_DEBUG_QUEUE_ACTIVE` | The tracking queue went from empty to non-empty |
| 8'h1      | `WB_DEBUG_QUEUE_IDLE`   | The tracking queue drained |
| 8'h2–8'hE | _(reserved)_            | _Reserved for future use_ |
| 8'hF      | `WB_DEBUG_USER_DEFINED` | User-defined debug event |

---

## Related

- [`wb4_monitor`](../wb4/wb4_monitor.md) - the only module that imports this package
- [`monitor_package_spec.md`](./monitor_package_spec.md) - packet layout and the `protocol` enum, including `PROTOCOL_WB` (`4'h5`)
- [`monitor_amba4_pkg.md`](./monitor_amba4_pkg.md) - the AMBA4 equivalent, whose `8'h08` address-range code this package matches
