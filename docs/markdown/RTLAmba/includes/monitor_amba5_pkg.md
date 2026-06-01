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

# AMBA5 Extended Event Code Reference

This is the per-protocol event-code reference for the AMBA5 family — AXI5,
APB5, and AXIS5. The enums here **extend** the AMBA4 set with the new
event categories introduced by the AMBA5 specifications: atomic operations
and tracing on AXI5; wake-up signaling, parity, and user signals on APB5;
wake-up, parity, and CRC on AXIS5. For the AMBA4 baseline see
[`monitor_amba4_pkg.md`](./monitor_amba4_pkg.md); for the universal packet
layout and helper functions see
[`monitor_package_spec.md`](./monitor_package_spec.md).

Source: `rtl/amba/includes/monitor_amba5_pkg.sv`. Each enum is 8 bits
wide; slot `8'hF` is the `*_USER_DEFINED` escape hatch. AMBA5 codes reuse
the AMBA4 `protocol` values (`PROTOCOL_AXI` / `PROTOCOL_APB` /
`PROTOCOL_AXIS`); the distinguishing field is the chosen `event_code`
enum and the `packet_type` context the producer uses.

---

## AXI5 Extended Event Codes

Two new categories on top of the AXI4 baseline: atomic-operation events and
QoS / trace events.

### `axi5_atomic_code_t`

**Packet context:** extends `axi_completion_code_t` semantics (`packet_type = PktTypeCompletion`, `protocol = PROTOCOL_AXI`) — used to report which AXI5 atomic primitive completed.

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXI5_ATOMIC_LOAD`         | Atomic load operation |
| 8'h1      | `AXI5_ATOMIC_SWAP`         | Atomic swap operation |
| 8'h2      | `AXI5_ATOMIC_COMPARE`      | Atomic compare operation |
| 8'h3      | `AXI5_ATOMIC_ADD`          | Atomic add operation |
| 8'h4      | `AXI5_ATOMIC_CLR`          | Atomic clear operation |
| 8'h5      | `AXI5_ATOMIC_XOR`          | Atomic XOR operation |
| 8'h6      | `AXI5_ATOMIC_SET`          | Atomic set operation |
| 8'h7      | `AXI5_ATOMIC_SMAX`         | Atomic signed max |
| 8'h8      | `AXI5_ATOMIC_SMIN`         | Atomic signed min |
| 8'h9      | `AXI5_ATOMIC_UMAX`         | Atomic unsigned max |
| 8'hA      | `AXI5_ATOMIC_UMIN`         | Atomic unsigned min |
| 8'hB–8'hE | _(reserved)_               | _Reserved for future use_ |
| 8'hF      | `AXI5_ATOMIC_USER_DEFINED` | User-defined atomic |

### `axi5_trace_code_t`

**Packet context:** `packet_type = PktTypeDebug` (trace / QoS / poison / MPAM events), `protocol = PROTOCOL_AXI`.

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXI5_TRACE_START`      | Trace session start |
| 8'h1      | `AXI5_TRACE_END`        | Trace session end |
| 8'h2      | `AXI5_TRACE_DATA`       | Trace data packet |
| 8'h3      | `AXI5_QOS_ESCALATION`   | QoS level escalation |
| 8'h4      | `AXI5_QOS_DEESCALATION` | QoS level de-escalation |
| 8'h5      | `AXI5_POISON_DETECTED`  | Poison bit detected |
| 8'h6      | `AXI5_LOOP_DETECTED`    | Loop detection triggered |
| 8'h7      | `AXI5_MPAM_EVENT`       | MPAM partition event |
| 8'h8–8'hE | _(reserved)_            | _Reserved for future use_ |
| 8'hF      | `AXI5_USER_DEFINED`     | User-defined |

---

## APB5 Extended Event Codes

Three new categories on top of the APB4 baseline: wake-up signaling
(PWAKEUP), parity (PPARITY / PRDATAPARITY / PREADYPARITY / PSLVERRPARITY),
and user signals (PUSER / PSUSER).

### `apb5_wakeup_code_t`

**Packet context:** `packet_type = PktTypeDebug` (or producer-defined), `protocol = PROTOCOL_APB` — APB5 wake-up / sleep transitions.

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `APB5_WAKEUP_REQUEST`      | PWAKEUP asserted by slave |
| 8'h1      | `APB5_WAKEUP_ACKNOWLEDGED` | Wake-up acknowledged |
| 8'h2      | `APB5_WAKEUP_TIMEOUT`      | Wake-up request timeout |
| 8'h3      | `APB5_WAKEUP_REJECTED`     | Wake-up request rejected |
| 8'h4      | `APB5_SLEEP_REQUEST`       | Sleep mode request |
| 8'h5      | `APB5_SLEEP_ENTERED`       | Entered sleep mode |
| 8'h6–8'hE | _(reserved)_               | _Reserved for future use_ |
| 8'hF      | `APB5_WAKEUP_USER_DEFINED` | User-defined wake-up |

### `apb5_parity_code_t`

**Packet context:** `packet_type = PktTypeError` (parity errors) or `PktTypeDebug` (status), `protocol = PROTOCOL_APB`.

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `APB5_PARITY_PWDATA_ERROR`   | PWDATA parity error (PPARITY) |
| 8'h1      | `APB5_PARITY_PRDATA_ERROR`   | PRDATA parity error (PRDATAPARITY) |
| 8'h2      | `APB5_PARITY_PREADY_ERROR`   | PREADY parity error (PREADYPARITY) |
| 8'h3      | `APB5_PARITY_PSLVERR_ERROR`  | PSLVERR parity error (PSLVERRPARITY) |
| 8'h4      | `APB5_PARITY_CORRECTED`      | Parity error corrected |
| 8'h5      | `APB5_PARITY_UNCORRECTED`    | Parity error uncorrectable |
| 8'h6      | `APB5_PARITY_CHECK_DISABLED` | Parity checking disabled |
| 8'h7      | `APB5_PARITY_CHECK_ENABLED`  | Parity checking enabled |
| 8'h8–8'hE | _(reserved)_                 | _Reserved for future use_ |
| 8'hF      | `APB5_PARITY_USER_DEFINED`   | User-defined parity |

### `apb5_user_code_t`

**Packet context:** `packet_type = PktTypeDebug`, `protocol = PROTOCOL_APB` — APB5 PUSER / PSUSER side-band signal events.

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `APB5_USER_PUSER_VALID`     | PUSER valid on master |
| 8'h1      | `APB5_USER_PSUSER_VALID`    | PSUSER valid on slave |
| 8'h2      | `APB5_USER_SIGNAL_MISMATCH` | User signal mismatch |
| 8'h3–8'hE | _(reserved)_                | _Reserved for future use_ |
| 8'hF      | `APB5_USER_USER_DEFINED`    | User-defined |

---

## AXIS5 Extended Event Codes

Three new categories on top of the AXIS4 baseline: wake-up (TWAKEUP),
parity (TPARITY), and CRC (TCRC_ERROR).

### `axis5_wakeup_code_t`

**Packet context:** `packet_type = PktTypeDebug` (or producer-defined), `protocol = PROTOCOL_AXIS` — AXIS5 wake-up / sleep transitions.

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXIS5_WAKEUP_REQUEST`      | TWAKEUP asserted |
| 8'h1      | `AXIS5_WAKEUP_ACKNOWLEDGED` | Wake-up acknowledged |
| 8'h2      | `AXIS5_WAKEUP_TIMEOUT`      | Wake-up timeout |
| 8'h3      | `AXIS5_WAKEUP_ACTIVE`       | Wake-up active, data pending |
| 8'h4      | `AXIS5_SLEEP_ENTERING`      | Entering sleep mode |
| 8'h5      | `AXIS5_SLEEP_EXITING`       | Exiting sleep mode |
| 8'h6–8'hE | _(reserved)_                | _Reserved for future use_ |
| 8'hF      | `AXIS5_WAKEUP_USER_DEFINED` | User-defined wake-up |

### `axis5_parity_code_t`

**Packet context:** `packet_type = PktTypeError` (parity errors) or `PktTypeDebug` (status), `protocol = PROTOCOL_AXIS`.

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXIS5_PARITY_TDATA_ERROR`    | TDATA parity error (TPARITY) |
| 8'h1      | `AXIS5_PARITY_CORRECTED`      | Parity error corrected |
| 8'h2      | `AXIS5_PARITY_UNCORRECTED`    | Parity error uncorrectable |
| 8'h3      | `AXIS5_PARITY_CHECK_DISABLED` | Parity checking disabled |
| 8'h4      | `AXIS5_PARITY_CHECK_ENABLED`  | Parity checking enabled |
| 8'h5–8'hE | _(reserved)_                  | _Reserved for future use_ |
| 8'hF      | `AXIS5_PARITY_USER_DEFINED`   | User-defined parity |

### `axis5_crc_code_t`

**Packet context:** `packet_type = PktTypeError` (CRC failures) or `PktTypeDebug` (status), `protocol = PROTOCOL_AXIS` — optional CRC feature in AXIS5.

| Value | Name | Description |
|---:|------|-------------|
| 8'h0      | `AXIS5_CRC_VALID`        | CRC check passed |
| 8'h1      | `AXIS5_CRC_ERROR`        | CRC error detected (TCRC_ERROR) |
| 8'h2      | `AXIS5_CRC_COMPUTED`     | CRC computed and sent |
| 8'h3      | `AXIS5_CRC_DISABLED`     | CRC checking disabled |
| 8'h4      | `AXIS5_CRC_ENABLED`      | CRC checking enabled |
| 8'h5–8'hE | _(reserved)_             | _Reserved for future use_ |
| 8'hF      | `AXIS5_CRC_USER_DEFINED` | User-defined CRC |

---

## Unified Event Code Union

`monitor_amba5_pkg` exports an `amba5_event_code_t` packed union that
overlays the eight AMBA5 enums above (plus a `raw` 8-bit view) onto a
single field. Helper functions `create_axi5_atomic_event`,
`create_axi5_trace_event`, `create_apb5_wakeup_event`,
`create_apb5_parity_event`, `create_apb5_user_event`,
`create_axis5_wakeup_event`, `create_axis5_parity_event`, and
`create_axis5_crc_event` construct the union from a typed enum value.

---

## Related

- **[`monitor_package_spec.md`](./monitor_package_spec.md)** — Universal types, packet layout, helper functions.
- **[`monitor_amba4_pkg.md`](./monitor_amba4_pkg.md)** — AXI4 / APB4 / AXIS4 baseline event codes.
- **[`monitor_arbiter_pkg.md`](./monitor_arbiter_pkg.md)** — ARB and CORE event codes.
- **[`monitor_system_whitepaper.md`](../monitor_system_whitepaper.md)** — Design-surface view of the monitor system.

---

## Navigation

- **[← Back to Includes Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
