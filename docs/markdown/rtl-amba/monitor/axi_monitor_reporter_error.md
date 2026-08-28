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

# AXI Monitor Reporter — Error Cone

**Module:** `axi_monitor_reporter_error.sv`
**Location:** `rtl/amba/monitor/`
**Status:** Production Ready

---

## Overview

The AXI Monitor Reporter Error Cone is the error-packet detection sub-block of `axi_monitor_reporter`. It scans the outstanding-transaction table for unreported transactions in the `TRANS_ERROR` (genuine error, not a timeout) or `TRANS_ORPHANED` state, priority-encodes the first match, and emits the fields for a `PktTypeError` MonBus packet. It was split out of the monolithic reporter so integrators can drop it with `ENABLE_ERROR_LOGIC=0` and pay zero LUT cost for the per-slot scan and priority encoder. The block is purely combinational.

`error` is a **fault class** ([taxonomy](monitor_system_architecture.md#healthy-classes-vs-fault-classes)): in correct operation it never fires. **An error, by definition, hangs the system** — a transaction that returns `SLVERR`/`DECERR` or is never answered does not retire, so exercising this cone means *deliberately injecting a fault* (a slave forced to return a bad response), and the traffic that provoked it is expected to wedge. That is exactly what this cone exists to catch: it emits the `PktTypeError` packet as the hang happens. (For the address-range/allowlist flavor of error injection, which lives in [`axi_monitor_addr_check`](axi_monitor_addr_check.md) (generate-gated by `N_ADDR_RANGES > 0`, so it is built only when ranges are configured) and does *not* require this cone, see that page.)

Key features:

- Scans for unreported `TRANS_ERROR` (non-timeout) and `TRANS_ORPHANED` slots
- Uses `timeout_detected` to keep genuine errors distinct from timeouts (which the timeout cone claims)
- First-match priority encoder selects one slot per cycle
- Emits `PktTypeError` with the slot's own `event_code.raw_code`
- Runtime-gated by `cfg_error_enable`; compile-time removable via the parent's `ENABLE_ERROR_LOGIC`
- Pure combinational — table, `event_reported`, and threshold state stay in the top reporter

The transaction manager marks a slot `TRANS_ERROR` when a transaction returns SLVERR/DECERR or violates protocol, and `TRANS_ORPHANED` when data or a response arrives with no matching command. These must become MonBus error packets exactly once each. This cone performs the detect-and-select half: it finds the error/orphan slots that have not yet been reported, excludes any slot already flagged as a timeout so the timeout cone can own those without aliasing, picks the first match, and hands the packet fields plus the chosen slot index to the top reporter for FIFO push and `event_reported` feedback. Splitting it out lets the wide scan and encoder be compiled away when error reporting is not required.

**Use cases:**

- Emitting SLVERR / DECERR / protocol-violation error packets
- Reporting orphaned data or response beats (no matching command)
- Functional-verification configurations that must catch bus errors

**Key benefit:** isolates the error/orphan scan/encoder for `ENABLE_ERROR_LOGIC=0` compile-out, and cleanly separates genuine errors from timeouts via the `timeout_detected` mask.

---

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| MAX_TRANSACTIONS | int | 16 | Depth of the shared transaction table scanned |
| IDX_W | int | `$clog2(MAX_TRANSACTIONS)` | Width of the selected-slot index |

---

## Ports

### Inputs (shared monitor state)

| Port | Direction | Width | Description |
|---|---|---|---|
| trans_table | Input | bus_transaction_t x MAX_TRANSACTIONS | The outstanding-transaction table |
| event_reported | Input | MAX_TRANSACTIONS | Per-slot "already reported" mask (from the top reporter) |
| timeout_detected | Input | MAX_TRANSACTIONS | Per-slot timeout mask; excludes timeout slots from the error scan |
| cfg_error_enable | Input | 1 | Runtime enable for error reporting |

### Outputs (packet fields to the top reporter)

| Port | Direction | Width | Description |
|---|---|---|---|
| pkt_valid | Output | 1 | An unreported error/orphan slot was found this cycle |
| pkt_type | Output | 4 | Packet type = `PktTypeError` |
| pkt_event_code | Output | 8 | Event code = selected slot's `event_code.raw_code` |
| pkt_channel | Output | 9 | Channel id `{3'b0, slot.channel[5:0]}` |
| pkt_data | Output | 64 | Slot address, zero-padded to 64 bits |
| sel_idx | Output | IDX_W | Index of the selected slot (for `event_reported` feedback) |

---

## Functional Description

### Error / Orphan Scan

For every slot, the slot qualifies as an error event when it is `valid`, its `event_reported` bit is clear, `cfg_error_enable` is set, and **either**:

- `state == TRANS_ERROR` **and** its `timeout_detected` bit is clear (a genuine error, not a timeout), **or**
- `state == TRANS_ORPHANED` (data/response with no matching command).

Qualifying slots collect into `w_events`. Consulting `timeout_detected` is what keeps this cone from aliasing timeouts: a transaction that errored because it timed out is left for the timeout sub-block to report, so the same slot is never emitted twice under two packet types.

### First-Match Selection

A second loop takes the first set bit of `w_events` into `w_sel` and asserts `w_has_event` (with the local `WIDTHTRUNC` lint waiver on the index narrowing). Strict low-index-first priority means exactly one error is emitted per cycle; additional errors are serialized on later cycles as each winner is marked reported upstream.

### Emitted Fields

- `pkt_valid` = `w_has_event`
- `sel_idx` = `w_sel`
- `pkt_type` = `PktTypeError`
- `pkt_event_code` = `trans_table[w_sel].event_code.raw_code` — the specific AXI error code captured by the trans manager (e.g. `AXI_ERR_RESP_SLVERR`, `AXI_ERR_RESP_DECERR`, `AXI_ERR_DATA_ORPHAN`, `AXI_ERR_RESP_ORPHAN`)
- `pkt_channel` = `{3'b0, trans_table[w_sel].channel[5:0]}`
- `pkt_data` = `pad_address(trans_table[w_sel].addr)`

Unlike the completion and debug cones, the error cone forwards the transaction's own captured raw error code rather than a fixed constant, so the packet carries the precise error kind.

### Ownership of State

The block is stateless. The transaction table, the `event_reported` feedback, the `timeout_detected` mask, and the threshold flags all live in the top reporter, which consumes `sel_idx` to set the reported bit after acceptance. Keeping the cone combinational lets it share the table snapshot with the sibling cones each cycle.

---

## Usage Example

```systemverilog
// Instantiated inside axi_monitor_reporter, gated by ENABLE_ERROR_LOGIC.
axi_monitor_reporter_error #(
    .MAX_TRANSACTIONS (MAX_TRANSACTIONS)
) u_error (
    .trans_table      (trans_table),
    .event_reported   (event_reported),
    .timeout_detected (timeout_detected),  // keeps timeouts out of the error scan
    .cfg_error_enable (cfg_error_enable),

    .pkt_valid        (err_valid),
    .pkt_type         (err_type),
    .pkt_event_code   (err_event_code),
    .pkt_channel      (err_channel),
    .pkt_data         (err_data),
    .sel_idx          (err_sel_idx)        // top reporter sets event_reported[err_sel_idx]
);
```

---

## Design Notes

### Timeout De-Aliasing

The `timeout_detected` input is the mechanism that prevents a timed-out transaction (which the trans manager may also mark `TRANS_ERROR`) from being reported by both this cone and the timeout cone. Only errors with a clear timeout bit are claimed here.

### Compile-Out Path

Instantiated under `ENABLE_ERROR_LOGIC` in the parent; setting it to 0 removes the wide scan and encoder for zero LUT cost. `cfg_error_enable` is the runtime mask when the logic is present.

### Raw Event Code Forwarding

Because `pkt_event_code` comes from the slot's `event_code.raw_code`, this cone reports the exact error type (SLVERR, DECERR, orphan variants, protocol errors, ...) rather than a single generic error code.

---

## Related Modules

**Used by:**

- **axi_monitor_reporter.sv** - Top reporter that pushes the packet into the MonBus FIFO and drives `event_reported`

**Uses:**

- **monitor_common_pkg** - `PktTypeError`, `TRANS_ERROR`, `TRANS_ORPHANED`, `bus_transaction_t`
- **monitor_amba4_pkg** - AXI error event codes (via the slot's `event_code`)

**See also:**

- **axi_monitor_reporter_compl.sv** - Completion detection cone (sibling sub-block)
- **axi_monitor_reporter_debug.sv** - State-change debug emitter (sibling sub-block)
- **axi_monitor_base.sv** - The monitor scaffold that houses trans_mgr + reporter

---

## References

### Source Code
- RTL: `rtl/amba/monitor/axi_monitor_reporter_error.sv`

### Documentation
- Packet format: `docs/markdown/rtl-amba/includes/monitor_package_spec.md`
- Monitor base: `docs/markdown/rtl-amba/monitor/axi_monitor_base.md`
- Known issues: `rtl/amba/KNOWN_ISSUES/axi_monitor_reporter.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- **[Back to Shared Infrastructure Index](../_book_monitor_index.md)**
- **[Back to rtl-amba Index](../index.md)**
