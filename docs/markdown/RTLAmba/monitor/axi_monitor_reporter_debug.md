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

# AXI Monitor Reporter — Debug State-Change Emitter

**Module:** `axi_monitor_reporter_debug.sv`
**Location:** `rtl/amba/monitor/`
**Status:** Production Ready

---

## Overview

The AXI Monitor Reporter Debug Emitter is the state-change (trace) sub-block of `axi_monitor_reporter` — the sixth cone alongside error, timeout, completion, threshold, and perf. It gives integrators (and the compression-analysis flow) a packet stream that mirrors the live transaction-table FSM: one `PktTypeDebug` packet per (slot, state-change) event. It holds a per-slot previous-state vector, compares it against the live state each cycle, priority-encodes the first slot that transitioned, and emits a packet carrying that slot's address plus the `(prev_state, new_state)` tuple. Unlike the combinational completion/error cones, this block is sequential (it flops the previous state).

### Key Features

- One `PktTypeDebug` packet per per-slot state transition, mirroring the trans_table FSM
- Per-slot 3-bit `prev_state` vector, `MAX_TRANSACTIONS` deep, flopped every cycle
- First-match priority encoder selects one changed slot per cycle
- Packs `(prev_state, new_state)` in the high bits of the 64-bit data field, address in the low bits
- Direct-inject path with an `output_busy` gate (bypasses the FIFO, like threshold/perf)
- Runtime-gated by `cfg_debug_enable`; compile-time removable via the parent's `ENABLE_DEBUG_LOGIC`

---

## Module Purpose

Deep debugging and compression research both benefit from a packet stream that reflects the internal monitor FSM rather than just terminal events. This block produces exactly that: whenever any transaction slot changes state, it emits a debug packet naming the slot's address and the state edge it took. Slot-free transitions are handled cleanly — when a slot is freed, its `prev_state` resets to `TRANS_IDLE` so the next allocation produces a fresh `IDLE → ADDR_PHASE` edge rather than a spurious `IDLE → IDLE`. The compression analysis can use either the state tuple or the address as its dictionary key, whichever carries more entropy.

**Use Cases:**
- FSM-level trace of the transaction table for deep debugging
- Feeding the MonBus compression-analysis flow with a rich event stream
- Correlating state transitions with observed protocol behavior during bring-up

**Key Benefit:** Surfaces the live per-slot FSM as MonBus packets, giving debuggers and the compressor a per-transition trace that terminal-event cones cannot provide.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| MAX_TRANSACTIONS | int | 16 | Depth of the transaction table monitored |
| IDX_W | int | `$clog2(MAX_TRANSACTIONS)` | Width of the internal selected-slot index |

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | Clock |
| aresetn | input | 1 | Active-low asynchronous reset |

### Inputs (shared monitor state)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| trans_table | input | bus_transaction_t × MAX_TRANSACTIONS | The outstanding-transaction table |
| cfg_debug_enable | input | 1 | Runtime enable / mask for debug packet emission |

### Direct-Inject Handshake

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| output_busy | input | 1 | High when the shared MonBus output is occupied; gates `pkt_valid` |
| pkt_taken | input | 1 | Pulsed when this block's packet is accepted (currently unused — see Design Notes) |

### Outputs (packet fields)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| pkt_valid | output | 1 | A state change was found and the output bus is free |
| pkt_type | output | 4 | Packet type = `PktTypeDebug` |
| pkt_event_code | output | 8 | Event code = `AXI_DEBUG_STATE_CHANGE` |
| pkt_channel | output | 9 | Channel id `{3'b0, slot.channel[5:0]}` |
| pkt_data | output | 64 | `{prev_state[2:0], new_state[2:0], 26'h0, addr[31:0]}` |

---

## Functional Description

### Change Detection

When `cfg_debug_enable` is set, the block scans every slot: a slot is flagged changed when it is `valid` and its live `state` differs from the captured `r_prev_state[idx]`. All changed slots collect into `w_changed`, and a first-match priority encoder selects the lowest-index changed slot into `w_sel` (asserting `w_has_event`). When `cfg_debug_enable` is low, no slot is flagged, so no packets are produced.

### Previous-State Flop

Each cycle `r_prev_state[idx]` snapshots the slot's live state — **except** when the slot is not valid, in which case it resets to `TRANS_IDLE`. This is the mechanism that makes freed slots behave: an emptied slot returns to IDLE, so its next allocation registers as a real `IDLE → ADDR_PHASE` transition rather than an aliased `IDLE → IDLE` non-event.

### Packet Assembly

When a change is found and the output bus is free (`w_has_event && !output_busy`):

- `pkt_valid` = 1
- `pkt_type` = `PktTypeDebug`
- `pkt_event_code` = `AXI_DEBUG_STATE_CHANGE`
- `pkt_channel` = `{3'b0, trans_table[w_sel].channel[5:0]}`
- `pkt_data` = `{3'(r_prev_state[w_sel]), 3'(trans_table[w_sel].state), 26'h0, trans_table[w_sel].addr}`

The `(prev, new)` state tuple sits in the top six bits and the 32-bit address in the low bits, leaving a 26-bit zero gap between them. The compression analysis can key on either field.

### Direct-Inject and output_busy

Like the threshold and perf cones, debug packets bypass the shared FIFO and inject directly onto the MonBus, so the block must observe `output_busy` to avoid overwriting an in-flight packet — `pkt_valid` is gated by `!output_busy`.

---

## Usage Example

```systemverilog
// Instantiated inside axi_monitor_reporter, gated by ENABLE_DEBUG_LOGIC.
axi_monitor_reporter_debug #(
    .MAX_TRANSACTIONS (MAX_TRANSACTIONS)
) u_debug (
    .aclk             (aclk),
    .aresetn          (aresetn),

    .trans_table      (trans_table),
    .cfg_debug_enable (cfg_debug_enable),

    // Direct-inject arbitration with the top reporter
    .output_busy      (monbus_output_busy),
    .pkt_taken        (debug_pkt_taken),   // currently unused inside the block

    .pkt_valid        (dbg_valid),
    .pkt_type         (dbg_type),
    .pkt_event_code   (dbg_event_code),
    .pkt_channel      (dbg_channel),
    .pkt_data         (dbg_data)
);
```

> Note: enabling debug packets alongside completions/perf can congest the MonBus. See the AXI Monitor Configuration Guide before turning `cfg_debug_enable` on in a real run.

---

## Design Notes

### pkt_taken Is Intentionally Unused

The `r_prev_state` flop advances every cycle regardless of whether the emitted packet was accepted, so a missed transition simply gets aliased into the next change. `pkt_taken` is therefore not consumed today — it is kept on the port list (with an explicit `UNUSED` lint waiver) for symmetry with the threshold/perf cones and for future hooks such as backpressure on debug bursts.

### Sequential, Not Combinational

Unlike the completion and error cones (pure combinational), this block flops `r_prev_state`, which is inherently required to detect edges. It therefore takes `aclk`/`aresetn`.

### Compile-Out Path

Instantiated under `ENABLE_DEBUG_LOGIC` in the parent; setting it to 0 drops the block entirely. `cfg_debug_enable` is the runtime mask when the logic is present — emissions are gated but the logic still synthesizes.

### State Tuple Encoding

The 3-bit state codes follow `transaction_state_t` (`TRANS_IDLE=0`, `ADDR_PHASE=1`, `DATA_PHASE=2`, `COMPLETE=3`, `ERROR=4`, `ORPHANED=5`), packed as `{prev, new}` in `pkt_data[63:58]`.

---

## Related Modules

### Used By
- **axi_monitor_reporter.sv** - Top reporter that arbitrates the direct-inject MonBus path

### Uses
- **monitor_common_pkg** - `PktTypeDebug`, `transaction_state_t`, `TRANS_IDLE`, `bus_transaction_t`
- **monitor_amba4_pkg** - `AXI_DEBUG_STATE_CHANGE` event code
- **reset_defs.svh** - `ALWAYS_FF_RST` / `RST_ASSERTED` reset macros

### See Also
- **axi_monitor_reporter_compl.sv** - Completion detection cone (sibling sub-block)
- **axi_monitor_reporter_error.sv** - Error/orphan detection cone (sibling sub-block)
- **axi_monitor_base.sv** - The monitor scaffold that houses trans_mgr + reporter

---

## References

### Source Code
- RTL: `rtl/amba/monitor/axi_monitor_reporter_debug.sv`

### Documentation
- Packet format: `docs/markdown/RTLAmba/includes/monitor_package_spec.md`
- Monitor base: `docs/markdown/RTLAmba/axi_monitor_base.md`
- Configuration: `docs/user-guides/AXI_Monitor_Configuration_Guide.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](../_book_monitor_index.md)
- [Back to RTLAmba Index](../index.md)
