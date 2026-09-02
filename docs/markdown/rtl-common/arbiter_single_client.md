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

**[← Back to Main Index](../index.md)** | **[rtl-common Index](index.md)**

# Single-Client Arbiter

**Module:** `arbiter_single_client.sv`
**Location:** `rtl/common/`
**Status:** Production Ready

## Overview

`arbiter_single_client` is the degenerate, one-requester member of the round-robin arbiter family. It exists to give a single-channel datapath the **exact same registered, ack-held grant lifecycle** as `arbiter_round_robin` running in `WAIT_GNT_ACK` mode, without the parameter degeneracy that breaks the multi-client arbiter when `CLIENTS == 1`.

`arbiter_round_robin` underflows at `CLIENTS == 1` because `$clog2(1) = 0` produces a `grant_id[-1:0]` slice. Historically single-channel builds worked around this by substituting a purely *combinational* passthrough (`grant = request`). That passthrough does **not** reproduce the arbiter's registered grant/ack handshake, so it injects a bubble beat at every burst boundary in the AXI read/write engines that depend on the "request, grant, hold-for-ack" timing. This module is the faithful single-client reduction of those rules.

### Key Features

- **Timing-faithful:** Mirrors `arbiter_round_robin` `WAIT_GNT_ACK` `always_ff` rules exactly for one client
- **Registered grant:** Grant is a flip-flop output, held until acknowledged (no combinational passthrough bubble)
- **Ack-held lifecycle:** Grant persists until `grant_ack`, then clears and can re-grant the next cycle
- **Bubble-free bursts:** Preserves the grant timing the AXI read/write engines rely on for back-to-back burst beats
- **Optional ack mode:** `WAIT_GNT_ACK = 0` falls back to a simple registered request-to-grant with no ack hold
- **Trivial decode:** `grant` is a one-hot of width 1 (equal to `grant_valid`); `grant_id` is always 0

### Use Cases

The module provides a drop-in single-client arbiter so that a design parameterized down to one channel behaves identically to the same design with two or more channels. Rather than special-casing the `NUM_CHANNELS == 1` build with a passthrough, the datapath instantiates `arbiter_single_client` and gets the identical grant/ack sequencing the general arbiter would have produced for one requester.

- Single-channel builds of a datapath that is otherwise parameterized for N channels
- AXI read/write engines that require the registered, ack-held grant handshake for correct burst sequencing
- Any place a `arbiter_round_robin` instance would be used, but with `CLIENTS == 1`
- Replacing a combinational `grant = request` passthrough that was injecting per-burst bubble beats

**Key Benefit:** A one-channel build behaves bit-for-bit like the multi-channel arbiter path, eliminating the burst-boundary bubble that a combinational passthrough introduced.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| WAIT_GNT_ACK | int | 1 | `1` = registered grant is held until `grant_ack` is received (round-robin ACK lifecycle). `0` = simple registered request-to-grant with no ack hold. |

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| clk | 1 | Clock |
| rst_n | 1 | Active-low asynchronous reset |
| block_arb | 1 | Block arbitration; when high the request is masked and no grant is issued |
| request | 1 | The single client's request |
| grant_ack | 1 | The single client's grant acknowledgment (used only when `WAIT_GNT_ACK = 1`) |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| grant_valid | 1 | Grant valid (registered) |
| grant | 1 | One-hot grant of width 1; equal to `grant_valid` |
| grant_id | 1 | Granted client index; always `0` for a single client |

## Functional Description

### Request Qualification

The incoming request is masked by `block_arb` first:

```systemverilog
assign w_req = request && !block_arb;
```

A blocked arbiter behaves as if the client were not requesting at all.

### Grant-Eligibility Logic (ACK Mode)

When `WAIT_GNT_ACK = 1`, three combinational signals gate whether a new grant may be issued:

```systemverilog
assign w_ack_received = r_pending_ack && grant_ack;          // ack seen for the outstanding grant
assign w_can_grant    = !r_pending_ack || w_ack_received;    // free to grant, or ack just closed the last grant
assign w_should_grant = w_req && w_can_grant;
```

`r_pending_ack` records that a grant has been issued and is awaiting its acknowledgment. A new grant can only be launched when there is no pending ack, or when the ack for the current grant arrives this cycle.

### Grant Lifecycle (ACK Mode)

The registered state machine is the single-client reduction of the `arbiter_round_robin` `WAIT_GNT_ACK` rules. Because there is only one client, `w_other_requests` is always 0, so the arbiter's Rule 4 (switch to another requester) never applies and Rule 3 simply clears:

| State | Condition | Action | `grant_valid` next | `r_pending_ack` next |
|-------|-----------|--------|--------------------|----------------------|
| Rule 1 | `grant_valid == 0` | Not granted; grant if requesting | `w_should_grant` | `w_should_grant` |
| Rule 2 | granted, `!w_ack_received` | Hold the grant | `1` | `1` |
| Rule 3 | granted, `w_ack_received` | Ack received; clear (re-grant next cycle) | `0` | `0` |

The grant is thus **registered and held** across cycles until the client acknowledges, then it drops for one cycle before it can be re-issued.

### No-ACK Fallback Mode

When `WAIT_GNT_ACK = 0`, the ack machinery is bypassed. `grant_valid` simply follows a registered version of the qualified request and `r_pending_ack` stays 0:

```systemverilog
grant_valid   <= w_should_grant;   // w_can_grant is constant 1 in this mode
r_pending_ack <= 1'b0;
```

This gives a one-cycle registered request-to-grant with no hold.

### Output Mapping

```systemverilog
assign grant    = grant_valid;   // one-hot of width 1
assign grant_id = 1'b0;          // single client
```

Because there is exactly one client, `grant` and `grant_valid` are identical, and `grant_id` is a constant 0.

## Timing Characteristics

This module is **sequential**: it contains 1 `always_ff` block(s),
clocked on `clk` with active-low asynchronous reset `rst_n`. Outputs derived
in those blocks are registered and therefore appear one clock after the inputs
that produced them.

Per-path cycle counts are not enumerated here; read the block that drives the
signal you care about. No synthesis frequency or area figures are quoted --
none have been measured against a target device.

---

## Usage Examples
```systemverilog
// Single-channel build: use arbiter_single_client where a >1-channel
// build would instantiate arbiter_round_robin in WAIT_GNT_ACK mode.
arbiter_single_client #(
    .WAIT_GNT_ACK(1)
) u_arb (
    .clk        (aclk),
    .rst_n      (aresetn),
    .block_arb  (arb_blocked),
    .request    (engine_request),
    .grant_ack  (engine_grant_ack),
    .grant_valid(engine_grant_valid),
    .grant      (engine_grant),      // width-1 one-hot
    .grant_id   ()                   // always 0, usually unconnected
);
```

## Design Notes

- **Why not a combinational passthrough?** `grant = request` looks correct for one client but loses the registered, ack-held timing. The AXI read/write engines interpret the missing hold as an early grant drop and insert a bubble beat at every burst boundary. This module preserves the exact cycle-by-cycle behavior.
- **`grant_id` degeneracy.** The general arbiter's `grant_id` is `$clog2(CLIENTS)` bits wide, which collapses to an illegal `[-1:0]` slice at `CLIENTS == 1`. Here `grant_id` is simply tied to `0`, sidestepping the elaboration problem.
- **Block behavior.** `block_arb` masks the request combinationally, so raising it prevents new grants; an already-pending ack-held grant continues to follow the state machine.
- **Reset.** Active-low asynchronous reset clears both `grant_valid` and `r_pending_ack`.

## Related Modules

Used by single-channel builds of AXI read/write datapath engines that otherwise instantiate `arbiter_round_robin`. The module itself is self-contained — no submodule instantiations.

- [arbiter_round_robin](arbiter_round_robin.md) - The general N-client arbiter whose `WAIT_GNT_ACK` timing this module reproduces for one client
- [arbiter_round_robin_simple](arbiter_round_robin_simple.md) - Minimal-area round-robin variant
- [arbiter_round_robin_weighted](arbiter_round_robin_weighted.md) - Weighted / QoS round-robin variant
- [arbiter_priority_encoder](arbiter_priority_encoder.md) - Fixed-priority arbiter

Source: `rtl/common/arbiter_single_client.sv`, with `rtl/common/arbiter_round_robin.sv` as the timing reference, and `docs/markdown/rtl-common/index.md`.

**Last Updated:** 2026-07-15

## Testing

**No dedicated testbench, by decision.** A single-client arbiter grants its
one requester unconditionally; the behaviour is verified in situ in STREAM
rather than through a standalone bench. Recorded as exempt in the coverage
baseline (COMMON-024).

Treat any behaviour described on this page as unverified by simulation.

---

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
