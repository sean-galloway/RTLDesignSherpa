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

# Monitor Bus Round-Robin Arbiter

**Module:** `monbus_arbiter.sv`
**Location:** `rtl/amba/monitor/`
**Status:** Production Ready

---

## Overview

`monbus_arbiter` merges monitor bus packet streams from multiple clients —
AXI monitors, APB monitors, arbiter monitors, whatever you've got — into a
single output stream, using fair round-robin arbitration with an ACK
protocol. Optional skid buffers on the inputs and the output improve timing
closure and give you elasticity against backpressure.

The ACK protocol is the point: a granted client gets to finish its packet
before the arbiter moves on to the next requester, so multi-cycle transfers
never fragment. Combined with the integrated buffering and proper
backpressure handling, packets don't get lost on the way through.

- Round-robin arbitration for monitor bus packet streams
- ACK mode operation (grants held until acknowledged)
- Optional input skid buffers per client (2..8 entries)
- Optional output skid buffer (2..8 entries)
- 128-bit packet + 64-bit side-band timestamp, carried atomically through a 192-bit skid
- Parameterizable client count (2-64; 1 does not elaborate)
- Skid buffers optional (disabling them removes the skid registers; the arbitration cycle itself remains, since `grant_valid` is registered)

---

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| CLIENTS | int | 4 | Number of monitor bus clients (**2**-64). `CLIENTS=1` does **not** elaborate: `N = $clog2(1) = 0` makes `grant_id` a `logic [-1:0]` and the priority encoder's generic branch does an illegal `i[-1:0]` part-select |
| INPUT_SKID_ENABLE | int | 1 | Enable skid buffers on input interfaces |
| OUTPUT_SKID_ENABLE | int | 1 | Enable skid buffer on output interface |
| INPUT_SKID_DEPTH | int | 2 | Depth of input skid buffers (2..8 inclusive) |
| OUTPUT_SKID_DEPTH | int | 2 | Depth of output skid buffer (2..8 inclusive) |
| `SKID_DATA_WIDTH` | int | `MONBUS_PKT_WIDTH + MONBUS_TS_WIDTH` | Width of the packed skid-buffer payload. |

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|---|---|---|---|
| axi_aclk | input | 1 | Clock signal |
| axi_aresetn | input | 1 | Active-low asynchronous reset |

### Block Arbitration

| Port | Direction | Width | Description |
|---|---|---|---|
| block_arb | input | 1 | Block arbitration when asserted |

### Monitor Bus Inputs (Array of CLIENTS)

| Port | Direction | Width | Description |
|---|---|---|---|
| monbus_valid_in[CLIENTS] | input | CLIENTS | Per-client packet valid signals |
| monbus_ready_in[CLIENTS] | output | CLIENTS | Per-client ready signals |
| monbus_packet_in[CLIENTS] | input | CLIENTS × 128 | Per-client `monitor_packet_t` packets |
| monbus_timestamp_in[CLIENTS] | input | CLIENTS × 64 | Per-client `monbus_timestamp_t`, sampled at each client's emission time |

### Monitor Bus Output (Aggregated)

| Port | Direction | Width | Description |
|---|---|---|---|
| monbus_valid | output | 1 | Aggregated packet valid |
| monbus_ready | input | 1 | Aggregated ready from downstream |
| monbus_packet | output | 128 | Aggregated `monitor_packet_t` |
| monbus_timestamp | output | 64 | Aggregated `monbus_timestamp_t`, paired atomically with `monbus_packet` |

### Debug/Status Outputs

| Port | Direction | Width | Description |
|---|---|---|---|
| grant_valid | output | 1 | Grant is active this cycle |
| grant | output | CLIENTS | One-hot grant vector |
| grant_id | output | $clog2(CLIENTS) | Binary encoded grant ID |
| last_grant | output | CLIENTS | Previous grant (for round-robin rotation) |

---

## Functional Description

### Arbiter Request and Grant ACK Logic

The module maps monitor bus protocol onto arbiter protocol.

**Request Mapping**: each client's valid becomes an arbiter request —
`request[i] = int_monbus_valid_in[i]`, i.e. the signal *after* the optional
input skid, not the port itself.

**Grant ACK Logic**: ACK occurs only when the beat is actually **consumed** —
grant, valid, and downstream ready together:

```systemverilog
grant_ack[i] = grant[i] && int_monbus_valid_in[i] && int_monbus_ready;
```

The `int_monbus_ready` term is load-bearing and must not be dropped. Without it
(`grant[i] && int_monbus_valid_in[i]` alone) the ack fires on every cycle the
sink is back-pressuring, so the grant rotates continuously while **zero**
transfers take place — breaking the grant-hold contract. That was a real defect;
`val/amba/test_monbus_arbiter_grant_hold.py` is the regression that pins it.

### Round-Robin Arbiter Instance

Uses arbiter_round_robin with WAIT_GNT_ACK=1:

- Fair rotation through active requests
- Grant held until acknowledged
- Block_arb input for external control

### Client Ready Signal Generation

Each client's ready signal asserts when:

1. That client is currently granted AND
2. Downstream (internal output) is ready to accept data

```systemverilog
int_monbus_ready_in[i] = grant[i] && int_monbus_ready;
```

This ensures only the granted client can transfer data, preventing collisions.

> **With the default `INPUT_SKID_ENABLE=1`, this is not what the port does.**
> The rule above governs the *internal* ready behind the skid buffer. The
> actual port `monbus_ready_in[i]` is the skid's `wr_ready`, which asserts
> whenever the skid has room — **independently of any grant**. A client can
> therefore be accepted while ungranted; the skid holds the beat until its
> grant comes. Only with `INPUT_SKID_ENABLE=0` do the port and the internal
> signal coincide.

### Output Multiplexer

Selects data from the granted client:

```systemverilog
if (grant_valid)
    int_monbus_packet = int_monbus_packet_in[grant_id];  // post-skid
```

### Optional Skid Buffers

All skid buffers in this arbiter carry the **packet and timestamp atomically**
in a 192-bit payload (`MONBUS_PKT_WIDTH + MONBUS_TS_WIDTH = 128 + 64`). The
arbiter never separates a packet from its sampled timestamp, so consumers
downstream of the [`monbus_group` family](monbus_group.md) see a coherent
(pkt, ts) tuple even after multiple levels of skid.

**Input Skid Buffers** (per client):

- Uses gaxi_skid_buffer instances configured for 192-bit data
- Provides elasticity for clients with bursty traffic
- Improves timing closure by breaking long paths
- Depth configurable: 2..8 entries inclusive (odd depths are legal)

**Output Skid Buffer**:

- Buffers aggregated stream before output (also 192-bit)
- Prevents backpressure propagation to arbiter
- Same depth options as input buffers

**When to Enable Skid Buffers**:

- Enable INPUT_SKID if clients have high-latency paths or bursty traffic
- Enable OUTPUT_SKID if downstream consumer has variable latency
- Disable both for minimum latency. That removes the skid registers only;
  it is NOT a combinational pass-through. `monbus_valid` comes from
  `arbiter_round_robin`'s `grant_valid`, which is registered, so a request
  still costs one arbitration cycle. See "Skid-Free Configuration".

---

## Timing Characteristics

This module is **purely combinational** -- it contains no `always_ff` and no
latch, so it holds no state and adds no clock cycles. Its outputs settle a
propagation delay after its inputs, and it introduces no latency into a
pipeline that instantiates it.

Timing closure is therefore a question of the surrounding logic's slack, not of
this module's cycle count. No synthesis figures are quoted; none have been
measured.

---

## Usage Examples
```systemverilog
// Aggregate monitor bus streams from 4 clients
monbus_arbiter #(
    .CLIENTS             (4),
    .INPUT_SKID_ENABLE   (1),    // Enable input buffers
    .OUTPUT_SKID_ENABLE  (1),    // Enable output buffer
    .INPUT_SKID_DEPTH    (4),    // 4-entry input buffers
    .OUTPUT_SKID_DEPTH   (4)     // 4-entry output buffer
) u_monbus_arb (
    .axi_aclk            (clk),
    .axi_aresetn         (rst_n),
    .block_arb           (1'b0),  // Not blocked

    // Connect 4 client monitor bus streams (packet + timestamp per client).
    // NOTE the asymmetry: the three INPUT arrays take assignment patterns,
    // which are legal rvalues for an unpacked-array input. monbus_ready_in is
    // an OUTPUT, so its connection must be an lvalue -- an assignment pattern
    // there does not compile. Declare the array and connect it whole:
    //     logic mon_ready [4];
    //     assign {mon0_ready, mon1_ready, mon2_ready, mon3_ready} =
    //            {mon_ready[0], mon_ready[1], mon_ready[2], mon_ready[3]};
    .monbus_valid_in     ('{mon0_valid, mon1_valid, mon2_valid, mon3_valid}),
    .monbus_ready_in     (mon_ready),
    .monbus_packet_in    ('{mon0_packet, mon1_packet, mon2_packet, mon3_packet}),
    .monbus_timestamp_in ('{mon0_ts,     mon1_ts,     mon2_ts,     mon3_ts}),

    // Aggregated output stream (packet + timestamp paired atomically)
    .monbus_valid        (agg_valid),
    .monbus_ready        (agg_ready),
    .monbus_packet       (agg_packet),
    .monbus_timestamp    (agg_ts),

    // Debug outputs
    .grant_valid         (arb_grant_valid),
    .grant               (arb_grant_onehot),
    .grant_id            (arb_grant_id),
    .last_grant          (arb_last_grant)
);

// Downstream consumer is typically the monbus_group family, which expects the
// 128-bit packet on monbus_packet and the 64-bit timestamp on
// monbus_timestamp. No additional FIFO is needed at this boundary —
// raw-mode groups have no ingress skid of their own; only the
// compressed build adds one (u_comp_in_skid in monbus_group_core).
```

---

## Design Notes

### ACK Mode Operation

The ACK mode is what guarantees clean packet transfer:

**Grant Assertion**: When arbiter selects a client, grant[i] asserts
**Client Response**: Client's monbus_valid_in[i] must be high
**Grant ACK**: `grant_ack[i] = grant[i] && int_monbus_valid_in[i] && int_monbus_ready` — the ready term is required (see above)
**Hold Grant**: Arbiter holds grant[i] until grant_ack[i] asserts
**Next Client**: After ACK, arbiter moves to next requesting client

This prevents:

- Packet fragmentation (grant switching mid-transfer)
- Lost packets (grant removed before client ready)
- Unfair arbitration (clients getting multiple back-to-back grants)

### Skid Buffer Depth Selection

Choose depth based on system characteristics:

**2 Entries (Minimum)**:

- Minimal buffering for timing closure only
- Use when clients have low, consistent latency

**4 Entries (Recommended)**:

- Good balance of buffering and area
- Handles typical backpressure scenarios
- Recommended for most systems

**6-8 Entries**:

- High buffering for very bursty traffic
- Use when downstream has high variable latency
- Higher area cost

### Skid-Free Configuration

For minimum latency:

```systemverilog
.INPUT_SKID_ENABLE  (0),
.OUTPUT_SKID_ENABLE (0)
```

This removes the skid registers, but it does **not** make the valid path
combinational. `monbus_valid` is driven from the arbiter's `grant_valid`,
which is a REGISTERED output of `arbiter_round_robin`, so a request still
takes an arbitration cycle to appear as a grant:

- monbus_valid_in[i] -> request[i] -> (registered grant) -> monbus_valid
- monbus_packet_in[grant_id] -> monbus_packet (combinational mux on grant_id)
- monbus_ready -> monbus_ready_in[grant_id] (combinational, gated by grant)

Use when:

- Timing is not critical
- Clients and downstream have matched latencies
- Minimum latency required for event ordering

### Assertions

The module includes comprehensive assertions:

**Grant One-Hot**: Verifies grant vector is one-hot when valid
**Grant ID Consistency**: Verifies grant_id corresponds to asserted grant bit
**Ready Exclusivity**: Verifies only granted client receives ready signal

---

## Related Modules

**Used by:**

- System-level monitor bus aggregation hierarchies
- Multi-subsystem monitoring infrastructures

**Uses:**

- arbiter_round_robin.sv (ACK-mode arbiter)
- gaxi_skid_buffer.sv (optional input/output buffering)

**Related:**

- arbiter_monbus_common.sv (generates monitor bus packets)
- arbiter_rr_pwm_monbus.sv (arbiter with integrated monitoring)

---

## Testing

The grant-hold defect described above is pinned by
`val/amba/test_monbus_arbiter_grant_hold.py` — run it after any change to
the ACK or ready logic.

---

## References

### Specifications

- Internal: docs/markdown/rtl-amba/index.md (AMBA subsystem requirements)
- Internal: docs/markdown/rtl-amba/includes/monitor_package_spec.md (monitor bus protocol)

### Source Code

- RTL: `rtl/amba/monitor/monbus_arbiter.sv`
- Tests: `val/amba/test_monbus_arbiter_grant_hold.py` (if exists)

---

**Last Updated:** 2025-10-24

---

## Navigation

- [Back to Shared Infrastructure Index](../_book_monitor_index.md)
- [Back to rtl-amba Index](../index.md)
