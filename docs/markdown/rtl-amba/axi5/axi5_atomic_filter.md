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

# AXI5 Atomic Filter

**Module:** `axi5_atomic_filter.sv`
**Location:** `rtl/amba/axi5/`
**Status:** Production Ready

---

## Overview

The AXI5 Atomic Filter terminates **read-return atomic transactions** at a
boundary whose downstream fabric can transport store-class atomics but cannot
route the read data that load-class atomics return. It sits on the AW/W/B
**control path**, plus an R-channel merge for the read data it owes; address
and data payload buses route around it.

AXI5 `AWATOP[5:0]` encodes four transaction classes:

| AWATOP | Class | Response | Filter action |
|---|---|---|---|
| `6'b000000` | Non-atomic write | B | **Forward** |
| `6'b01xxxx` | AtomicStore | B only | **Forward** |
| `6'b10xxxx` | AtomicLoad | B + original data on **R** | **Swallow + local DECERR on B and R** |
| `6'b11000x` | AtomicSwap / AtomicCompare | B + original data on **R** | **Swallow + local DECERR on B and R** |

The load-class R response uses the AW's ID on the **read** channel. A fabric
that splits write and read paths (such as the bridge crossbar, where every
R-return tracker learns only about ARs) would never route that response — the
transaction would hang. The filter guarantees it never reaches the fabric:
the AW is accepted upstream but not forwarded, its W burst is consumed and
discarded, a local `DECERR` B response returns with the AW's ID, and the read
data transfers the atomic owes are returned on R, each `DECERR`, with
`RID` = `AWID` and `RLAST` on the last one.

IHI 0022L §A6.4.8 requires those R transfers: "A Subordinate must send the
correct number of read data transfers, even if the write response is DECERR or
SLVERR", and a compliant manager waits for them. The count is §A6.4.7's:

| Atomic | R transfers |
|---|---|
| AtomicLoad, AtomicSwap | `AWLEN + 1` |
| AtomicCompare, `AWLEN = 0` | 1 |
| AtomicCompare, `AWLEN > 0` | `(AWLEN + 1) / 2` (the compare and swap values share the write data; the original value is half as long) |

Both Compare rows reduce to `(AWLEN >> 1) + 1`, which is what the RTL
computes. A filter that answered on B only (the module before GitHub #102)
left a compliant manager waiting for R forever.

### Key Features

- Discriminates purely on `AWATOP[5]` — one wire, no decode table
- Route queue (push per AW, pop at WLAST) steers or sinks each W burst, so
  forwarded and swallowed bursts interleave correctly in AW order
- Read-return queue (`AWID` + beat count per swallowed atomic) drains local
  DECERR R beats whenever the downstream R channel is idle. Entries are visible
  as soon as the AW is accepted: §A6.4.7 lets a Subordinate send all read data
  before accepting any write data, and requires the Manager to take it.
- **R bursts never interleave.** Once a burst's first beat is accepted, the R
  source is held until `RLAST`, so a downstream read burst and a local
  read-return burst cannot mix on `s_r*`. Downstream wins only at a burst
  boundary.
- Response queue drains local DECERRs whenever the downstream B channel is
  idle. Downstream takes priority only when the filter is free to switch:
  once a beat is presented on `s_bvalid`, the chosen source is **held** until
  the master accepts it, and `m_bready` is qualified by that choice. Without
  the hold, a downstream B arriving under a stalled `s_bvalid` would swap
  `s_bid`/`s_bresp` mid-beat, which AXI forbids
- Control-plane only: `id`, `atop`, `awlen`, `wlast`, `rlast` and the eight
  handshake pairs (`s_aw`/`s_w`/`s_b`/`s_r` and `m_aw`/`m_w`/`m_b`/`m_r`).
  All other AW/W payload passes around the filter; the B payload
  (`bid`/`bresp`) and the R control payload (`rid`/`rresp`/`rlast`) are the
  filter's output muxes. `RDATA`, `RUSER` and the AXI5 R sidebands route
  around it too: on a local error beat they carry whatever the downstream R
  bus holds, which a DECERR makes don't-care
- Single clock domain, no protocol state machine — two small FIFOs and
  combinational routing

## Parameters

| Parameter | Default | Description |
|---|---|---|
| `AXI_ID_WIDTH` | 4 | Width of `s_awid` / `s_bid` / `m_bid` |
| `AXI_ATOP_WIDTH` | 6 | AWATOP width (the spec value; only bit [5] is examined) |
| `DEPTH_LG2` | 3 | log2 of the route, B-response and read-return queue depth (default 8 entries) |

### Derived Parameters (do not override)

These are declared as `parameter` so the elaborator can compute them, not so callers can set them. Each defaults to an expression over the parameters above; overriding one desynchronises it from its source and the design fails to elaborate or silently mis-sizes a bus. Set the parameters they are derived FROM and leave these alone.

| Derived parameter | Default expression |
|---|---|
| `IW` | `AXI_ID_WIDTH` |
| `DEPTH` | `1 << DEPTH_LG2` |

## Ports

Upstream (`s_*`) faces the boundary wrapper's FUB side; downstream (`m_*`)
faces the fabric. Only control signals pass through:

| Group | Signals |
|---|---|
| AW | `s_awvalid/awready/awid/awatop/awlen` → `m_awvalid/awready` |
| W | `s_wvalid/wready/wlast` → `m_wvalid/wready` |
| B | `m_bvalid/bready/bid/bresp` → `s_bvalid/bready/bid/bresp` |
| R | `m_rvalid/rready/rid/rresp/rlast` → `s_rvalid/rready/rid/rresp/rlast` (merged with the local read-return beats) |

The ports added for the R path (GitHub #102 item 2):

| Port | Width | Direction | Description |
|---|---|---|---|
| `s_awlen` | 8 | Input | AWLEN of the upstream AW; sets the R beat count of a swallowed atomic (§A6.4.7) |
| `s_rvalid` | 1 | Output | Merged read data valid toward the manager |
| `s_rready` | 1 | Input | Manager read data ready |
| `s_rid` | IW | Output | `m_rid`, or the swallowed atomic's `AWID` |
| `s_rresp` | 2 | Output | `m_rresp`, or `2'b11` (DECERR) on a local beat |
| `s_rlast` | 1 | Output | `m_rlast`, or the last local beat of the atomic |
| `m_rvalid` | 1 | Input | Downstream read data valid |
| `m_rready` | 1 | Output | `s_rready` while the downstream source is selected |
| `m_rid` | IW | Input | Downstream RID |
| `m_rresp` | 2 | Input | Downstream RRESP |
| `m_rlast` | 1 | Input | Downstream RLAST |
| Clock/reset | `aclk`, `aresetn` (active-low async) -- single domain, shared with both sides |

## Functional Description

The filter sits on the write path and decides, per AW,
whether the burst is forwarded downstream or swallowed. An unsupported atomic
(`AWATOP` naming a load, swap or compare) is swallowed: its W beats are discarded,
a local DECERR is returned on B with the AW's ID, and its read data transfers are
returned on R as DECERR beats with the same ID. Everything else passes through.

A route queue pushed per AW and popped at WLAST steers each W burst, so forwarded and
swallowed bursts interleave correctly in AW order. A response queue holds the locally
generated DECERRs, and the B output selects between that queue and the downstream
response. A read-return queue holds `{AWID, beats-1}` per swallowed atomic plus a beat
counter for its head, and the R output selects between it and the downstream R channel,
holding the choice for a whole burst.

There is no protocol state machine: three small FIFOs, a beat counter and
combinational routing.

---

## Timing Characteristics

This module is **sequential**: it contains 3 `always_ff` block(s),
clocked on `aclk` with active-low asynchronous reset `aresetn`. Outputs derived
in those blocks are registered and therefore appear one clock after the inputs
that produced them.

Per-path cycle counts are not enumerated here; read the block that drives the
signal you care about. No synthesis frequency or area figures are quoted --
none have been measured against a target device.

---

## Usage Examples

Every parameter and port below is taken from the module declaration.

```systemverilog
axi5_atomic_filter #(
    .AXI_ID_WIDTH          (4),
    .AXI_ATOP_WIDTH        (6),
    .DEPTH_LG2             (3),
    .IW                    (AXI_ID_WIDTH),
    .DEPTH                 (1 << DEPTH_LG2)
) u_axi5_atomic_filter (
    .aclk                  (aclk),
    .aresetn               (aresetn),
    .s_awvalid             (s_awvalid),
    .s_awready             (s_awready),
    .s_awid                (s_awid),
    .s_awatop              (s_awatop),
    .s_awlen               (s_awlen),
    .s_wvalid              (s_wvalid),
    .s_wready              (s_wready),
    .s_wlast               (s_wlast),
    .s_bvalid              (s_bvalid),
    .s_bready              (s_bready),
    .s_bid                 (s_bid),
    .s_bresp               (s_bresp),
    .s_rvalid              (s_rvalid),
    .s_rready              (s_rready),
    .s_rid                 (s_rid),
    .s_rresp               (s_rresp),
    .s_rlast               (s_rlast),
    .m_awvalid             (m_awvalid),
    .m_awready             (m_awready),
    .m_wvalid              (m_wvalid),
    .m_wready              (m_wready),
    .m_bvalid              (m_bvalid),
    .m_bready              (m_bready),
    .m_bid                 (m_bid),
    .m_bresp               (m_bresp),
    .m_rvalid              (m_rvalid),
    .m_rready              (m_rready),
    .m_rid                 (m_rid),
    .m_rresp               (m_rresp),
    .m_rlast               (m_rlast)
);
```

---

### Integration

The bridge generator (bridge TASK-002 (was BRIDGE-002) A5-3a) inserts this filter automatically in
the master adapter of any AXI5 master port with `atomic` in its
`axi5_features`, between the `axi5_slave_wr` boundary wrapper (`pref_axi_*`)
and the fabric-facing `fub_axi_*` namespace. Handshakes and the B payload go
through the filter; every other signal gets a `pref → fub` pass-through
assign. Swallowed transactions never assert `m_awvalid`, so stale
pass-through payload is inert.

Standalone integrations follow the same recipe: route payload around,
handshakes through.

### Design Notes and Constraints

- **W stalls until its AW is queued.** `s_wready` is held low while the
  route queue is empty. AW acceptance never depends on W, so this cannot
  deadlock; it simply serializes W-before-AW masters at this boundary.
- **Same-ID B and R ordering.** A local DECERR (B or R) can pass an
  in-flight forwarded transaction's response. The AXI atomic rules already require atomics not to
  share an ID with outstanding transactions, so a compliant master never
  observes the reorder.
- **DECERR, not SLVERR.** An unsupported atomic at this boundary is "no
  such capability at this address path" — the decode-class error.
- The filter is intentionally not parameterized to pass load-class atomics
  through: a fabric that CAN route read returns (A5-3b's shared per-ID
  tracker) simply omits the filter.
## Design Notes

**The B selection must be HELD once presented.** AXI requires BID
and BRESP to be stable from BVALID until the handshake. Selecting combinationally
between the downstream response and a queued DECERR lets a downstream B arriving
under a stalled `s_bvalid` change the payload mid-beat; the module latches which
source is presented and releases only on accept, and qualifies `m_bready` by that
choice so a downstream response is not consumed while the master is still looking at
a DECERR.

**DECERR, not SLVERR.** An unsupported atomic at this boundary is "no such
capability here", which is a decode error.

**The R channel passes through it.** The filter has eight handshake pairs --
`s_aw`/`s_w`/`s_b`/`s_r` and `m_aw`/`m_w`/`m_b`/`m_r`. AR does not pass
through it; only R does, because that is where a swallowed atomic's read data
must appear. The R selection is held twice over: under backpressure (payload
stable from RVALID to the handshake, as for B) and for a whole burst (no
interleaving of local and downstream bursts).

---

## Testing
`val/amba/test_axi5_atomic_filter.py` — direct cocotb driving: mixed
forward/swallow traffic, a multi-beat swallowed burst, DECERR ID/order checks,
and forwarded-set assertions.

`atomic_filter_read_return_r_test` covers the R path: AtomicLoad, AtomicSwap
and AtomicCompare at several `AWLEN`s, each checked for its exact §A6.4.7 beat
count, `RID`, DECERR on every beat and `RLAST` on the last one, while a
downstream R stream shares the channel under random manager backpressure. It
also checks that bursts from the two sources never interleave and that the
presented R payload holds from RVALID to the handshake. Each of three RTL
mutations (no burst hold, no backpressure hold, Compare not halved) fails it;
on the pre-#102 module it fails at once, because there is no R channel.

Until GitHub #102 this file passed its tests to cocotb as a comma-separated
`testcase=` list. Under cocotb 2.x that matched no test at all, so the file ran
zero tests and still reported PASS; it now runs every test in the module.

Most phases use an always-ready downstream model, which cannot exercise the B
selection hold: with `s_bready` high throughout, no beat is ever presented and
unaccepted, so the stability window never opens. A dedicated phase therefore
stalls the master, queues a local DECERR, then raises `m_bvalid` underneath it
and asserts `s_bid`/`s_bresp` hold for eight cycles. Removing the hold from the
RTL fails that phase at cycle 0; nothing else in the suite notices.
End-to-end behavior (real ATOP values through a generated bridge, memory
side-effect checks) is covered by
`projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_1x2_wr_axi5a_atomics.py`.

## Related Modules

- [axi5_slave_wr](axi5_slave_wr.md) — the boundary wrapper upstream of the
  filter in bridge master adapters
- [axi5_atomic_rr_tracker](axi5_atomic_rr_tracker.md) — the alternative for a
  fabric that CAN route read-return data
- [AXI5 index](README.md) — scope statement for the AXI5 family

## References

- Arm. *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022, Issue H, Mar. 2020. [developer.arm.com/documentation/ihi0022/h](https://developer.arm.com/documentation/ihi0022/h/) -- §E1.1.8 "Response signaling": an error response is permitted from a component that does not support atomics, but for AtomicLoad, AtomicSwap and AtomicCompare "a slave must send the correct number of read data beats, even if the write response is DECERR or SLVERR". This filter does exactly that: a DECERR on B and the full count of DECERR read beats on R (Issue L §A6.4.8; GitHub #102 item 2).
- Arm. *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022, Issue H, Mar. 2020. [developer.arm.com/documentation/ihi0022/h](https://developer.arm.com/documentation/ihi0022/h/) -- §E1.1.4 "ID use for Atomic transactions" (Issue L §A6.4.4, "unique-in-flight"): why a local DECERR passing a same-ID B is invisible to a compliant master; §A3.3.1 "Dependencies between channel handshake signals": B only after the last W beat, which is why the local DECERR is committed at WLAST.
- Arm. *AMBA AXI Protocol Specification*, ARM IHI 0022, Issue L, Aug. 2025. [developer.arm.com/documentation/ihi0022/latest](https://developer.arm.com/documentation/ihi0022/latest/) -- §A6.4.2 "Atomic transaction operations" and §A6.4.6 "Atomic transaction signaling" (the AWATOP encodings; bit 5 set marks the read-return classes); §A6.4.7 "Transaction structure" (the number of read data transfers: AWLEN+1, halved for a multi-transfer AtomicCompare); §A6.4.8 "Response signaling" (the read transfers are owed even when the write response is an error).
- Cummings, C.E. "Simulation and Synthesis Techniques for Asynchronous FIFO Design." *SNUG San Jose*, 2002 -- the wrap-bit full/empty test used by the route and response queues.
- Indexed in `rtl/amba/references/README.md` (local PDF, archived under `rtl/cdc/references/`: `AsyncFifoGrayPointers__Cummings2002.pdf`)

---

## Navigation

- **[← Back to axi5 index](../axi5/README.md)**
- **[← Back to rtl-amba index](../index.md)**
