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
**control path** only — address and data payload buses route around it.

AXI5 `AWATOP[5:0]` encodes four transaction classes:

| AWATOP | Class | Response | Filter action |
|---|---|---|---|
| `6'b000000` | Non-atomic write | B | **Forward** |
| `6'b01xxxx` | AtomicStore | B only | **Forward** |
| `6'b10xxxx` | AtomicLoad | B + original data on **R** | **Swallow + local DECERR** |
| `6'b11000x` | AtomicSwap / AtomicCompare | B + original data on **R** | **Swallow + local DECERR** |

The load-class R response uses the AW's ID on the **read** channel. A fabric
that splits write and read paths (such as the bridge crossbar, where every
R-return tracker learns only about ARs) would never route that response — the
transaction would hang. The filter guarantees it never reaches the fabric:
the AW is accepted upstream but not forwarded, its W burst is consumed and
discarded, and a local `DECERR` B response returns with the AW's ID.

### Key Features

- Discriminates purely on `AWATOP[5]` — one wire, no decode table
- Route queue (push per AW, pop at WLAST) steers or sinks each W burst, so
  forwarded and swallowed bursts interleave correctly in AW order
- Response queue drains local DECERRs whenever the downstream B channel is
  idle. Downstream takes priority only when the filter is free to switch:
  once a beat is presented on `s_bvalid`, the chosen source is **held** until
  the master accepts it, and `m_bready` is qualified by that choice. Without
  the hold, a downstream B arriving under a stalled `s_bvalid` would swap
  `s_bid`/`s_bresp` mid-beat, which AXI forbids
- Control-plane only: `id`, `atop`, `wlast`, and the six handshake pairs
  (`s_aw`/`s_w`/`s_b` and `m_aw`/`m_w`/`m_b` -- the filter sits on the write
  path only). All other AW/W payload passes around the filter; the B payload
  (`bid`/`bresp`) is the filter's output mux
- Single clock domain, no protocol state machine — two small FIFOs and
  combinational routing

## Parameters

| Parameter | Default | Description |
|---|---|---|
| `AXI_ID_WIDTH` | 4 | Width of `s_awid` / `s_bid` / `m_bid` |
| `AXI_ATOP_WIDTH` | 6 | AWATOP width (the spec value; only bit [5] is examined) |
| `DEPTH_LG2` | 3 | log2 of the route/response queue depth (default 8 entries) |

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
| AW | `s_awvalid/awready/awid/awatop` → `m_awvalid/awready` |
| W | `s_wvalid/wready/wlast` → `m_wvalid/wready` |
| B | `m_bvalid/bready/bid/bresp` → `s_bvalid/bready/bid/bresp` |

## Integration

The bridge generator (BRIDGE-002 A5-3a) inserts this filter automatically in
the master adapter of any AXI5 master port with `atomic` in its
`axi5_features`, between the `axi5_slave_wr` boundary wrapper (`pref_axi_*`)
and the fabric-facing `fub_axi_*` namespace. Handshakes and the B payload go
through the filter; every other signal gets a `pref → fub` pass-through
assign. Swallowed transactions never assert `m_awvalid`, so stale
pass-through payload is inert.

Standalone integrations follow the same recipe: route payload around,
handshakes through.

## Design Notes and Constraints

- **W stalls until its AW is queued.** `s_wready` is held low while the
  route queue is empty. AW acceptance never depends on W, so this cannot
  deadlock; it simply serializes W-before-AW masters at this boundary.
- **Same-ID B ordering.** A local DECERR can pass an in-flight forwarded
  write's B response. The AXI atomic rules already require atomics not to
  share an ID with outstanding transactions, so a compliant master never
  observes the reorder.
- **DECERR, not SLVERR.** An unsupported atomic at this boundary is "no
  such capability at this address path" — the decode-class error.
- The filter is intentionally not parameterized to pass load-class atomics
  through: a fabric that CAN route read returns (A5-3b's shared per-ID
  tracker) simply omits the filter.

## Verification

`val/amba/test_axi5_atomic_filter.py` — direct cocotb driving: mixed
forward/swallow traffic, a multi-beat swallowed burst, DECERR ID/order checks,
and forwarded-set assertions.

Most phases use an always-ready downstream model, which cannot exercise the B
selection hold: with `s_bready` high throughout, no beat is ever presented and
unaccepted, so the stability window never opens. A dedicated phase therefore
stalls the master, queues a local DECERR, then raises `m_bvalid` underneath it
and asserts `s_bid`/`s_bresp` hold for eight cycles. Removing the hold from the
RTL fails that phase at cycle 0; nothing else in the suite notices.
End-to-end behavior (real ATOP values through a generated bridge, memory
side-effect checks) is covered by
`projects/components/bridge/dv/tests/test_bridge_1x2_wr_axi5a_atomics.py`.

## Related Modules

- [axi5_slave_wr](axi5_slave_wr.md) — the boundary wrapper upstream of the
  filter in bridge master adapters
- [AXI5 index](README.md) — scope statement for the AXI5 family
