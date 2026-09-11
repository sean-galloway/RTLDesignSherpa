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

# AXI5 Atomic Read-Return Tracker

**Module:** `axi5_atomic_rr_tracker.sv`
**Location:** `rtl/amba/axi5/`
**Status:** Production Ready

---

## Overview

The AXI5 Atomic Read-Return Tracker gives a fabric the one piece of state it
is missing when a **read-return atomic** passes through it: which read data
channel, and which requester, an R beat belongs to when no AR was ever issued
for it.

AXI5 `AWATOP[5:0]` splits atomics into two classes by bit 5:

| AWATOP | Class | Response |
|---|---|---|
| `6'b01xxxx` | AtomicStore | B only |
| `6'b10xxxx` | AtomicLoad | B, **plus** the location's original data on **R** |
| `6'b11000x` | AtomicSwap / AtomicCompare | B, **plus** the original data on **R** |

The read-return classes answer on the **read** data channel using the **AW's
ID**. A fabric that splits its write and read paths (the bridge crossbar is
one) routes R beats with trackers that learn only from AR handshakes, so the
atomic's R beat matches nothing and is never delivered. `axi5_atomic_filter`
solves that at a boundary with no read path by refusing the classes. This
block solves it where a read path exists: it records the atomic at its AW
handshake and answers the R beat's routing question from its ID.

### Key Features

- Keyed on ID alone. AXI5 forbids an atomic from sharing its ID with any
  transaction outstanding from the same Manager, so within one requester's
  traffic a live ID is unambiguous
- Combinational lookup from the presented `RID`: `hit` says the beat is a
  tracked atomic's, `hit_data` says where it goes
- Allocate and release may land in the same cycle; they can never target the
  same slot, because release needs a live entry and allocate needs a free one
- `full` is a registered view. The caller must not allocate while it is set;
  in the bridge the slave adapter holds the atomic AW's `awready` on it
- No protocol state machine: a valid vector, two small arrays and two
  priority encoders

## Parameters

| Parameter | Default | Description |
|---|---|---|
| `AXI_ID_WIDTH` | 4 | Width of `alloc_id` / `lookup_id` |
| `DATA_WIDTH` | 1 | Width of the routing tag stored per entry (the bridge stores its master index) |
| `DEPTH` | 4 | Number of read-return atomics that may be outstanding at once |

### Derived Parameters (do not override)

| Derived parameter | Default expression |
|---|---|
| `IW` | `AXI_ID_WIDTH` |
| `DW` | `DATA_WIDTH` |

## Ports

| Group | Signals | Direction | Meaning |
|---|---|---|---|
| Allocate | `alloc`, `alloc_id`, `alloc_data` | in | An accepted read-return atomic AW: its ID and routing tag |
| | `full` | out | Every slot live; do not allocate |
| Lookup | `lookup_id` | in | The `RID` being presented |
| | `hit`, `hit_data` | out | This beat belongs to a tracked atomic, and its routing tag |
| Release | `release_beat` | in | The R handshake's last beat; frees the matching entry when `hit` is set, ignored otherwise |
| Clock/reset | `aclk`, `aresetn` | in | Single domain, active-low asynchronous reset |

## Functional Description

At a slave-side boundary the adapter connects `alloc` to the AW handshake
qualified by `AWATOP[5]`, `alloc_id` to `AWID`, and `alloc_data` to the
bridge's requester index for that AW. On the read side it presents `RID` on
`lookup_id`. When `hit` is set the adapter routes the beat by `hit_data` and
does **not** advance its in-order AR tracker; every other beat is routed by
that tracker exactly as before. `release_beat` is the R handshake on its last
beat, and the tracker frees the entry only if the beat was one of its own.

Two requesters may present the same ID at one Subordinate. That aliasing is a
property of the surrounding fabric, not of this block: the generated bridge
adapter reports it in simulation when an R beat matches both a tracked atomic
and the head of the in-order tracker.

---

## Timing Characteristics

This module is **sequential**: one `always_ff` block clocked on `aclk` with
active-low asynchronous reset `aresetn`. `hit` and `hit_data` are
combinational from `lookup_id` and the stored entries, so a beat is routable in
the cycle it is presented. An allocation is visible to lookup on the cycle
after its handshake.

---

## Usage Examples

Every parameter and port below is taken from the module declaration. This is
how the bridge's slave adapter instantiates it beside its in-order read FIFO:

```systemverilog
axi5_atomic_rr_tracker #(
    .AXI_ID_WIDTH (ID_WIDTH),
    .DATA_WIDTH   (BRIDGE_ID_WIDTH),
    .DEPTH        (8)
) u_atom_rd (
    .aclk         (aclk),
    .aresetn      (aresetn),
    .alloc        (xbar_awvalid && xbar_awready && xbar_awatop[5]),
    .alloc_id     (xbar_awid),
    .alloc_data   (xbar_bridge_id_aw),
    .full         (atom_full),
    .lookup_id    (xbar_rid),
    .hit          (atom_hit),
    .hit_data     (atom_bridge_id),
    .release_beat (xbar_rvalid && xbar_rready && xbar_rlast)
);

assign rid_bridge_id = atom_hit ? atom_bridge_id : rd_fifo_head;
assign rid_valid     = atom_hit || rd_fifo_nonempty;
```

## Verification

`val/amba/test_axi5_atomic_rr_tracker.py`: directed allocate / lookup /
release / fill-to-full / same-cycle allocate-and-release, then a random phase
against a dictionary model checked on every round, scaled by TEST_LEVEL. The
end-to-end path is exercised by the bridge fixture `bridge_1x2_rw_axi5a` and
its hand-written `test_bridge_1x2_rw_axi5a_atomics.py`.

## Related

- [`axi5_atomic_filter`](axi5_atomic_filter.md): the other half of the story,
  for a boundary that has no read path and must refuse the classes instead
- Bridge MAS, AMBA5 boundary chapter (BRIDGE-002 A5-3b)
