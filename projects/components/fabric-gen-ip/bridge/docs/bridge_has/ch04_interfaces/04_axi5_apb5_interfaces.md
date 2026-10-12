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

# AXI5 and APB5 Interfaces (AMBA5 Support)

## Overview

The bridge is AXI4-shaped internally with every AXI5 feature the library
wrappers carry riding alongside in the channel structs — since bridge TASK-007 (was BRIDGE-018)
that includes Memory Tagging and read-data chunking, so there is no AXI5
signal an `axi5` port can present that the fabric cannot carry natively
to another `axi5` port. Any master or slave port can be declared AMBA5.
This chapter covers the external surfaces; the mechanism lives in the MAS
([AMBA5 Boundary and Native Sideband](../../bridge_mas/ch02_blocks/10_amba5_boundary.md)).

## Parameters

### Declaring AMBA5 Ports

AMBA5 is declared per port, in the TOML:

```toml
[[bridge.masters]]
name = "cpu_wr"
protocol = "axi5"
axi5_features = ["trace", "atomic"]   # optional; empty = base AXI5
# ... standard fields unchanged

[[bridge.slaves]]
name = "periph5"
protocol = "apb5"                      # APB5 peripheral via the apb5 shim
channels = "rw"                        # APB rules unchanged (rw-only, 32-bit)

[[bridge.masters]]
name = "lite5"
protocol = "axil5"                     # AXI5-Lite requester (bridge TASK-004, was BRIDGE-014)
id_width = 1                           # AWID/ARID: required on an AXI5-Lite Subordinate
axi5_features = ["user"]               # the one group with an AXI4 destination

[[bridge.masters]]
name = "apb5m"
protocol = "apb5"                      # APB5 requester (bridge TASK-004, was BRIDGE-014)
id_width = 0
addr_width = 32                        # the requester addresses the whole fabric
channels = "rw"
```

## Ports

### AXI5 Port Surface

An `axi5` port exposes the AXI4 signal set **minus AW/ARREGION** (AXI5
removed REGION) **plus** the enabled features' sideband signals. Disabled
features' signals are not exposed at all — the boundary wrapper ties them
off internally.

| Feature | Signals added | Class |
|---|---|---|
| `nsaid` | `aw/arnsaid[3:0]` | Droppable sideband |
| `trace` | `aw/artrace`, `btrace`, `rtrace` | Droppable sideband |
| `mpam` | `aw/armpam[10:0]` | Droppable sideband |
| `mecid` | `aw/armecid[15:0]` | Droppable sideband |
| `unique` | `aw/aridunq` in; `bidunq`, `ridunq` out (IHI 0022L A5.2) | Droppable sideband; the response indicators are regenerated at the master port (below) |
| `wakeup` | `awakeup` (one signal for both request channels, present on rd-only, wr-only and rw ports alike) | Not path sideband; see "AWAKEUP" below |
| `poison` | `wpoison`, `rpoison` | **Connectivity-gated** |
| `atomic` | `awatop[5:0]` | **Connectivity-gated**; read-return classes native on rw ports, DECERR on write-only ports |
| `mte` | `aw/artagop[1:0]`, `wtag`, `wtagupdate`, `btagmatch[1:0]`, `rtag` (tag buses are 4 bits per 16 bytes of data, `wtagupdate` one bit per 16 bytes; IHI 0022L A12.2 has no `AWTAG`, `BTAG` or `RTAGMATCH`, and `BTAGMATCH` encodes Table A12.14: `00` none, `01` separate, `10` fail, `11` pass) | **Connectivity-gated**; 128-bit ports or wider (bridge TASK-007, was BRIDGE-018) |
| `chunking` | `archunken`, `rchunkv`, `rchunknum[3:0]`, `rchunkstrb` (one bit per 128 bits of data) | Droppable sideband; 128-bit ports or wider (bridge TASK-007, was BRIDGE-018) |

### APB5 Slave Surface

An `apb5` slave exposes the APB4 requester surface plus the APB5 sideband,
mirroring `rtl/amba/apb5/apb5_slave.sv` pin-for-pin:

| Direction | Signals |
|---|---|
| Requester → completer | APB4 set + `PAUSER`, `PWUSER` (driven `'0` — nothing upstream sources them) + `PWAKEUP` (below) |
| Completer → requester | APB4 set + `PRUSER`, `PBUSER` (accepted and terminated) |

`PWAKEUP` is a **requester output** (IHI 0024E 3.7.2, Table 3-7). The bridge
port used to take it as an input, following a library convention that had the
direction backwards (GitHub #102 item 7). `axi4_to_apb5_shim` now drives it from
a flop of `PSEL`: glitch-free, high from the cycle after the Setup phase and
held through the PREADY cycle, so a completer that waits for `PWAKEUP` before
`PREADY` always receives it, and low when no transfer is in progress. 3.7.2
permits assertion during or after `PSEL`; the recommended one-cycle lead is not
available because the command queue that would predict a transfer is inside
the shared APB4 conversion core. No `*CHK` check signals are exposed (the port
is `Check_Type = False`).

The transfer protocol is unchanged from APB4, so the `axi4_to_apb5_shim`
is a sideband wrapper over the APB4 conversion core; APB constraints
(rw-only, 32-bit data) apply unchanged.

### AXI5-Lite Master Surface

An `axil5` master port (bridge TASK-004, was BRIDGE-014) exposes the AXI4-Lite requester set, the
AXI5-Lite ID (`awid`/`arid` in, `bid`/`rid` out, `id_width` bits -- required on
an AXI5-Lite Subordinate, IHI 0022L B2.1.5, so `id_width` must be at least 1),
and the **whole** AXI5-Lite optional set, every group whether or not it is enabled --
the same rule as the slave surface, so the boundary keeps one shape. The
directions flip relative to the slave table: requester-driven groups are
bridge inputs, completer-driven groups bridge outputs.

| Group | Signals | Behaviour |
|---|---|---|
| **ID** | `awid`, `arid` in; `bid`, `rid` out | reach the adapter's AXI4 face, ride the fabric inside `{master index, id}` and come back unchanged |
| **FORWARDED** (when enabled) | `awuser`, `wuser`, `aruser` (`user`) | reach the adapter's AXI4 face and ride the fabric to the slave |
| **TERMINATED inputs** | `aw/artrace`, `wpoison`; `awuser`/... when `user` is off | consumed at the bridge top (a reduction into an `_unused` wire), never floating |
| **TERMINATED outputs** | `btrace`, `rtrace`, `rpoison`; `buser`/`ruser` when `user` is off | driven `'0` |
| **Response USER** | `buser`, `ruser` with `user` on | connected, but read 0: the master adapters tie response-side USER (see the PRD) |

: AXI5-Lite sideband groups at an `axil5` master boundary

### APB5 Master Surface

An `apb5` master port makes the bridge the APB5 **completer**: the APB4 set
with the requester-driven signals as inputs and `PREADY/PRDATA/PSLVERR` as
outputs, plus `PAUSER`, `PWUSER`, `PWAKEUP` in and `PRUSER`, `PBUSER` out,
one bit each (the fabric USER width). `PAUSER[0]`/`PWUSER[0]` become
`awuser`/`aruser`/`wuser` on the fabric -- observable at an `axil5` slave
with `user` enabled. `PWAKEUP` is requester-driven (an input here, since
the bridge is the completer) and is accepted and terminated: the bridge never
waits for it. Behind the surface sits `apb5_to_axi4`
(`apb4_to_axi4` for `protocol = "apb"`), then the same AXI4 timing wrapper
an AXI4 master port gets; from there the port is an AXI4-Lite-shaped
single-beat requester and takes the wide-slave aligner toward wider slaves.
An unmapped address answers `PSLVERR` (the subtractive slave's DECERR folds
into APB's one error bit).

### AXI5-Lite Slave Surface

An `axil5` slave gets `axi4_to_axil5_{rd,wr}` at the boundary: the AXI4-Lite
conversion core plus the AXI5-Lite ID and optional signals. The signal set is
IHI 0022L B2.1.5 / Table B2.2: AXI5-Lite has **no** AxLOCK (no exclusive
access), AxMPAM, AxMECID, AxNSAID or xLOOP -- the bridge carried all five until
GitHub #102 item 3 -- and it **does** carry AWID/BID and ARID/RID. Because the
master side is AXI4, the rest splits three ways, and which group a signal
falls in is the whole story of what an AXI4 front end can and cannot express.

| Group | Signals | Behaviour |
|---|---|---|
| **ID** | `awid`, `arid` (request); `bid`, `rid` (response) | The fabric ID (`{master index, id}`, the crossbar ID width), carried across the converter and returned unchanged. |
| **FORWARDED** | `awuser`, `wuser`, `aruser` (request); `buser`, `ruser` (response) | AXI4 has an equivalent, passed straight through and returned to the master. AXI4 `AxLOCK` has nowhere to go: an exclusive access completes as a normal one with OKAY. |
| **TIED** | `awtrace`, `wpoison`, `artrace` | AXI5-Lite optional signals with no AXI4 source. The port exists and is driven to `'0` — never left floating. There is deliberately no `ENABLE_` knob: there is nothing it could switch between. |
| **TERMINATED** | `btrace`, `rtrace`, `rpoison` | Completer-driven, with nothing on the AXI4 side to return them to. Accepted and dropped. |

: AXI5-Lite sideband groups at an `axil5` slave boundary

## Functional Description

**Droppable sideband** passes natively end-to-end when both ends of a path
are AXI5, feature-enabled, and width-matched; on any other path it
terminates at the fabric boundary with a generation-time warning.

**Connectivity-gated features** are a config **error** unless *every*
connected path is native (AXI5 both ends, feature enabled both ends, data
widths matched — dwidth converters cannot carry per-beat sideband).
Dropping POISON silently would launder corrupted data; dropping ATOP would
turn an atomic into a plain write; dropping a tag operation would turn a
tagged write into an untagged one and a Match into a plain access, with
the requester none the wiser — so `mte` is gated the same way.

**Chunking is permission, not demand.** `ARCHUNKEN` tells the completer it
*may* return the burst in chunks; a completer that cannot simply returns
ordered data with `RCHUNKV` low, and every chunking requester must accept
that. So `chunking` is droppable: toward an AXI4 slave, or through a width
converter, the enable terminates with a generation-time warning and the
read completes unchunked. Toward an AXI5 slave that chunks, the enable and
the chunk fields ride the structs natively; the fabric never looks inside
them — it routes each R beat by ID and frees its tracking on `RLAST`
exactly as for an ordered burst, so chunks may arrive in any order the
completer chooses.

**Both need a 128-bit bus.** Tags are one per 16 bytes and chunks are 128
bits; the validator rejects `mte` or `chunking` on a narrower port
(`bridge_2x2_axi5_native` and `bridge_1x2_rd_axi5c` are the 128-bit
fixtures; MAS 7.1a lists what their tests check).

**Atomics depend on the port having a read path.** `AWATOP = 01xxxx`
(AtomicStore) and plain writes forward natively on any atomic-enabled
port. Read-return classes (AtomicLoad `10xxxx`, AtomicSwap/Compare
`11000x`) answer on the R channel with the AW's ID:

- On an **rw** master port they forward natively. The slave performs the
  operation and returns the location's original data on R; the bridge
  routes that beat back by ID (`axi5_atomic_rr_tracker` at the slave
  adapter, an extra AR->R tracking slot at the master adapter). Every
  connected atomic slave must be `rw` -- the validator rejects a
  write-only one, since it could never return the data.
- On a **write-only** master port there is nowhere to deliver the R beat,
  so the boundary's `axi5_atomic_filter` answers those classes locally
  with **DECERR** -- no slave-side AW handshake, no memory side effect.
  IHI 0022L A6.4.8 also requires the read data transfers to be sent even
  when the write response is an error; the filter generates them
  (GitHub #102 item 2), but a write-only port has no R channel to carry
  them, so the bridge accepts and **discards** them inside the filter
  (its `s_rready` is tied high, which also keeps its read-return queue from
  filling and stalling AW). The atomic therefore completes with DECERR on
  **B only**. A manager that issues a load-class atomic on a write-only
  port is outside the spec -- such a port has no read data channel to
  receive the result -- and **must not** issue them; the DECERR exists so a
  stray one cannot hang the port. To use load-class atomics, declare the
  port `rw`.

**Unique-ID indicators are regenerated, not routed back.** IHI 0022L A5.2
makes `BIDUNQ` equal the request's `AWIDUNQ`, `RIDUNQ` equal `ARIDUNQ`, and an
atomic's `RIDUNQ` equal its `AWIDUNQ`. The request indicator is droppable
sideband: an AXI4 slave, a dwidth converter, the subtractive DECERR slave and
the atomic filter's local response never see it. So the response indicators
do not ride the fabric; each AXI5 master port with `unique` keeps one bit per
ID, written at every AW (and AR, and read-return atomic AW) handshake and read
by `BID`/`RID`. A5.2 forbids an `AxIDUNQ=1` request while any same-ID request
is outstanding, and any request reusing an outstanding `AxIDUNQ=1` ID, so every
outstanding transaction of one ID carries the same indicator and the per-ID bit
is exact under any response order. On a write-only atomic port the table sits
on the wrapper side of the filter, so a local DECERR carries the right bit.

**AWAKEUP** (IHI 0022L A14.1.1, feature `wakeup`). A master port accepts
`AWAKEUP` and does not wait for it -- the bridge is always clocked, and a
Subordinate is permitted, not required, to wait. A wake-capable AXI5 slave
port drives `AWAKEUP` as the OR of (a) every connected wake-capable master's
request -- the master's `AWAKEUP` OR'd with requests held in its boundary
wrapper -- so the slave can wake before a request reaches it, which is the
A14.1.1 recommendation; the bridge cannot know which slave a request decodes
to before it arrives, so every connected wake-capable slave sees it; and (b)
the slave wrapper's own held requests, so `AWAKEUP` is high on every cycle the
port presents `AWVALID`, `WVALID` or `ARVALID` and stays high until the
handshake, as A14.1.1 requires -- including traffic from a master without
`AWAKEUP` (A14.1.1's "derive from AxVALID" fallback). Every term is a flop or
a top-level `AWAKEUP` input, so the OR is glitch-free (A14.1). It falls when
nothing is requested. The read and write halves of a port each produce a copy
and the port ORs them: `AWAKEUP` is one signal for both request channels.

**The tied group is the honest limit of an AXI4 front end.** MPAM partition
IDs, MECID encryption contexts and NSAID security IDs are properties of the
*originating* master; a bridge whose masters speak AXI4 has nowhere to learn
them, so an `axi5` slave reached from an `axi4` master sees zeros rather than
invented values. If a design needs real MPAM or MECID at the slave, the master
port has to be `axi5`, not `axi4`. (AXI5-Lite has no MPAM, MECID or NSAID at
all.)

**Sideband is held for the whole burst, not just the address beat.** AXI4
presents `AWID`/`AWUSER` once, with AW; AXI5-Lite needs them stable across
every beat that follows. The shims capture on the address handshake and hold:

```systemverilog
wire w_aw_accept = s_axi_awvalid && s_axi_awready;
wire [AXI_USER_WIDTH-1:0] w_awuser_sel = w_aw_accept ? s_axi_awuser
                                                     : r_held_awuser;
```

A combinational passthrough here is a real defect rather than a style
question: with two bursts in flight, burst A's later beats would carry burst
B's `AWUSER`.

### Interop Matrix

| Master \ Slave | axi4 | axi5 | apb / apb5 / axil | axil5 |
|---|---|---|---|---|
| axi4 | native | base subset | via shim | via shim, sideband TIED to `'0` |
| axi5 | sideband drops (warning) | **native sideband** when width-matched | sideband drops (warning) | forwarded where AXI4-expressible |
| axil / axil5 | single-beat AXI4 | single-beat AXI4 | via shim | ID and `user` forwarded end to end (axil5 master); rest tied |
| apb / apb5 | single-beat AXI4 | single-beat AXI4 | via shim (APB in, APB out) | `PAUSER[0]` visible as `awuser` (apb5 master) |

Connectivity-gated features tighten the axi5→axi5 cell: they *require* it.
