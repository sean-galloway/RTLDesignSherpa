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

The bridge remains AMBA4-shaped internally — the crossbar fabric is always
AXI4 — but any master or slave port can be declared AMBA5. This chapter
covers the external surfaces; the mechanism lives in the MAS
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
protocol = "axil5"                     # AXI5-Lite requester (BRIDGE-014)
id_width = 0                           # Lite has no ID pins
axi5_features = ["user", "exclusive"]  # the two groups with an AXI4 destination

[[bridge.masters]]
name = "apb5m"
protocol = "apb5"                      # APB5 requester (BRIDGE-014)
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
| `unique` | `aw/arunique` | Droppable sideband |
| `poison` | `wpoison`, `rpoison` | **Connectivity-gated** |
| `atomic` | `awatop[5:0]` | **Connectivity-gated**; read-return classes native on rw ports, DECERR on write-only ports |
| `mte`, `chunking` | — | Rejected at config time (deferred) |

### APB5 Slave Surface

An `apb5` slave exposes the APB4 requester surface plus the APB5 sideband,
mirroring `rtl/amba/apb5/apb5_slave.sv` pin-for-pin:

| Direction | Signals |
|---|---|
| Requester → completer | APB4 set + `PAUSER`, `PWUSER` (driven `'0` — nothing upstream sources them) |
| Completer → requester | APB4 set + `PWAKEUP`, `PRUSER`, `PBUSER` (accepted and terminated) |

The transfer protocol is unchanged from APB4, so the `axi4_to_apb5_shim`
is a sideband wrapper over the APB4 conversion core; APB constraints
(rw-only, 32-bit data) apply unchanged.

### AXI5-Lite Master Surface

An `axil5` master port (BRIDGE-014) exposes the AXI4-Lite requester set plus
the **whole** AXI5-Lite sideband, every group whether or not it is enabled --
the same rule as the slave surface, so the boundary keeps one shape. The
directions flip relative to the slave table: requester-driven groups are
bridge inputs, completer-driven groups bridge outputs.

| Group | Signals | Behaviour |
|---|---|---|
| **FORWARDED** (when enabled) | `awlock`/`arlock` (`exclusive`); `awuser`, `wuser`, `aruser` (`user`) | reach the adapter's AXI4 face and ride the fabric to the slave |
| **TERMINATED inputs** | `aw/arloop`, `aw/armpam`, `aw/armecid`, `aw/arnsaid`, `aw/artrace`, `wpoison`; `awlock`/`awuser`/... when their feature is off | consumed at the bridge top (a reduction into an `_unused` wire), never floating |
| **TERMINATED outputs** | `bloop`, `btrace`, `rloop`, `rtrace`, `rpoison`; `buser`/`ruser` when `user` is off | driven `'0` |
| **Response USER** | `buser`, `ruser` with `user` on | connected, but read 0: the master adapters tie response-side USER (see the PRD) |

: AXI5-Lite sideband groups at an `axil5` master boundary

### APB5 Master Surface

An `apb5` master port makes the bridge the APB5 **completer**: the APB4 set
with the requester-driven signals as inputs and `PREADY/PRDATA/PSLVERR` as
outputs, plus `PAUSER`, `PWUSER`, `PWAKEUP` in and `PRUSER`, `PBUSER` out,
one bit each (the fabric USER width). `PAUSER[0]`/`PWUSER[0]` become
`awuser`/`aruser`/`wuser` on the fabric -- observable at an `axil5` slave
with `user` enabled. `PWAKEUP` is requester-driven and is accepted and
terminated. Behind the surface sits `apb5_to_axi4`
(`apb4_to_axi4` for `protocol = "apb"`), then the same AXI4 timing wrapper
an AXI4 master port gets; from there the port is an AXI4-Lite-shaped
single-beat requester and takes the wide-slave aligner toward wider slaves.
An unmapped address answers `PSLVERR` (the subtractive slave's DECERR folds
into APB's one error bit).

### AXI5-Lite Slave Surface

An `axil5` slave gets `axi4_to_axil5_{rd,wr}` at the boundary: the AXI4-Lite
conversion core plus the AXI5-Lite sideband. Because the master side is AXI4,
the sideband splits three ways, and which group a signal falls in is the whole
story of what an AXI4 front end can and cannot express.

| Group | Signals | Behaviour |
|---|---|---|
| **FORWARDED** | `awlock`, `awuser`, `wuser`, `arlock`, `aruser` (request); `buser`, `ruser` (response) | AXI4 has an equivalent, passed straight through and returned to the master. |
| **TIED** | `awloop`, `awmecid`, `awmpam`, `awnsaid`, `awtrace`, `wpoison` (and the AR equivalents) | AXI5 additions with no AXI4 source. The port exists and is driven to `'0` — never left floating. There is deliberately no `ENABLE_` knob: there is nothing it could switch between. |
| **TERMINATED** | `bloop`, `btrace` (and the R equivalents) | Completer-driven, with nothing on the AXI4 side to return them to. Accepted and dropped. |

: AXI5-Lite sideband groups at an `axil5` slave boundary

## Functional Description

**Droppable sideband** passes natively end-to-end when both ends of a path
are AXI5, feature-enabled, and width-matched; on any other path it
terminates at the fabric boundary with a generation-time warning.

**Connectivity-gated features** are a config **error** unless *every*
connected path is native (AXI5 both ends, feature enabled both ends, data
widths matched — dwidth converters cannot carry per-beat sideband).
Dropping POISON silently would launder corrupted data; dropping ATOP would
turn an atomic into a plain write.

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

**The tied group is the honest limit of an AXI4 front end.** MPAM partition
IDs, MECID encryption contexts and NSAID security IDs are properties of the
*originating* master; a bridge whose masters speak AXI4 has nowhere to learn
them, so it drives zeros rather than inventing values. If a design needs real
MPAM or MECID at the slave, the master port has to be `axi5`, not `axi4`.

**Sideband is held for the whole burst, not just the address beat.** AXI4
presents `AWUSER`/`AWLOCK` once, with AW; AXI5-Lite needs them stable across
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
| axil / axil5 | single-beat AXI4 | single-beat AXI4 | via shim | `user`/`exclusive` forwarded end to end (axil5 master); rest tied |
| apb / apb5 | single-beat AXI4 | single-beat AXI4 | via shim (APB in, APB out) | `PAUSER[0]` visible as `awuser` (apb5 master) |

Connectivity-gated features tighten the axi5→axi5 cell: they *require* it.
