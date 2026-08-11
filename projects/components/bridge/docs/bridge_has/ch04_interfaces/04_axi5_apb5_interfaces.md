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

The bridge remains AMBA4-shaped internally — the crossbar fabric is always
AXI4 — but any master or slave port can be declared AMBA5. This chapter
covers the external surfaces; the mechanism lives in the MAS
([AMBA5 Boundary and Native Sideband](../../bridge_mas/ch02_blocks/10_amba5_boundary.md)).

## Declaring AMBA5 Ports

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
```

## AXI5 Port Surface

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
| `atomic` | `awatop[5:0]` | **Connectivity-gated** (store-class only) |
| `mte`, `chunking` | — | Rejected at config time (deferred) |

**Droppable sideband** passes natively end-to-end when both ends of a path
are AXI5, feature-enabled, and width-matched; on any other path it
terminates at the fabric boundary with a generation-time warning.

**Connectivity-gated features** are a config **error** unless *every*
connected path is native (AXI5 both ends, feature enabled both ends, data
widths matched — dwidth converters cannot carry per-beat sideband).
Dropping POISON silently would launder corrupted data; dropping ATOP would
turn an atomic into a plain write.

**Atomics are store-class only.** `AWATOP = 01xxxx` (AtomicStore) and plain
writes forward natively. Read-return classes (AtomicLoad `10xxxx`,
AtomicSwap/Compare `11000x`) return their data on the R channel of a path
the split-wr/rd fabric cannot route, so the master boundary's
`axi5_atomic_filter` answers them locally with **DECERR** — no slave-side
AW handshake, no memory side effect.

## APB5 Slave Surface

An `apb5` slave exposes the APB4 requester surface plus the APB5 sideband,
mirroring `rtl/amba/apb5/apb5_slave.sv` pin-for-pin:

| Direction | Signals |
|---|---|
| Requester → completer | APB4 set + `PAUSER`, `PWUSER` (driven `'0` — nothing upstream sources them) |
| Completer → requester | APB4 set + `PWAKEUP`, `PRUSER`, `PBUSER` (accepted and terminated) |

The transfer protocol is unchanged from APB4, so the `axi4_to_apb5_shim`
is a sideband wrapper over the APB4 conversion core; APB constraints
(rw-only, 32-bit data) apply unchanged.

## Interop Matrix

| Master \ Slave | axi4 | axi5 | apb / apb5 / axil |
|---|---|---|---|
| axi4 | native | base subset | via shim |
| axi5 | sideband drops (warning) | **native sideband** when width-matched | sideband drops (warning) |

Connectivity-gated features tighten the axi5→axi5 cell: they *require* it.
