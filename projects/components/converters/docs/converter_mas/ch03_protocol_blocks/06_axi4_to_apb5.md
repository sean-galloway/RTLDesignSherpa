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

# AXI4 to APB5 Shim

**Module:** `axi4_to_apb5_shim.sv`
**Filelist:** `rtl/filelists/axi4_to_apb5_shim.f` (-f's the APB4 shim's closure)

## Overview

APB5 keeps the APB4 transfer protocol — PSEL/PENABLE phases, PREADY,
PSLVERR are unchanged — and adds only sideband: requester-driven user
signals and completer-driven wakeup/user signals. So this block is a thin
**pin-superset wrapper** over [`axi4_to_apb4_shim`](04_axi4_to_apb4.md):
the entire protocol engine (CDC, cmd/rsp FIFOs, burst decomposition,
response assembly) is the APB4 shim instantiated unchanged, with all 58
ports and 18 parameters forwarded 1:1.

The APB5 additions on the requester surface:

| Signal | Dir | Handling |
| --- | --- | --- |
| `m_apb_PAUSER[APB_AUSER_WIDTH-1:0]` | out | tied `'0` — nothing upstream sources it (AXI USER bits do not map onto APB user semantics) |
| `m_apb_PWUSER[APB_WUSER_WIDTH-1:0]` | out | tied `'0` |
| `m_apb_PWAKEUP` | in | accepted and terminated |
| `m_apb_PRUSER[APB_RUSER_WIDTH-1:0]` | in | accepted and terminated |
| `m_apb_PBUSER[APB_BUSER_WIDTH-1:0]` | in | accepted and terminated |

User-signal widths default to 1. `rtl/amba/apb5/apb5_slave.sv` defaults
its own to 4, so the two do NOT line up out of the box — set
`APB_{A,W,R,B}USER_WIDTH` to match whatever completer you attach. The
signal set is otherwise pin-for-pin with that slave, including the
repo's convention that PWAKEUP rides completer→requester.

## Parameters

The width and depth parameters are the same as the APB4 shim's -- see
[Table 3.17](04_axi4_to_apb4.md) -- with the APB5 user-signal widths
(`APB_AUSER_WIDTH`, `APB_WUSER_WIDTH`, `APB_RUSER_WIDTH`, `APB_BUSER_WIDTH`)
added for the sideband above.

One parameter is inert and worth calling out so nobody wires a knob to it:

| Parameter | Type | Default | Description |
| --- | --- | --- | --- |
| `USE_2_PHASE_CDC` | bit | 1 | **Deprecated and ignored.** This shim forwards it to `apb5_slave_cdc`, which does not reference it either, so it has no effect at any level |

: AXI4 to APB5 Shim -- Inert Parameter

## Design Notes

Deriving the wrapper from the APB4 shim's actual port surface (rather
than reimplementing the conversion) means the APB4 engine's fixes and
its dependency closure are inherited automatically — the closure
filelist simply `-f`'s the APB4 shim's. When a future consumer needs
real PAUSER/PWUSER sourcing or PWAKEUP-gated clocking, those grow here
without touching the conversion core.

## Related Modules

The bridge generator instantiates this shim for `protocol = "apb5"`
slaves (BRIDGE-002 A5-3c) through the same component path as the APB4
shim — the `Axi4ToApbShim` component takes `protocol='apb5'` and wires
the five extra pairs. Verified by
`projects/components/bridge/dv/tests/test_bridge_1x2_rw_apb5.py`
(APB4 BFM legally drives the port: same transfer protocol).

---

**Next:** [PeakRDL Adapter](05_peakrdl_adapter.md)
