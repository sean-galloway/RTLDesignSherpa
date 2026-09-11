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

# APB to AXI4 (Requester)

**Modules:** `apb4_to_axi4.sv`, `apb5_to_axi4.sv`, `apb_cmdrsp_to_axi4.sv`
**Filelists:** `rtl/filelists/apb4_to_axi4.f`, `rtl/filelists/apb5_to_axi4.f` (each `-f`'s its `rtl/amba` APB completer and the shared requester core)

## Overview

The mirror of [AXI4 to APB](04_axi4_to_apb4.md). There an AXI4 requester is
turned into an APB requester; here an APB requester -- a small CPU, a debug
port, a register sequencer -- becomes an AXI4 requester. The bridge generator
puts one of these in front of a master port declared `protocol = "apb"` or
`"apb5"` (BRIDGE-014).

Two proven pieces and one small new one:

| Piece | Job |
| --- | --- |
| `apb4_slave` / `apb5_slave` (`rtl/amba`) | The APB completer surface: PSEL/PENABLE/PREADY handshake, skid-buffered cmd/rsp pair, the orphan-response guard |
| `apb_cmdrsp_to_axi4` | One command -> one single-beat AXI4 transaction -> one response |
| `apb4_to_axi4` / `apb5_to_axi4` | The wiring, and for APB5 the USER mapping |

: Table 3.35: APB-to-AXI4 requester pieces

APB is strictly one-outstanding, so there is never more than one AXI4
transaction in flight and the response needs no ID matching: every request
carries the constant `DEFAULT_ID`. `AW` and `W` are presented together and
each is held until its own handshake, so the requester is legal against a
completer that takes `W` before `AW` or the other way round.

```
pwrite=1 : AW + W (awlen=0, wlast=1)  ->  B  ->  rsp  (PSLVERR = bresp[1])
pwrite=0 : AR      (arlen=0)          ->  R  ->  rsp  (PRDATA, PSLVERR = rresp[1])
```

Both `SLVERR` and `DECERR` fold to `PSLVERR`: APB has one error bit, so a
requester cannot tell an unmapped address from a failing completer. `R` is
drained to `RLAST` even though every request asks for one beat, so a
completer that answers with more cannot wedge the port; only the first
beat's data is returned.

## Fields the requester invents

| Field | Value | Why |
| --- | --- | --- |
| `AxID` | `DEFAULT_ID` | APB has no ID; one value is enough with one transaction outstanding |
| `AxLEN` | 0 | one beat per transfer |
| `AxSIZE` | `$clog2(DATA_WIDTH/8)` | the full data width; `PSTRB` becomes `WSTRB` unchanged |
| `AxBURST` | INCR | |
| `AxCACHE` | `DEFAULT_CACHE` (device non-bufferable) | the natural attribute for a peripheral-bus requester |
| `AxPROT` | `PPROT` | forwarded |
| `AxLOCK`, `AxQOS`, `AxREGION` | 0 | |
| `WLAST` | 1 | |

: Table 3.36: AXI4 request fields from an APB transfer

## APB5 sideband

`apb5_to_axi4` maps the APB5 USER signals onto the AXI USER fields with a
plain size cast -- the low bits travel, anything wider is zero-filled or
dropped:

| APB5 | AXI4 |
| --- | --- |
| `PAUSER` | `awuser` / `aruser` |
| `PWUSER` | `wuser` |
| `buser` | `PBUSER` |
| `ruser` | `PRUSER` |

: Table 3.37: APB5 USER mapping

`PWAKEUP` is requester-driven (AMBA APB5, IHI 0024E) and is an **input**
here, accepted and terminated -- there is nothing on the AXI side for it to
become. `apb5_slave`'s own `PWAKEUP` output (its wake-up *request* toward
the requester) is left unconnected with `wakeup_request` tied low. Parity is
not part of this surface: `apb5_slave` is instantiated with
`ENABLE_PARITY=0` and its parity pins tied off, matching
[`axi4_to_apb5_shim`](06_axi4_to_apb5.md).

Inside the bridge the AXI USER width is 1, so one bit of `PAUSER` reaches
the fabric -- the same width the AXI5-Lite slave side exposes, which is how
an APB5 requester's user bit can be observed at an AXI5-Lite completer. The
return direction is not symmetrical: the bridge's master adapters tie
response-side USER to zero (see the bridge PRD), so `PBUSER`/`PRUSER` read 0
on a bridge port even though the converter itself carries them.

## Parameters

| Parameter | Default | Description |
| --- | --- | --- |
| `APB_ADDR_WIDTH` | 32 | `PADDR` and `AxADDR` width (one address space; no windowing) |
| `APB_DATA_WIDTH` | 32 | `PWDATA`/`PRDATA` and the AXI data width -- equal by construction |
| `AXI_ID_WIDTH` | 1 | width of the constant ID |
| `AXI_USER_WIDTH` | 1 | AXI USER width (APB4 wrapper drives 0) |
| `DEFAULT_ID` | `'0` | the ID on every request |
| `DEPTH` | 2 | cmd/rsp skid depth inside the APB completer |
| `APB_{A,W,R,B}USER_WIDTH` | 1 | APB5 only; independent of `AXI_USER_WIDTH` |

: Table 3.38: APB-to-AXI4 parameters

`DEFAULT_CACHE` on the core is not exposed by the wrappers; a consumer that
needs a different cache attribute instantiates `apb_cmdrsp_to_axi4` directly.

## Verification

`dv/tests/test_apb4_to_axi4.py` and `dv/tests/test_apb5_to_axi4.py` share
`dv/tbclasses/apb_to_axi4_tb.py`: an APB master BFM drives the completer
surface, memory-backed AXI4 slave BFMs answer the requester surface, and a
monitor samples every AW/W/AR handshake. Checked: the data round trip (the
completer's memory is read directly as well as through a second transfer,
so a converter echoing its own write data is caught), the single-beat shape
of every request, `PPROT`->`AxPROT`, `PSTRB`->`WSTRB` against a
byte-accurate shadow, out-of-range `SLVERR` folding to `PSLVERR` with
nothing written and the port working afterwards, the APB5 USER mapping in
both directions, and a slow completer holding `AW`/`W`/`AR` to their
handshakes. Twelve cells at FULL (data widths 16/32/64, AXI USER 1/2/4,
APB USER 2/4).

## Related Modules

The bridge generator's master adapter instantiates `apb4_to_axi4` /
`apb5_to_axi4` for `protocol = "apb"` / `"apb5"` master ports and feeds the
result to the same `axi4_slave_{wr,rd}` timing wrapper an AXI4 master port
gets, so decode, width adaptation (including the wide-slave aligner) and
the response mux are untouched. Sign-off:
`projects/components/bridge/dv/tests/test_bridge_2x3_apb_req_paths.py`.

## Navigation

**Previous:** [Wishbone B4 to AXI4-Lite](11_wb4_to_axil4.md)
