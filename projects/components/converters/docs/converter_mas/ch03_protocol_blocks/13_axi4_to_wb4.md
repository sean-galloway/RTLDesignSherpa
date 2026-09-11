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

# AXI4 to Wishbone B4

**Module:** `axi4_to_wb4.sv`
**Filelist:** `rtl/filelists/axi4_to_wb4.f` (`-f`'s the two AXI4-Lite decomposers and `axil4_to_wb4`)

## Overview

Full AXI4 completer in, Wishbone B4 requester out -- the Wishbone
counterpart of [`axi4_to_apb4_shim`](04_axi4_to_apb4.md), built entirely
from blocks this component already has:

| Stage | Block | Job |
| --- | --- | --- |
| 1 | [`axi4_to_axil4_wr`](02_axi4_to_axil4.md), [`axi4_to_axil4_rd`](02_axi4_to_axil4.md) | burst decomposition: one AXI4-Lite beat per AXI4 beat, response folding, ID/LAST bookkeeping |
| 2 | [`axil4_to_wb4`](10_axil4_to_wb4.md) | five AXI4-Lite channels to one Wishbone command stream and back, in-order termination |

: Table 3.39: axi4_to_wb4 stages

Every AXI4 beat becomes one Wishbone transfer: `WE` from the channel it came
on, `SEL` from `WSTRB`, `ADR` the beat's address. Termination maps `ACK` to
`OKAY`, `ERR` to `SLVERR`, `RTY` to `RTY_RESP` (`SLVERR` by default; AXI has
no retry, so a completer that wants retries handled needs a `wb4_retry`
between it and this block). Same address and data width on both sides; the
bridge's width converters sit in front when they differ.

The Wishbone side is B4 pipelined unless `CLASSIC = 1` (B4 standard mode);
match the completer -- the two do not mix (see the `rtl/amba/wb4` README).
`CTI`/`BTE` are driven CLASSIC/LINEAR: the decomposer issues one transfer at
a time and burst hints are advisory in B4.

## Parameters

| Parameter | Default | Description |
| --- | --- | --- |
| `AXI_ID_WIDTH`, `AXI_ADDR_WIDTH`, `AXI_DATA_WIDTH`, `AXI_USER_WIDTH` | 8, 32, 32, 1 | the AXI4 face; data width is also the Wishbone width |
| `SKID_DEPTH_AW/W/B/AR/R` | 2 | `axil4_to_wb4`'s channel skids |
| `CMD_DEPTH`, `RSP_DEPTH` | 4, 4 | `wb4_master` queues; `RSP_DEPTH` bounds transfers in flight on the bus |
| `SIDE_DEPTH` | 8 | direction queue in `axil4_to_wb4_core` (>= CMD + RSP) |
| `CLASSIC` | 0 | 0 = B4 pipelined, 1 = B4 standard |
| `RTY_RESP` | `2'b10` | AXI response for a Wishbone `RTY` |

: Table 3.40: axi4_to_wb4 parameters

## Verification

`dv/tests/test_axi4_to_wb4.py` with `dv/tbclasses/axi4_to_wb4_tb.py`: AXI4
master BFMs drive bursts of 1..16 beats into a `WB4Slave` whose
`status_hook` turns two address windows into `ERR` and `RTY`. Checked: an
N-beat burst is exactly N Wishbone transfers in address order, each landing
in the completer's memory, and the read burst returns it beat by beat;
`WSTRB` becomes `SEL` against a byte shadow; `ERR` folds to `SLVERR` and
`RTY` to `RTY_RESP` on both B and R with the port working after; fixed,
stalling and slow completer profiles; pipelined and classic builds.

## Related Modules

The bridge generator's slave adapter instantiates this for a slave port
declared `protocol = "wb4"` (BRIDGE-019), through `Axi4ToWb4Shim`, with
the same monitor-wrapper sandwich and response intercepts the APB shim
gets. Sign-off: `projects/components/bridge/dv/tests/test_bridge_2x2_wb4_paths.py`.

## Navigation

**Previous:** [APB to AXI4 (Requester)](12_apb_to_axi4.md)
**Next:** [Wishbone B4 to AXI4](14_wb4_to_axi4.md)
