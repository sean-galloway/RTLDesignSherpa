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

# Wishbone B4 to AXI4

**Module:** `wb4_to_axi4.sv`
**Filelist:** `rtl/filelists/wb4_to_axi4.f` (`-f`'s `wb4_to_axil4`'s closure)

## Overview

Wishbone B4 completer in, full AXI4 requester out -- the Wishbone
counterpart of [`apb4_to_axi4`](12_apb_to_axi4.md). [`wb4_to_axil4`](11_wb4_to_axil4.md)
does the work (`wb4_slave`, the in-order response merge, the AXI4-Lite
masters); this wrapper promotes its AXI4-Lite face to AXI4 the way any
AXI4-Lite requester is promoted in the fabric:

| Field | Value |
| --- | --- |
| `AxID` | `DEFAULT_ID` (constant; Wishbone has no ID) |
| `AxLEN`, `AxBURST`, `WLAST` | 0, INCR, 1 -- every transfer is one beat |
| `AxSIZE` | the full data width; `SEL` rides `WSTRB` unchanged |
| `AxPROT` | `AXIL_PROT` (Wishbone carries no protection bits) |
| `AxLOCK`, `AxCACHE`, `AxQOS`, `AxREGION`, USER | 0 (`AxCACHE` = `DEFAULT_CACHE`) |
| `BID`/`RID`, `RLAST`, response USER | dropped: one ID in use, one beat per read |

: Table 3.41: AXI4 fields the wrapper invents

`ERR` to the requester when the AXI response is `SLVERR` or `DECERR`
(Wishbone has one way to say either); `RTY` is never generated. The core's
`OUTSTANDING` (default 1) is how many commands it lets into the AXI side at
once -- B4 terminates in issue order, and above 1 a slow write at the head
holds back a read that finished behind it.

## Parameters

`ADDR_WIDTH`, `DATA_WIDTH`, `CMD_DEPTH`, `RSP_DEPTH`, `MAX_OUTSTANDING`,
`CLASSIC`, `OUTSTANDING`, `SKID_DEPTH_*`, `AXIL_PROT` are `wb4_to_axil4`'s
(Table 3.31); added here: `AXI_ID_WIDTH` (1), `AXI_USER_WIDTH` (1),
`DEFAULT_ID` (`'0`), `DEFAULT_CACHE` (`4'b0000`).

## Verification

`dv/tests/test_wb4_to_axi4.py` with `dv/tbclasses/wb4_to_axi4_tb.py`: a
`WB4Master` drives the completer surface, memory-backed AXI4 slave BFMs
answer, a monitor samples every AW/W/AR handshake. Checked: the single-beat
shape of every request, `SEL` to `WSTRB` against a byte shadow, the data
round trip (memory read directly and through a second transfer), the
completer's out-of-range `SLVERR` terminating `ERR` with nothing written
and the port working after, a slow completer, pipelined and classic builds.

## Related Modules

The bridge generator's master adapter instantiates this for a master port
declared `protocol = "wb4"` (BRIDGE-019) and feeds the ordinary
`axi4_slave_{wr,rd}` timing wrapper with its `m_axi` face, exactly as it
does `apb4_to_axi4` for an APB requester.

## Navigation

**Previous:** [AXI4 to Wishbone B4](13_axi4_to_wb4.md)
