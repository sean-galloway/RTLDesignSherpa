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

# AXIS to CXS Adapters

**Modules:** `axis_to_cxs.sv`, `cxs_to_axis.sv`
**Location:** `rtl/amba/cxs/`
**Filelists:** `rtl/amba/filelists/axis_to_cxs.f`, `rtl/amba/filelists/cxs_to_axis.f`
**Status:** New (2026-10-15)

---

## Overview

The two adapters let an AXI-Stream design use a CXS link without changing its stream logic. `axis_to_cxs` sits on the FUB side of a [`cxs_master`](cxs_master.md) and turns AXIS beats into CXS flits; `cxs_to_axis` sits on the FUB side of a [`cxs_slave`](cxs_slave.md) and turns them back. Both are combinational on the data path and pass the valid/ready handshake straight through, so neither adds a pipeline stage. `axis_to_cxs` keeps one flop (whether a packet is open), and `cxs_to_axis` keeps one sticky flag.

One AXIS beat is one CXS flit, and one TLAST-delimited AXIS packet is one CXS packet.

## Mapping

| CXS field | From the AXIS beat |
|---|---|
| `CXSDATA` | `TDATA` |
| `CXSCNTL` START[0] | first beat of a packet, START0PTR = 0 |
| `CXSCNTL` END[0] | the TLAST beat; END0PTR = the highest 4-byte word with any strobe set |
| `CXSSRCID` | `TID` |
| `CXSTGTID` | `TDEST` |
| `CXSUSER` | `{TUSER, TSTRB}` (`CARRY_TUSER = 1`) or `TSTRB` alone (`CARRY_TUSER = 0`) |

CXS packets end on a 4-byte boundary, but AXIS packets can end on any byte. Carrying `TSTRB` in `CXSUSER` keeps byte-exact framing across the link: `cxs_to_axis` restores `TSTRB` from the user bits, so a packet of any length or alignment comes out exactly as it went in. `ENDERROR` is never set.

## Parameters

| Parameter | Default | Description |
|---|---|---|
| DATA_WIDTH | 512 | `TDATA` and `CXSDATAFLITWIDTH` |
| ID_WIDTH / DEST_WIDTH / USER_WIDTH | 8 / 4 / 1 | `TID` / `TDEST` / `TUSER`; 0 is legal |
| CXS_MAX_PKT_PER_FLIT | 2 | Sizes the `CXSCNTL` layout; must be at least 2 |
| CXS_START_ALIGN | 16 | `CXS_START_ALIGNMENT` in bytes |
| CARRY_TUSER | 1 | 0 leaves `TUSER` off the link, so `CXSUSER` = `TSTRB` only |
| STREAM_ID_BITS / STREAM_DEST_BITS | 0 / 0 | low `TID` / `TDEST` bits that separate interleaved packets (`axis_to_cxs` only) |

Derived: `CXS_UW = DATA_WIDTH/8 + (CARRY_TUSER ? USER_WIDTH : 0)`. CXSUSER is at most 128 bits (Issue D), so carrying strobes limits `DATA_WIDTH` to 1024, or to `8 * (128 - USER_WIDTH)` with `TUSER` carried. The link must be configured for Issue D (`CXS_ISSUE = 4`) because the SRCID, TGTID and USER sidebands exist only there.

## Limits

- **Interleaved packets.** AXIS may interleave packets of different `TID`/`TDEST`, and CXS lets flits of different streams interleave (IHI 0079D 2.5.2). `axis_to_cxs` therefore keeps a START bit per stream key (`STREAM_ID_BITS` / `STREAM_DEST_BITS`), so each stream's first beat gets its START. The receiver must track the same streams (`cxs_slave` `CXS_STREAM_SRCID_BITS` / `CXS_STREAM_TGTID_BITS`). `cxs_to_axis` is stateless, so it needs no key.
- `axis_to_cxs` never packs two packets into one flit. That costs some link efficiency on short packets, but it is what lets a flit map back onto a single AXIS beat.
- AXIS allows only one TLAST per beat, so `cxs_to_axis` handles only flits shaped the way `axis_to_cxs` makes them: at most one START and one END, and START at pointer 0. If a transmitter sends a flit with two packet boundaries, or a packet starting mid-flit, the sticky `unsupported` output is set. The beat is still forwarded, with TLAST taken from END[0].
- Parity (`Odd_Byte_Parity`) is not part of these adapters. Configure it on the endpoints.

## Used By

The RAPIDS CXS network planes (`projects/components/dma-ip/rapids/rtl/plane/rapids_plane_cxs_{tx,rx}.sv`); see `projects/components/dma-ip/rapids/docs/rapids_planes.md`.
