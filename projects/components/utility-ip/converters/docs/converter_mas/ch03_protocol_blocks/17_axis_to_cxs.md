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

# 3.17 AXI-Stream to CXS Adapters

The **axis_to_cxs** and **cxs_to_axis** adapters let an AXI-Stream design use a credited CXS link (Arm IHI 0079, Issue D) without changing its stream logic. `axis_to_cxs` sits on the FUB side of a `cxs_master` and turns AXIS beats into CXS flits; `cxs_to_axis` sits on the FUB side of a `cxs_slave` and turns them back. The CXS endpoints and the rest of the CXS family are in `rtl/amba/cxs/` (`docs/markdown/rtl-amba/cxs/README.md`).

## 3.17.1 Module Organization

```
projects/components/utility-ip/converters/rtl/
  axis_to_cxs.sv    AXIS beats -> CXS flits, one packet per TLAST run
  cxs_to_axis.sv    CXS flits -> AXIS beats, CXS END -> TLAST
rtl/filelists/axis_to_cxs.f, cxs_to_axis.f
```

Both are combinational on the data path and pass the valid/ready handshake straight through, so neither adds a pipeline stage. `axis_to_cxs` keeps one flop per stream key (whether that stream has a packet open), and `cxs_to_axis` keeps one sticky flag. One AXIS beat is one CXS flit, and one TLAST-delimited AXIS packet is one CXS packet.

## 3.17.2 Field Mapping

| CXS field | From the AXIS beat |
|---|---|
| `CXSDATA` | `TDATA` |
| `CXSCNTL` START[0] | first beat of a stream's packet, START0PTR = 0 |
| `CXSCNTL` END[0] | the TLAST beat; END0PTR = the highest 4-byte word with any strobe set |
| `CXSSRCID` | `TID` |
| `CXSTGTID` | `TDEST` |
| `CXSUSER` | `{TUSER, TSTRB}` (`CARRY_TUSER = 1`) or `TSTRB` alone (`CARRY_TUSER = 0`) |

: Table 3.53: AXI-Stream to CXS field mapping

CXS packets end on a 4-byte boundary, but AXIS packets can end on any byte. Carrying `TSTRB` in `CXSUSER` keeps byte-exact framing across the link: `cxs_to_axis` restores `TSTRB` from the user bits, so a packet of any length or alignment comes out exactly as it went in. `ENDERROR` is never set. On the way back, TLAST is END[0] of the flit.

## 3.17.3 Interleaved Packets

AXIS may interleave packets of different `TID`/`TDEST`, and CXS lets flits of different streams (`CXSSRCID`/`CXSTGTID`) interleave too (IHI 0079D 2.5.2). So `axis_to_cxs` frames START per stream: one state bit per key built from the low `STREAM_ID_BITS` of `TID` and the low `STREAM_DEST_BITS` of `TDEST` (`cxs_stream_key`). The default 0/0 means the input never interleaves. The receiving `cxs_slave` must track the same streams (`CXS_STREAM_SRCID_BITS` / `CXS_STREAM_TGTID_BITS`). `cxs_to_axis` is stateless, so it needs no key.

## 3.17.4 Parameters

| Parameter | Default | Description |
|---|---|---|
| DATA_WIDTH | 512 | `TDATA` and `CXSDATAFLITWIDTH` (256 / 512 / 1024) |
| ID_WIDTH / DEST_WIDTH / USER_WIDTH | 8 / 4 / 1 | `TID` / `TDEST` / `TUSER`; 0 is legal |
| CXS_MAX_PKT_PER_FLIT | 2 | Sizes the `CXSCNTL` layout; must be at least 2 |
| CXS_START_ALIGN | 16 | `CXS_START_ALIGNMENT` in bytes |
| CARRY_TUSER | 1 | 0 leaves `TUSER` off the link, so `CXSUSER` = `TSTRB` only |
| STREAM_ID_BITS / STREAM_DEST_BITS | 0 / 0 | Per-stream framing key (`axis_to_cxs` only) |

: Table 3.54: AXI-Stream to CXS adapter parameters

Derived: `CXS_UW = DATA_WIDTH/8 + (CARRY_TUSER ? USER_WIDTH : 0)`. CXSUSER is at most 128 bits, so carrying strobes limits `DATA_WIDTH` to 1024, or to `8 * (128 - USER_WIDTH)` with `TUSER` carried. The link must be Issue D (`CXS_ISSUE = 4`), because the SRCID, TGTID and USER sidebands exist only there.

## 3.17.5 Limits

- `axis_to_cxs` never packs two packets into one flit. That costs some link efficiency on short packets, but it is what lets a flit map back onto a single AXIS beat.
- AXIS allows only one TLAST per beat, so `cxs_to_axis` handles only flits shaped the way `axis_to_cxs` makes them: at most one START and one END, and START at pointer 0. If a transmitter sends a flit with two packet boundaries, or a packet starting mid-flit, the sticky `unsupported` output is set. The beat is still forwarded, with TLAST taken from END[0].
- Parity (`Odd_Byte_Parity`) is not part of these adapters. Configure it on the endpoints.

## 3.17.6 Used By and Verification

| User | Path |
|---|---|
| RAPIDS CXS network planes | `projects/components/dma-ip/rapids/rtl/plane/rapids_plane_cxs_{tx,rx}.sv` |
| CXS pattern injector / checker | `rtl/amba/shared/cxs_master_injector.sv`, `cxs_slave_pattern_check.sv` |

: Table 3.55: AXI-Stream to CXS adapter users

They are verified through those users: `val/amba/test_cxs_pattern_pair.py` (every AXIS pattern-pair scenario, interleave included, across a CXS link with a wire monitor) and the RAPIDS CXS top suites (`rapids_cxs_top`, `rapids_beats_cxs_top`, including concurrent channels interleaved mid-packet).
