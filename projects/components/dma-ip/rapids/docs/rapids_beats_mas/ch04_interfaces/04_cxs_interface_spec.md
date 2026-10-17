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
# CXS Interface Specification

**Applies to:** `rapids_beats_cxs_top`, `rapids_cxs_top`
**Protocol:** Arm IHI 0079 (CXS) Issue D, one fixed profile
**Last Updated:** 2026-10-16

---

## Overview

The CXS tops replace the two AXIS network ports with one CXS link per
direction: the **sink port** `s_cxs_*` (a CXS receiver) into the sink half and
the **source port** `m_cxs_*` (a CXS transmitter) out of the source half. One link carries every channel; the
channel rides in `CXSSRCID`. The planes that implement the links are described
in the Network Planes chapter (Section 3.13).

## Link Profile

| Property | Value |
|----------|-------|
| Issue | D (the issue with SRCID, TGTID and USER) |
| `CXSMAXPKTPERFLIT` | 2 |
| Packet start alignment | 16 bytes; RAPIDS always starts a packet at byte 0 |
| Packet mapping | One AXIS packet (`tlast`-delimited) is one CXS packet |
| `CXSSRCID` | The channel (AXIS `tid`) |
| `CXSTGTID` | AXIS `tdest` |
| `CXSUSER` | `{tuser, tstrb}`; `tuser` dropped when `DATA_WIDTH/8 + AXIS_USER_WIDTH > 128` |
| Stream framing | Per stream on the channel bits of `CXSSRCID` |
| Link control | Explicit credit return, activation, deactivation |
| Parity | Off |

: Table 4.4.1: CXS Link Profile

## Signal Table

| Signal | Sink port | Source port | Width | Description |
|--------|-----------|-------------|-------|-------------|
| `{s,m}_cxs_valid` | in | out | 1 | Flit valid |
| `{s,m}_cxs_data` | in | out | `DATA_WIDTH` | Flit data |
| `{s,m}_cxs_cntl` | in | out | `CXS_CNTL_PW` | START / END / pointers |
| `{s,m}_cxs_srcid` | in | out | `AXIS_ID_WIDTH` | Channel |
| `{s,m}_cxs_tgtid` | in | out | `AXIS_DEST_WIDTH` | `tdest` |
| `{s,m}_cxs_user` | in | out | `CXS_UW` | `{tuser, tstrb}` |
| `{s,m}_cxs_crdgnt` | out | in | 1 | Credit grant (receiver to transmitter) |
| `{s,m}_cxs_crdrtn` | in | out | 1 | Credit return (transmitter to receiver) |
| `{s,m}_cxs_activereq` | in | out | 1 | Transmitter requests the link |
| `{s,m}_cxs_activeack` | out | in | 1 | Receiver acknowledges |
| `{s,m}_cxs_deacthint` | out | in | 1 | Receiver asks the transmitter to deactivate |
| `snk_cxs_link_state`, `src_cxs_link_state` | out | out | 2 | `{ACTIVEREQ, ACTIVEACK}` |
| `snk_cxs_protocol_error`, `src_cxs_protocol_error` | out | out | 1 | Sticky protocol violation |
| `snk_cxs_unsupported` | out | - | 1 | Sticky: a flit AXIS framing cannot carry |

: Table 4.4.2: CXS Interface Signals

## Credit Flow

One credit permits one flit (IHI 0079D 2.1). The receiver grants up to
`CXS_MAX_CREDIT` (default 32) credits, one per free entry in its receive FIFO,
so every flit sent against a credit has space. The transmitter spends one
credit per flit and returns the credits it still holds on deactivation. Credits are a single
pool for the link; a grant carries no ID and cannot be reserved for a channel.

The grant -> flit -> free round trip between the RAPIDS endpoints is about 3
cycles, so 32 credits sustains one flit per cycle with margin for pipeline
stages or a clock crossing on the link. More than 63 credits is beyond the
spec and requires `CXS_CREDIT_BEYOND_SPEC` on both ends.

## Link Activation

| Step | Transmitter (`m_cxs_*`) | Receiver (`s_cxs_*`) |
|------|-------------------------|----------------------|
| 1 | Raises `ACTIVEREQ` when it has a flit to send (and only once the previous activation's `ACTIVEACK` has fallen: 4-phase) | - |
| 2 | - | Raises `ACTIVEACK`; starts granting credits |
| 3 | Sends flits, one credit each | Frees an entry and regrants as the core drains |
| 4 | After `CXS_IDLE_CYCLES` idle cycles in RUN (or on `DEACTHINT`) drops `ACTIVEREQ`, then returns every held credit on `CRDRTN`, one per cycle | - |
| 5 | - | Drops `ACTIVEACK` once its credits are back |

: Table 4.4.3: Link Activation Sequence

## Backpressure

On the sink port, a full receive FIFO means no further grants: the transmitter
stalls for lack of credit. This is the CXS form of the AXIS sink's
`s_axis_tready = 0`, including the byte-granular sink's hold until a channel's
descriptor has been fetched. On the source port, the plane stalls the core's
egress (`fub_axis_tready = 0`) while it has no credit.

## Proposed Changes

A proposal (2026-10-16, not implemented) puts a tile packet header at the
front of every packet: destination and source coordinates, payload type
(`cfg` / `prog` / `mem`), length and target address. It is described once in
the compute-engine tile's [`TILE_SPEC.md`](../../../../../compute-eng-ip/tile/docs/TILE_SPEC.md) Section 11; CXS carries it
as the first flit. The link signals, credits and per-stream framing on this
page do not change, because `CXSSRCID` keeps the channel.
