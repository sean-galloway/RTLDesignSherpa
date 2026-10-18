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

# Tile Packet Header

**Modules:** `rapids_tile_hdr_rx.sv` and `rapids_tile_credits.sv` (new), with header and credit logic in `scheduler.sv`, `src_data_path_axis.sv` and `descriptor_engine_shared.sv`
**Location:** `projects/components/dma-ip/rapids/rtl/fub/`, `rtl/macro/`
**Status:** Header behind `TILE_HDR` = 1, end-to-end credits behind `TILE_CREDITS` = 1 (both default 0)
**Last Updated:** 2026-10-18

---

## Overview

With `TILE_HDR` = 1, RAPIDS is the I/O of a compute-engine tile. Every packet on
the source port and the sink port starts with one header beat. The header and
its packing are defined in the tile's TILE_SPEC Section 11.5; this section
describes the RAPIDS hardware that builds and reads it. The network planes do
not change: on a CXS link the header is the data of the first flit of the
packet, which is what TILE_SPEC 11.6 asks of CXS, and an AXIS plane carries it
as the first beat in the same way.

`TILE_HDR` needs `SHARED_ENGINES` = 1, because cell-issued descriptors are
written into the shared descriptor engine's queues, and `DATA_WIDTH` >= 256, so
that a descriptor arrives in one beat. Both are elaboration-time checks.

## Header Beat

The header occupies bits [127:0] of its beat (`rapids_pkg::tile_hdr_pack`) and
its strobe is the low 16 bytes. Bits [127:119] are zero. A coordinate is 15
bits, `{ext, level, X, Y, Z}`: `ext` picks the node's internal ID (0, the node
itself) or its external ID (1, what is attached to it, such as a cell).

| Bits | Field | Source half fills it from |
|------|-------|---------------------------|
| [14:0] | Destination coordinate `{ext, level, X, Y, Z}` | descriptor `dst_addr[63:49]` |
| [29:15] | Source coordinate | `TILE_SRC_COORD` (level 3, the tile I/O) |
| [32:30] | `ptype` | descriptor [215:213] |
| [33] | `op` (0 write, 1 read) | descriptor [216] |
| [65:34] | Length in bytes | descriptor `length` |
| [114:66] | Target address | descriptor `dst_addr[48:0]` |
| [118:115] | Tag | the issuing channel |

: Table 3.14.1: Header Fields and Their Sources

## Source Half

**Scheduler.** It latches `ptype` and `op` with the descriptor and passes
`{op, ptype, dst_addr}` (`sched_rd_pkt_tile`) with the packet record it already
sends the source data path. A read request (`op` = 1) loads zero read beats, so
no memory is read, and completes like any data descriptor once its record is
queued. A source descriptor whose `ptype` is not `cfg`, `prog` or `mem` is refused
as an invalid descriptor (CH_ERROR): `credit` and `desc` packets are built by
the tile, never by a descriptor.

**Source data path.** The packet-record queue stores the tile fields beside the
byte length and offset. Before a packet's first data beat, the egress emits its
header from the head record:

- The output register takes, in priority order, a flush beat, a header beat,
  then a data pop.
- A data packet's header goes only when its first memory beat is at the drain
  stage, so header and payload leave back to back. Only the channel the drain
  stage is parked on can need a header, so it is served first.
- A header-only packet (read request) can go at any time. When it competes
  with a data pop, the two alternate, and header-only channels are scanned
  round-robin, so neither a run of read requests nor a long data packet starves
  the other.
- The header-only record is popped when its header leaves.

## Sink Half: `rapids_tile_hdr_rx`

The module sits between the sink plane and `snk_data_path_axis`. Packets are
framed per stream, and the stream is the TID (`CXSSRCID`, the channel), so the
"next beat is a header" state is kept per stream.

| Header | Action |
|--------|--------|
| `cfg` / `prog` / `mem`, `op` = 0 | Header dropped; payload beats to the sink data path unchanged, delivered by stream ID |
| `desc`, `op` = 0 | First payload beat [255:0] goes out on `desc_inj_*` with the tag as the source channel; never stored in the sink |
| `credit` | Consumed and counted (`TILE_COUNTS.CREDIT_COUNT`); `{source coordinate, op, count, class}` goes to the source half's counters on `credit_*` (used when `TILE_CREDITS` = 1) |
| Anything else | Consumed; sets `UNSUPPORTED`: a read request to RAPIDS, a reserved `ptype`, a `desc` with no payload or a tag past `NUM_CHANNELS`, extra `desc` payload, or `DATA_WIDTH` < 256 |

: Table 3.14.2: Sink-Port Packet Handling

Only data payload waits on the sink data path's `tready`. Header, `desc`,
`credit` and dropped beats are taken at once, so a full sink channel never holds
a descriptor or a credit behind it. A data packet whose tag differs from its
stream ID is still delivered by stream ID and sets `TAG_MISMATCH`.

## Cell-Issued Descriptors: `descriptor_engine_shared` (`INJ_EN`)

`desc_inj_*` is a single-cycle pulse with no backpressure. Each channel has a
one-descriptor slot:

- **Capture.** A descriptor for a channel whose slot is empty is captured. The
  chain decision (non-zero next pointer, not last, valid, in range) is taken
  once at capture, so one set of comparators serves every channel.
- **Write.** The slot is written into the channel's descriptor FIFO when the
  channel's fetch side is idle (`S_IDLE`), no R beat is owed from a fetch a
  channel reset aborted, and the FIFO has room. Idle means no fetch is in
  flight, so the R path never writes that FIFO in the same cycle and the
  injection never takes the entry an outstanding fetch needs.
- **Start and chain.** An idle channel starts on the descriptor as if kicked; a
  busy one runs it after what is already queued. A chaining descriptor moves
  the channel to `S_PEND` with its next pointer, and the chain continues from
  memory.
- **Kicks** wait while the slot is full.
- **Drops.** A descriptor that arrives while the slot is full, while the channel
  is held in reset, or of type EXT (its second chunk has no way in) is dropped
  and sets the channel's sticky drop bit. A drop is not a descriptor error:
  the channel and the work it holds carry on.

## End-to-End Credits: `rapids_tile_credits` (`TILE_CREDITS`)

With `TILE_CREDITS` = 1 (it needs `TILE_HDR` = 1), a packet leaves the source
port only when its destination has room for it (TILE_SPEC 11.9, 11.10). The
credits are end to end, between RAPIDS and the destinations. A delta node holds
no credit state for traffic passing through it. For packets addressed to it, it
is an endpoint like a cell.

**Counters.** The source half keeps 64 counters in flits, one per destination
index `{ext, n}` (`rapids_pkg::tile_dest_index`): the internal and the external
ID of every node. Only a node with something attached has external credit; an
external ID with nothing behind it never advertises and so is never legal.

| Index | Destination |
|-------|-------------|
| 0-15 | Cell-level node (internal), `{Y[1:0], X[1:0]}` |
| 16-19 | Tetrad node (internal), `{Y[0], X[0]}` of its group |
| 20-21 | Root node 0, 1 (internal) |
| 32-47 | Cell: the cell-level node's external ID |
| 48-51 | Tetrad control core: the tetrad node's external ID |
| others | Spare: never advertised, always illegal |

: Table 3.14.3: Credit Counter Index

A coordinate outside this map (the tile I/O itself, a cell past 4x4, a tetrad
past 2x2, a root past 1) has no index. Every counter starts at 0. A class-0
credit packet from an indexed coordinate fills it: `op` = 1 (`set`) replaces the
count and `op` = 0 (`add`) adds to it, saturating. Class-1 credits (descriptor
slots) and credits from a coordinate with no index are ignored.

**Advertisement window.** `rapids_tile_credits` counts cycles from reset up to
`SRC.TILE_ADV_WINDOW` (default 4096). When the window closes, every counter
still at 0 marks an illegal destination, and the 64-bit result is saved in
`SRC.TILE_LEGAL_DEST_LO` (internal IDs) and `_HI` (external IDs) until the next
reset. `SRC.TILE_CREDIT_STATUS.ADV_DONE`
reports the close. A later advertisement updates the count but never makes a
destination legal.

**Scheduler.** A tile data descriptor with a non-zero length waits in
`CH_FETCH_DESC` until the window closes. Its destination must then be legal (an
index whose bit is set in the mask), or the descriptor is refused as invalid
(CH_ERROR) and nothing is sent.

**Source data path.** Each channel asks for its head packet's flits, the header
and `ceil(bytes / beat)` data beats or the header alone for a read request,
against its destination (`tile_acq_*`). `rapids_tile_credits` grants one request
per cycle, round-robin, and only when the counter covers the whole packet. It
charges the counter in the same cycle and pulses `tile_acq_gnt` the next. Until
the grant, neither the packet's header nor any further SRAM reservation of the
channel goes ahead, so a channel waiting for credits does not hold the shared
drain stage. A reservation made under the previous packet can still run into
this one's first beat, and the drain stage then waits there for the grant.
Counters are per destination, so concurrent channels to one cell share its
buffer.

**Limits.** A channel reset that discards a packet whose credits are already
charged does not refund them. Sink-space grants to cells and descriptor-slot
grants (TILE_SPEC 11.9, 11.11) are not built: rapids TASK-027.

## Status Registers

`SNK.TILE_STATUS` (`UNSUPPORTED`, `TAG_MISMATCH`), `SRC.TILE_DESC_DROPPED`
(`DROPn`) and `SNK.TILE_COUNTS`, plus, for `TILE_CREDITS`, `SRC.TILE_ADV_WINDOW`
(RW), `SRC.TILE_LEGAL_DEST_LO` / `_HI` and `SRC.TILE_CREDIT_STATUS` (see the Register Map). The W1C fields are live
mirrors of stickies owned by the RTL. `rapids_top_base` decodes a write to
either register from the register block's own request and sends a one-cycle
clear (`wr_data & wr_biten`) to the owner, where a same-cycle event wins. The
same values are on the top-level `sts_tile_*` ports.

## Verification

`test_rapids_cxs_top.py` builds `rapids_cxs_top` (and `rapids_16ch_cxs_top`)
with `TILE_HDR` = 1:

| Cell | Proves |
|------|--------|
| `tile_source_write` | Header fields from the descriptor, ahead of the payload |
| `tile_source_read` | `op` = 1 is a header-only packet with no memory read |
| `tile_sink_write` | Header stripped, payload to memory |
| `tile_cell_descriptors` | Idle, busy and chaining injections on four channels (and channels 12-15 at 16) |
| `tile_desc_overflow` | A slot overflow drops, flags `DROPn` (and clears it by W1C); the running transfer and queued work finish |
| `tile_source_bad_ptype` | A source descriptor with `ptype` `credit` is refused |
| `tile_unsupported` | `credit` counted, a read request to RAPIDS flagged and cleared by W1C, the stream still carries data |
| `tile_credits[window]` | `TILE_CREDITS`: the legal mask from the advertisements; a zero and a late advertisement stay illegal; a descriptor kicked during the window waits for it |
| `tile_credits[no_oversend]` | A destination takes only what it advertised and returned; one flit short holds the packet; class-1 and unindexed credits change nothing |
| `tile_credits[shared_counter]` | Two channels to one cell share its counter (also on `rapids_16ch_cxs_top`) |
| `tile_credits[node]` | A tetrad node's counter covers `cfg` writes to it; a read request spends one flit |
| `tile_credits[illegal]` | Descriptors to an unadvertised, zero-advertised, out-of-map or tile-I/O destination, and to a legal cell's own (unadvertised) node, are refused; a legal one still goes |

: Table 3.14.4: Tile Header Test Cells

`test_descriptor_engine_shared.py` `inject_owed_beat` covers the owed-beat
guard. Every cell was mutation-checked.
