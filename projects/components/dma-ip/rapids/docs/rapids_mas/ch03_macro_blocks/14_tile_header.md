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

**Modules:** `rapids_tile_hdr_rx.sv` (new), with header logic in `scheduler.sv`, `src_data_path_axis.sv` and `descriptor_engine_shared.sv`
**Location:** `projects/components/dma-ip/rapids/rtl/fub/`, `rtl/macro/`
**Status:** Implemented behind `TILE_HDR` = 1 (default 0)
**Last Updated:** 2026-10-17

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
its strobe is the low 16 bytes. Bits [127:118] are zero.

| Bits | Field | Source half fills it from |
|------|-------|---------------------------|
| [13:0] | Destination coordinate `{level, X, Y, Z}` | descriptor `dst_addr[63:50]` |
| [27:14] | Source coordinate | `TILE_SRC_COORD` (level 3, the tile I/O) |
| [30:28] | `ptype` | descriptor [215:213] |
| [31] | `op` (0 write, 1 read) | descriptor [216] |
| [63:32] | Length in bytes | descriptor `length` |
| [113:64] | Target address | descriptor `dst_addr[49:0]` |
| [117:114] | Tag | the issuing channel |

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
| `credit` | Consumed and counted (`TILE_COUNTS.CREDIT_COUNT`); end-to-end credits are rapids TASK-027 |
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

## Status Registers

`SNK.TILE_STATUS` (`UNSUPPORTED`, `TAG_MISMATCH`), `SRC.TILE_DESC_DROPPED`
(`DROPn`) and `SNK.TILE_COUNTS` (see the Register Map). The W1C fields are live
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

: Table 3.14.3: Tile Header Test Cells

`test_descriptor_engine_shared.py` `inject_owed_beat` covers the owed-beat
guard. Every cell was mutation-checked.
