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
- **Hold (`INJ_HOLD`, `TILE_CREDITS` = 1).** `inj_*` becomes a valid/ready
  handshake from the descriptor intake queue (below). A descriptor for a channel
  whose slot is full waits (`inj_ready` low) instead of being dropped; one for a
  channel in reset, or an EXT one, is still taken and dropped.

## End-to-End Credits: `rapids_tile_credits` (`TILE_CREDITS`)

With `TILE_CREDITS` = 1 (it needs `TILE_HDR` = 1), a packet leaves the source
port only when its destination has room for it (TILE_SPEC 11.9, 11.10). The
credits are end to end, between RAPIDS and the cells and control cores. A delta
node only transports: it never originates a packet, so it never advertises or
returns credits, and it consumes what is addressed to it on arrival.

**Counters.** The source half keeps 64 counters in flits, one per destination
index `{ext, n}` (`rapids_pkg::tile_dest_index`): the internal and the external
ID of every node. Only the external IDs carry credits: a node's internal ID is
legal by topology, and a packet to it is never held for credits or charged. An
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
past 2x2, a root past 1) has no index. Every external counter starts at 0. A
class-0 credit packet from an external ID fills it: `op` = 1 (`set`) replaces
the count and `op` = 0 (`add`) adds to it, saturating. Class-1 credits
(descriptor entries), credits carrying a node's internal ID and credits from a
coordinate with no index are ignored.

**Advertisement window.** `rapids_tile_credits` counts cycles from reset up to
`SRC.TILE_ADV_WINDOW` (default 4096). When the window closes, every node index
is legal and every external counter still at 0 marks an illegal destination,
and the 64-bit result is saved in
`SRC.TILE_LEGAL_DEST_LO` (internal IDs) and `_HI` (external IDs) until the next
reset. `SRC.TILE_CREDIT_STATUS.ADV_DONE`
reports the close. A later advertisement updates the count but never makes a
destination legal.

**Scheduler.** A tile data descriptor with a non-zero length waits in
`CH_FETCH_DESC` until the window closes. Its destination must then be legal (an
index whose bit is set in the mask), or the descriptor is refused as invalid
(CH_ERROR) and nothing is sent. A read request to a node's internal ID is
refused the same way, with or without `TILE_CREDITS`: a node never replies.

**Source data path.** Each channel asks for its head packet's flits, the header
and `ceil(bytes / beat)` data beats or the header alone for a read request,
against its destination (`tile_acq_*`). `rapids_tile_credits` grants one request
per cycle, round-robin, and only when the counter covers the whole packet. It
charges the counter in the same cycle and pulses `tile_acq_gnt` the next. A
request to a node is granted without a count check and charges nothing. Until
the grant, neither the packet's header nor any further SRAM reservation of the
channel goes ahead, so a channel waiting for credits does not hold the shared
drain stage. A reservation made under the previous packet can still run into
this one's first beat, and the drain stage then waits there for the grant.
Counters are per destination, so concurrent channels to one cell share its
buffer.

**Limits.** A channel reset that discards a packet whose credits are already
charged does not refund them. With `TILE_CREDITS` a channel reset acts only
while the tile is quiescent (below), when no packet is in flight against a
charge, so the case does not arise under the quiescent rule.

## Straps Toward RAPIDS (`TILE_CREDITS`)

What a cell or control core sends into the sink port is charged against a strap
RAPIDS reserves, and RAPIDS returns the credit as it consumes (TILE_SPEC 11.9,
11.11). The straps are fixed by construction, not granted: a sender starts
from its strap after reset. They are Hive-level parameters that the cells and
cores must be built with too.

| Sender (external slot = index - 32) | Strap | Reserved in RAPIDS | Returned when |
|---|---|---|---|
| Cell, slots 0-15 | `TILE_LAND_FLITS` flits (default 16), header included | A landing space of `TILE_LAND_FLITS` beats | Each beat leaves the landing space; the header when it is decoded |
| Control core, slots 16-19 | `TILE_DESC_PER_CORE` entries (default 2), credit class 1 | A share of the intake queue (`4 x TILE_DESC_PER_CORE` deep) | The descriptor moves into the descriptor queue |

: Table 3.14.4: Straps toward RAPIDS

**Header decode (`rapids_tile_hdr_rx`, `STRAPS`).** The sender is the header's
source coordinate as an external slot (`rapids_pkg::tile_ext_slot`). Data
payload goes on with the sender's cell slot to the landing space; the header
flit returns at once. A packet the decode drops (a read request into RAPIDS, a
reserved `ptype`) returns every beat. A `desc` packet refused at its header
returns its entry. A data packet from a sender with no landing space (not a
cell) is dropped and flagged `UNSUPPORTED`, and returns nothing: it was charged
to no strap. Credit packets are never charged.

**Landing space (`rapids_tile_landing`, in `rapids_snk`).** One FIFO of
`TILE_LAND_FLITS` beats per cell, holding payload by sender. A cell under its
strap can never fill its FIFO, so the sink port never waits on a landing space.
The drain moves one whole packet at a time into `snk_data_path_axis`,
round-robin over the cells. A packet is a candidate once its `tlast` beat has
landed, so the drain never waits on the network, and only when its channel can
take all of it now: `snk_data_path_axis` `chan_can_take` says the channel is out
of reset, has the packet's record (its descriptor is running), no spill is
waiting, and `TILE_LAND_FLITS + 4` beats are free (the packet, a spill and what
the previous packet may still hold in the shifter). A packet for a disabled
channel is drained and thrown away. A cell whose channel has no descriptor yet
holds only its own landing space; every other cell's data keeps flowing. Each
beat that leaves, delivered or thrown away, returns one flit. A beat arriving
for a full landing space (a cell past its strap) waits and sets
`TILE_CREDIT_STATUS.LAND_OVERRUN`. The per-channel sink SRAM must be at least
`TILE_LAND_FLITS + 4` beats (an elaboration check).

**Descriptor intake (`rapids_tile_desc_intake`, in `rapids_core`).** `desc`
packets go into a FIFO `4 x TILE_DESC_PER_CORE` deep with their channel and
sender, and leave in order through the `INJ_HOLD` handshake into
`descriptor_engine_shared`. A descriptor for a busy channel at the head waits
there; the schedulers' two-deep descriptor skid keeps that short. When an entry
leaves, its class-1 credit returns. A `desc` arriving at a full queue (a core
past its strap) is dropped, sets `TILE_CREDIT_STATUS.INTAKE_OVERRUN`, and still
returns its entry: no path consumes a descriptor silently.

**Credit returns (`rapids_tile_credit_tx`, in `rapids_core`).** Pending returns
are kept per external slot and class and taken round-robin into one output
register as soon as it is free; whatever arrives while a return waits is
coalesced into that slot's next one, and nothing is held back to build a batch.
A return is a header-only credit packet (`ptype` = `credit`, `op` = `add`, count
in the length, class in target bits [1:0]) addressed to the sender's source
coordinate as last seen in a header, on its own interface, `m_tile_credit_*`
(valid/ready, the 128-bit header): a return never waits behind data.
`TILE_CREDIT_STATUS.RET_COUNT` counts them.

**Resync (TILE_SPEC 11.10).** A write of `SRC.TILE_RESYNC.GO` requests one; it
is taken only while the top-level `tile_quiescent` input is high and waits for
it otherwise (`TILE_CREDIT_STATUS.RESYNC_BUSY`). It then sends one `set` per
legal sender in the saved mask: `TILE_LAND_FLITS` (class 0) to each cell and
`TILE_DESC_PER_CORE` (class 1) to each control core, replacing that slot's
pending `add`. Sets go before adds. RAPIDS sends one `set` per sender rather
than the multicast TILE_SPEC 11.10 describes: it has no multicast header to
build. The answering advertisements refill RAPIDS's own counters as at boot.

**Quiescent gating.** With `TILE_CREDITS`, a channel reset of either half
(`CHANNEL_RESET`) acts only while `tile_quiescent` is high; a reset bit written
while it is low has no effect until it rises.

**Stalled-data checks (`rapids_tile_stall_mon`).** Data that stops moving is a
monitor error (TILE_SPEC 11.9, hazard rules). Each half carries one check, on
the spare client 2 of its MonBus arbiter:

| Half | Pending | Moves on | Agent |
|---|---|---|---|
| Sink | The channel's sink SRAM holds data not yet written out (an allocated, unfilled segment does not count) | A W beat of the channel | `0x0B` |
| Source | The channel has read bursts outstanding (AR accepted, RLAST not seen; ARID low bits = channel) | An R beat for the channel | `0x0C` |

: Table 3.14.5: Stalled-data checks

A channel pending for `SRC.TILE_STALL_CYCLES` cycles (default 1000, 10 us at
100 MHz; 0 turns both off) with no movement raises one error packet
(`PktTypeError`, `PROTOCOL_CORE`, `RAPIDS_EVENT_STALL`; event data bit 32 = 0
sink / 1 source, bits [31:0] the threshold) and sets its bit in that half's
`TILE_STALLED`, and raises nothing more until the data moves or drains.

## Ordering Across the Fabric (open: delta DELTA-013)

Delta is moving to multi-path route tables, with failover as a table write
(delta HAS ch07, Resilient Routing: Open Hazards). A request and its reply
can then take different paths with different latencies, so delta guarantees
the order of flits within one packet and nothing between packets. RAPIDS
must not rely on fabric order. Under correct configuration, four places would;
O4's rule is decided (2026-10-19), the rest are open:

| # | Where | Mechanism | Candidate direction |
|---|---|---|---|
| O1 | Read replies | The tag is the sink channel only. Two reads outstanding on one sink channel, to different cells or to one cell over two paths, can reply in either order, and the sink lands the bytes in arrival order | A transaction ID per read, echoed in the reply, and the sink places by ID (AXI-ID style), or one read outstanding per sink channel |
| O2 | Credit `set` vs `add` | A resync `set` (TILE_SPEC 11.10) can overtake, or be overtaken by, an `add` sent before it, and the counter ends wrong | A sequence or epoch on credit packets; an `add` older than the last `set` is discarded |
| O3 | Write, then a dependent packet | A cell's data write and a later packet that depends on it (a `desc` whose source is that data, a flag) can arrive in either order | Completion is signalled (the credit return says the data was consumed), never implied by send order |
| O4 | Writes from one cell to one sink channel | The sink lands a channel's data in arrival order, so a cell's later write that overtakes an earlier one lands in the wrong place | Built on the delta assumption that packets never interleave on a link (delta HAS, Interface Assumptions): the cell sends its next packet only once RAPIDS has returned at least one flit of the previous one. RAPIDS returns a packet's header credit when the header lands and never returns a flit it has not received, so with returns counted, `returned >= flits sent before the last packet + 1` proves the last packet arrived. No RAPIDS change; coalesced returns still count |

: Table 3.14.6: RAPIDS ordering hazards under multi-path routing

The flits of one packet stay in order, so the header-then-payload framing of
the source and sink halves is unaffected.

## Status Registers

`SNK.TILE_STATUS` (`UNSUPPORTED`, `TAG_MISMATCH`), `SRC.TILE_DESC_DROPPED`
(`DROPn`) and `SNK.TILE_COUNTS`, plus, for `TILE_CREDITS`, `SRC.TILE_ADV_WINDOW`
(RW), `SRC.TILE_LEGAL_DEST_LO` / `_HI`, `SRC.TILE_CREDIT_STATUS` (`ADV_DONE`,
`RESYNC_BUSY`, `LAND_OVERRUN`, `INTAKE_OVERRUN`, `RET_COUNT`), `SRC.TILE_RESYNC`
(`GO`, singlepulse), `SRC.TILE_STALL_CYCLES` (RW), `SRC` / `SNK.TILE_STALLED` and
`TILE_STRAPS` (see the Register Map). `TILE_STRAPS` is the last config word of
each half, 0x7FC below the monitor block (`SRC` 0x07FC, `SNK` 0x17FC, on the 8-
and 16-channel maps alike), so the Hive finds it without the rest of the map:
`LAND_FLITS` [15:0] = `TILE_LAND_FLITS` and `DESC_PER_CORE` [31:16] =
`TILE_DESC_PER_CORE`, both 0 when `TILE_CREDITS` = 0. The W1C fields are live
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
| `tile_credits[window]` | `TILE_CREDITS`: every node legal unadvertised, node credits ignored; the cells and core that advertise are legal; a zero and a late advertisement stay illegal; a descriptor kicked during the window waits for it |
| `tile_credits[no_oversend]` | A destination takes only what it advertised and returned; one flit short holds the packet; class-1 and unindexed credits change nothing |
| `tile_credits[shared_counter]` | Two channels to one cell share its counter (also on `rapids_16ch_cxs_top`) |
| `tile_credits[node]` | `cfg` writes to an unadvertised tetrad node go out uncharged; its control core stays illegal; a read request to the node is refused |
| `tile_credits[illegal]` | Descriptors to an unadvertised cell or core, a zero-advertised cell, an out-of-map or the tile-I/O destination are refused; one to a legal cell and one to that cell's node still go |
| `tile_straps[land]` | A cell streams past its strap into one channel: every packet lands, the cell keeps going only on the returns, every flit (header included) comes back, the first promptly |
| `tile_straps[isolation]` | A cell whose channel has no descriptor holds only its own landing space: another cell's packets land meanwhile; the waiting data drains once the descriptors arrive (also on `rapids_16ch_cxs_top`) |
| `tile_straps[discard]` | A disabled channel's data, a read request into RAPIDS and a reserved `ptype` are consumed and return every flit; a core's data packet returns none; the channel works afterwards |
| `tile_straps[coalesce]` | Returns held by `m_tile_credit_ready` leave as the held one plus one coalesced `add` |
| `tile_straps[intake]` | Core descriptors under the strap all run, in order per channel, none dropped, one class-1 entry back each |
| `tile_straps[intake_overrun]` | A flood past the intake queue: `INTAKE_OVERRUN`, every entry returned, the descriptor queue drops none, the survivors run in send order |
| `tile_straps[resync]` | A resync waits for `tile_quiescent`, then sets exactly the legal cells (`TILE_LAND_FLITS`) and core (`TILE_DESC_PER_CORE`) |
| `tile_straps[quiescent_reset]` | A channel reset written while not quiescent does nothing; written while quiescent it clears the channel's error |
| `tile_strap_regs[off]` / `[default]` / `[alt]` | `TILE_STRAPS` sits at 0x7FC in both halves and reads 0 / 16, 2 / 8, 1 (also on `rapids_16ch_cxs_top`) |
| `tile_straps_alt[land]` / `[isolation]` / `[intake]` | The straps hold in a `TILE_LAND_FLITS` = 8, `TILE_DESC_PER_CORE` = 1 build, with the senders modelling the same straps |
| `tile_straps[stall_sink]` / `[stall_source]` | Held WREADY / late R data raise one MonBus stall record (agent, channel, kind, threshold) and the `TILE_STALLED` bit, which clears when the data moves; the data then lands / goes out correctly |

: Table 3.14.7: Tile Header Test Cells

`test_descriptor_engine_shared.py` `inject_owed_beat` covers the owed-beat
guard. Every cell was mutation-checked.
