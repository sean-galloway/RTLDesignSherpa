# TASK-025: CXS planes frame per stream; credits default to the channel SRAM

**Priority:** P1
**Status:** closed 2026-10-16
**Owner:** sean galloway

One CXS link per direction, CXSSRCID = channel (owner 2026-10-16). The byte
source egress interleaves channels mid-packet, which the TASK-024 planes
emitted as CXS the family rejected (single-context framing) -- missed because
every CXS cell ran one channel at a time.

## Amendment (2026-10-16, owner)

CXS_MAX_CREDIT defaults to **32**, not SRAM_DEPTH. One CXS credit is one flit
(IHI 0079D 2.1: "Each credit permits one flit of data transfer"), so a credit
cannot stand for several beats on a compliant link. The credit round trip
between the endpoints is about 3 cycles (registered grant -> flit next cycle
-> next-state occupancy), so 32 runs full rate with ~29 cycles of slack, and
stays inside the spec's 63. SRAM_DEPTH is beats per channel; the board design
point is 4 KB/channel (128 x 32 B), set by hand in create_project.tcl.

## Done

- Planes and generated tops: CXS_STREAM_SRCID_BITS = CIW (amba TASK-045);
  CXS_MAX_CREDIT defaults to SRAM_DEPTH (owner 2026-10-16: credits = the
  channel's SRAM beats, overridable lower), CXS_CREDIT_BEYOND_SPEC =
  (CXS_MAX_CREDIT > 63), CXS_RX_FIFO_DEPTH = credits.
- New cells source_concurrent / sink_concurrent (4 channels, one KICK_ENABLE
  write); the source cell fails unless the egress really switched channel
  mid-packet on the byte tree.
- RAPIDS top GATE 22/22, top_beats 18/18; both CXS tops lint at the 4096,
  512 and 15 credit points.
