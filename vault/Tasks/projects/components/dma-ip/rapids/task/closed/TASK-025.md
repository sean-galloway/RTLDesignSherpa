# TASK-025: CXS planes frame per stream; credits default to the channel SRAM

**Priority:** P1
**Status:** closed 2026-10-16
**Owner:** sean galloway

One CXS link per direction, CXSSRCID = channel (owner 2026-10-16). The byte
source egress interleaves channels mid-packet, which the TASK-024 planes
emitted as CXS the family rejected (single-context framing) -- missed because
every CXS cell ran one channel at a time.

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
