# Packet framing is per stream wherever streams can interleave

**Rule:** if a protocol lets packets of different streams interleave on one
link, every block that tracks "a packet is open" must track it PER STREAM:
the endpoints, any adapter that inserts START/END, monitors, snoops and the
DV models. One open-packet bit per link rejects legal traffic.

CXS is the case in this repo. A CXS stream is the flits sharing
CXSPRCLTYPE / CXSSRCID / CXSTGTID (IHI 0079D 2.5.2), and flits of different
streams may interleave, so `cxs_cntl_track` keeps a bit per stream key
(`cxs_stream_key`, the low bits that tell the streams in use apart) and the
RDS-DV depacketizer keeps an open packet per stream. AXI-Stream has the same
property: packets of different TID/TDEST may interleave.

## The failure that taught it

The CXS family shipped (2026-10-15) tracking one open packet per link, and
the RAPIDS CXS planes passed every test. Every RAPIDS CXS cell ran one channel
at a time. The byte-granular RAPIDS source arbitrates round-robin per drain
block while a packet spans the whole descriptor, so with two channels active
it switches channel mid-packet. That's legal AXIS and legal CXS, and the CXS
endpoints flagged it as a protocol error. The next day the CXS pattern
injector's interleave mode exposed it immediately, and a concurrent-channel
RAPIDS cell confirmed it.

## How to apply

- When a protocol has stream identifiers, read the spec for whether streams
  may interleave before writing any packet-state tracker.
- Bound the state with a key (the low bits of the stream fields that are in
  use) and document that streams outside the key alias.
- Test the key both ways on the same traffic: with it, interleaved streams
  pass; without it, they MUST fail. Without the second half, a pass can mean
  the traffic never interleaved (`val/amba/test_cxs_stream_interleave.py`).
- A multi-channel engine needs a test that runs its channels concurrently and
  checks that they actually overlapped.

Related: [[new-monbus-protocol]], [[observers-do-not-drive]].
