---
title: AXI burst splitting
summary: A block that cuts one burst into several must restart every later piece on the size grid, and its tests must split an UNALIGNED burst.
---

# AXI burst splitting

- **Only the first beat of an AXI burst may be unaligned** (AXI A3.4.1):
  every later beat is on the `2^AxSIZE` grid. So when a converter cuts an
  INCR burst into pieces (AXI4 -> AXI3 at 16 beats, a 4 KB splitter, a
  downsizer), piece *n > 0* starts at `aligned(start) + n * piece_beats * size`,
  never `start + n * piece_beats * size`. The second form carries the first
  beat's offset into every later piece, and each piece's first beat then
  looks partial to the slave: a write's full strobe lands on lanes the slave
  thinks are inactive, and a read can come back with only the upper lanes.
- **The test that catches it splits an unaligned burst.** Aligned starts make
  both formulas agree, so a suite of aligned bursts -- even long, chopped,
  multi-ID ones -- passes the broken step. Every split path needs one case
  whose start is off the size grid.
- *Case (2026-10-19, converters BUG-011):* `axi4_to_axi3_{wr,rd}` stepped the
  chunk address with `active_addr + (chunk_beats << size)`. The converter's
  own suite chopped 17/32/64/256-beat bursts, all aligned, and passed. The
  Genesys 2 bridge stress model's AXI3 build found it on the first run: the
  stress slave computes each beat's lanes from its own AW, so it flagged
  `S_WSTRB` on the first beat of every later chunk -- in sim and, from the
  pre-fix bitstream, on the board. Regressions:
  `incr_write_len32_unaligned`, `incr_burst_len17_unaligned`.
- A responder that returns every byte lane hides the read-side half of the
  bug; it was found from the write side. Check strobes and lanes against the
  slave's OWN view of the burst, not the master's.
- **The same rule applies per beat, not only per piece.** An address
  generator that walks a burst one beat at a time steps INCR from the
  aligned address, `(addr & ~(bytes - 1)) + bytes`, exactly as WRAP already
  must. *Case (2026-10-21, bridge BUG-019):* `axi_gen_addr` (so every
  AXI4 -> APB shim and the `sdpram_slave_*` blocks) and
  `axi4_to_axil4_{rd,wr}` both stepped `addr + bytes`.
- **A width converter may rewrite AxSIZE only for full-width INCR.** FIXED,
  WRAP and narrow bursts are legal on any bus at least as wide as their
  beats, so the converter must pass them through (one beat for one beat) or,
  when they are wider than the narrow bus, expand them into one narrow INCR
  piece per beat. Packing them produced a one-beat WRAP, a 24-beat FIXED and
  miscounted narrow INCR (bridge BUG-018). A documented contract
  ("full-width INCR only") that nothing at the port enforces is the defect,
  not a limitation.
- **Check the BFM against the spec before trusting a green suite.** The AXI
  slave BFMs stepped INCR from the unaligned start and walked FIXED, so the
  converters' own tests agreed with the broken RTL. One test even wrote the
  BFM's bug into its expected data ("the BFM returns address + beat_offset
  even for FIXED"). A reference with the same bug as the design hides it.
  The BFMs now take every beat address from one shared helper
  (`CocoTBFramework/components/shared/axi_burst.py`, `beat_addr` /
  `beat_lanes`), unit-tested against A3.4.1. The converter matrix tests
  (`*_burst_matrix`) drive every burst type x size x alignment and check
  the slave-side AXI is legal as well as the bytes.
