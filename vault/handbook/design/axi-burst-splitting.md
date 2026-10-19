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
