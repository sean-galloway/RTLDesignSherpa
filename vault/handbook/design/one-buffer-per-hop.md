---
title: One buffer per hop, and never share a combinational decoder across independent channels
summary: A data beat should be buffered once at each plane boundary. Granite's write beat crossed a W skid, an intake FIFO, the store's beat buffer and a DFI FIFO; the read return a DFI FIFO, the ring, an intake FIFO and an R skid. Dropping the intake FIFOs and halving the skids was cycle-identical on every proxy cell (2026-10-24). Sharing one address decoder between the AR and AW paths with an alternating grant cost 23 percent on concurrent read-write traffic and stays a knob, off.
---

# One buffer per hop

**Rule:** count the buffers a beat passes between the host port and the
PHY. Each plane boundary earns one (a skid or a FIFO sized to the latency it
hides); a second buffer behind the first is elasticity nobody asked for, and
on an FPGA its storage is LUTRAM, which is where the LUTs go.

## The case (pumice TASK-054, 2026-10-24)

granite's AXI plane buffered a write beat four times before the PHY (W skid
depth 4, 16-deep wr-data FIFO, the store's beat BRAM, the DFI write FIFO)
and a read return four times after it (DFI read FIFO, the 32-ticket ring, a
16-deep rd-data FIFO, R skid depth 4). The intake FIFOs existed to feed a
CAM that repacked on pop; the FIFO store takes beats in fill order, and the
ring already holds returns in AR order. With `INTAKE_FIFO_DEPTH = 0` and
`AXI_SKID_DEPTH = 2` every proxy cell (1 and 8 threads, all families, random,
mixed, 2-beat row_thrash) was cycle-identical on writes and one to five
cycles shorter on reads: AXI plane 4 958 -> 3 906 ASAP7 cells, 1 298 -> 933
flops, 5 722 -> 3 314 RAM bits. Nothing was lost because nothing was there.

## The counter-case: a shared decoder is not a buffer

The same round tried one address mapper for both intakes (`SHARED_ADDR_MAP`,
227 cells saved). The request could carry no ready term (the decode feeds
ready through the bank: a ready-gated request is a combinational loop,
Verilator UNOPTFLAT), so a side that cannot admit still holds the decoder,
and an alternating grant halves both sides under contention. Streams did not
notice; the concurrent read-write family lost 23 percent (98.1 -> 75.4
MB/s). A combinational resource on two independent channels' handshake
paths is a coupling, not a saving; it stays a knob, default off.

## The latency case: an empty buffer still costs a cycle unless it is transparent (jet TASK-003, 2026-11-10)

The area rule has a latency twin.  jet's CPU plane put a 2-deep FIFO
between the frontend's one-cycle request pulse and the lookup's
hold-until-accepted contract (it adapts the two handshakes, and it is
needed).  A FIFO presents a word the cycle after it is written, so every
request paid a cycle in a buffer that held nothing: the tag read, which
needs only the address, waited a cycle for a queue to turn over.  The
response ring did the same at the other end: a deposit became visible the
cycle after it landed, so a completed head sat one cycle in a slot before
leaving.  Making both transparent while empty (present the arriving
request to the lookup in its handshake cycle and write the FIFO only if
the lookup does not take it; present a deposit to the empty head slot in
its own cycle and never store it if the channel is ready) took the
resident read hit from 5 cycles to 3 on the Genesys2 pair-rig harness
with no change to either contract or to `jet_control`.  The FIFOs stayed:
they still absorb the rate difference they were built for; they just no
longer charge the common case for it.

Check: for each buffer on the latency path, ask whether a word that finds
it EMPTY waits in it.  If yes, and the consumer can take the word this
cycle, the buffer wants a bypass.  The bypass puts the consumer's accept
on the buffer's write-enable; on the Kintex-7 that was within the budget
because the accept was already a registered-state cone.

## How to check a design against it

1. Trace one beat each way and list every register stage that holds it.
   For each, name the latency or rate difference it absorbs. One that
   absorbs nothing is a candidate; drop it and run the proxy grid.
2. Shared combinational resources across independent channels: before
   building the arbiter, ask what the losing side does while it waits. If
   the answer is "its handshake stalls", measure the concurrent family
   first.

Related: [[per-bank-queues-admit-from-the-pool]] (the store side of the
same plane), [[cdc]] (the DFI crossing that was the first buffer removed).
