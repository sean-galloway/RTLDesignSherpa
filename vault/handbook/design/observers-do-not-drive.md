# An observer observes; it never drives

**Rule:** an OBSERVER — a block snooping a bus it is not an endpoint of — must
not gate that bus's handshake. If it cannot keep up, it loses observations. It
does not throttle, and it certainly does not corrupt.

Losing observations is a coverage problem you can size your way out of.
Driving the bus makes the instrument a participant, and then the thing you
measure is no longer the thing that would have happened.

## What this rule is NOT about

The `*_mon` wrappers (`axi4_slave_rd_mon`, `axi4_master_wr_mon`, and their ten
siblings) are **not** observers. Each wraps a real endpoint core — 
`axi4_slave_rd_mon` instantiates `axi4_slave_rd` — so it is IN the datapath by
construction and owns `s_axi_arready` by design. Its `block_ready` gate is
intended behaviour, and `ap_block_ready_gating` is the correct contract for it.
Do not "fix" that family against this note.

The rule applies to the OBS modules: `axi4_intf_master_observer` / `axi4_intf_slave_observer` and the
observer split that replaces it. Those hang off a bus as parallel snoops, and
for them any handshake gating is the defect.

## The failure that taught it

`dma_slave_monitors` was built by splicing in-path `*_mon` wrappers onto the
DMA-slave bus, where a parallel snoop belonged. One un-sliced
`MAX_TRANSACTIONS(16)` table against 8 channels x 8 outstanding, so the table
saturated and the gate — a legitimate gate, in a block that should not have
been in the path at all — went live on a production datapath.

On the Genesys 2 STREAM perf build, counted at both ends of the same link over
7 ms: **49 ARs went in, 367 were accepted**, all on channel 3. Each replay was
a well-formed 16-beat burst (15.97 beats/AR). The downstream slave dutifully
returned data for every one, and channel 3's SRAM wedged with its allocator
reading EMPTY and its drain reading FULL at the same instant.

**A second, separable defect made the saturation catastrophic rather than
merely slow.** The wrapper applies its gate to the OUTWARD ready only:

```systemverilog
.s_axi_arvalid (s_axi_arvalid),          // ungated into the core
.s_axi_arready (w_core_s_axi_arready),   // core's own ready
...
assign s_axi_arready = w_core_s_axi_arready &
       (w_block_ready | ~cfg_monitor_enable);
```

The core underneath still sees the ungated `s_axi_arvalid` and answers with its
own ready, so it accepts the command while the master is told "not ready". The
master, never having seen a handshake, holds the same command on the bus — and
the core accepts it again, every cycle, until the table drains. Backpressure
became replay. That is a wrapper bug in its own right and is tracked
separately; it is not what this note is about.

## Why nothing caught it

Every per-transaction property held. Bursts were well formed, IDs matched,
rlast landed in the right place, no timeout fired. The in-RTL formal property
sitting directly below the bug —

```systemverilog
ap_block_ready_gating: assert (!s_axi_arready);   // when blocked
```

— passed, because it constrains the outward ready and says nothing about what
the core accepts. What broke was **conservation**: commands in ≠ commands out.
Nothing was watching that.

**Corollary worth more than the rule:** on any inserted block, assert
conservation across it, not just well-formedness within it. A handshake count
in versus out would have flagged this on the first blocked cycle instead of
50 µs later as an impossible pair of SRAM counters three layers away.

## The right shapes

- **Snoop in parallel.** An observer taps the bus; it does not sit in it. If
  the block you are reaching for wraps an endpoint core, it is the wrong block
  for the job — that is how `dma_slave_monitors` happened.
- **Size the table for the real concurrency** so no block ever arises. The
  STREAM observer's own comment gets this right: *"An instrument must not be
  the bottleneck."*
- **Switch the taps off** where you do not need them (`ENABLE_MON_TAPS=0`).
- **Bank the table by ID** when one table large enough will not close timing —
  see [[sizing-invariants]] for the per-bank rule, since banking caps per-ID
  concurrency at the bank depth, not the table depth.
- **Where a gate is legitimate** (an in-path `*_mon` wrapper), mask the valid
  into the core with the *same* term that masks the outward ready, so both ends
  of the handshake agree. Gating one side alone is the defect.

Filtering *what is tracked* is always fine — an ID-range filter changes which
transactions get a table entry and never what flows on the bus. That is the
difference between an observer that scales and one that participates.

Related: [[valid-ready-contracts]], [[sizing-invariants]].
