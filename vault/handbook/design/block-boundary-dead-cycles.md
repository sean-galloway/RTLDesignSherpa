# Dead cycles hide at the block boundary, and a latency test will not find them

**Rule:** a datapath that processes framed blocks is only pipelined if its
throughput is `beats_per_block` cycles per block. Measure the SLOPE across two
block counts, never the absolute cycle count of one run -- the slope cancels
fill and drain latency, which is free, and isolates the per-block gap, which is
not. Then account for the slope against the architecture: every cycle above
`beats_per_block` has a named mechanism, and each mechanism is a separate fix.

## Measure a slope, not a time

Run N blocks and 2N blocks and subtract:

```python
c1 = await self.run_blocks(4)
c2 = await self.run_blocks(8)
slope = (c2 - c1) / 4           # cycles per block, latency-free
assert slope - beats_per_block <= 0.25
```

A single-run test cannot separate "the block took 70 cycles because the pipe is
10 deep" from "the block took 70 cycles because it stalls 6 at every boundary".
The first is free and the second is a throughput bug, and only the slope tells
them apart. Latency is free; a gap at the block boundary is not.

## The author of this note then divided a total by a block count

Worth recording because the rule above was already written down when it
happened. The RS decoder was slope-tested in sim to zero dead cycles on every
profile. The BOARD measurement was then taken as a single 64-block run, 4168
cycles, reported as `4168 / 64 = 65.1 cycles/block` and therefore "2.1 dead
cycles per block" -- and a hunt began for them in the encoder, the beat packer
and the error injector.

Measured properly, at four block counts:

| blocks | cycles | cycles - 63*blocks |
|---|---|---|
| 16 | 1,144 | 136 |
| 32 | 2,152 | 136 |
| 64 | 4,168 | 136 |
| 128 | 8,200 | 136 |

Slope 63.00 everywhere, which is the codeword, with one fixed 136-cycle fill.
Zero dead cycles. The phantom 2.1 was 136/64. The same single-point method
would have reported 71.5 at 16 blocks and 63.5 at 256 for identical hardware.

Two tells were available before any of that, and both were ignored:

- **A "rate" that moves with the run length is not a rate.** 71.5, 67.2,
  65.1, 64.1 across block counts is the signature of `slope + intercept/N`.
  One extra data point distinguishes a per-block gap from a fixed cost, and it
  costs one more run.
- **Someone else's working system is evidence.** The owner's objection was
  that another project saturates the SAME shared generator, checker and bus
  meter. A conclusion that requires widely-used shared fixtures to be broken
  needs far better support than elimination, and "I ruled out everything else"
  is not a measurement of the thing you landed on.

Per-cycle bucket counters settle it directly where they exist: the meter's
STARVATION count was a constant 140 at 64, 128 and 256 blocks while
BACKPRESSURE scaled linearly. A constant is a fill; only the term that scales
with the block count is a per-block gap.

## Account for the slope, do not just threshold it

On the Reed-Solomon decoder (2026-09-30) the slope was above line rate on 8 of
8 profiles, and it was TWO independent mechanisms wearing one number:

| mechanism | cost per block | binds when |
|---|---|---|
| load cycle at the boundary | `beats + 1` | always |
| non-pipelined solver stage | `iterations + 3` | `iterations + 3 > beats + 1` |

The same sweep outward then found two more in the repacking stage feeding the
codec -- a conservative accept condition that refused a beat the same cycle's
emit had made room for, and a flush that held off input while draining a tail.
Both were invisible until the stages around them reached line rate: a gap only
shows once it is the slowest thing in the pipe.

`slope = max(beats + 1, solver_occupancy)` matched all 8 measured profiles
exactly, with zero misses. That model is what made the work tractable: the
residue on the SHORTEST codeword was 3 cycles and on the longest 1, and without
the model the short-codeword cells look like a worse version of the same bug
instead of a second bug with a different fix. Build the model, check it against
every cell, and only then start cutting.

A profile-dependent residue is the tell. If the gap were one mechanism it would
be one number everywhere.

## The three cuts

1. **The boundary load cycle.** A stage that spends a cycle loading the next
   block's coefficients, then `beats` cycles walking it, costs `beats + 1`. The
   load must ride the previous block's LAST STEP edge. This is safe when the
   loaded units give `i_load` priority over `i_step`: the final beat's outputs
   are combinational off the pre-load registers and are captured downstream on
   the same edge the registers reinitialise.

2. **The per-block flags the load overwrites.** Cut 1 hands the live per-block
   flags to the next block one cycle before the old verdict wanted to read
   them. The fix is not to delay the load -- it is to give the verdict its own
   pipeline, one stage per datapath stage, captured on the same edge the data
   advances. A single snapshot register is not enough: whatever reads it a
   cycle later is reading the next block's block.

3. **Handshake overhead around a multi-cycle unit.** An `IDLE -> RUN -> PUSH`
   wrapper around an `iterations`-cycle solver costs `iterations + 3`: one
   cycle to accept, one to observe a registered `done`, one to push the result.
   Both the push and the accept can ride the done edge -- write the result and
   start the next block on the same edge -- taking it to `iterations + 1`. The
   last cycle is the registered `done` itself; see [[registered-status-outputs]]
   for retiring on the final update instead of a cycle later, which is what
   closed the final profile here.

## Prove the measurement saturates before you believe the number

The first slope reading off the RS AXIS wrappers was +128 dead cycles against
a 64-beat codeword. The board, running those same wrappers, was at 65.1
cycles/block -- so the measurement was wrong by a factor of three and the
hardware said so. The cause was the testbench: the send helper awaited each
packet's COMPLETION, so `tvalid` dropped between beats and what was being
measured was the BFM's send rate, not the DUT's throughput.

A throughput number is only about the DUT if the stimulus can saturate it.
Before trusting one:

- Drive through the queueing path (`_driver_send(pkt, sync=True)`), not the
  blocking one (`await master.send(pkt)`), and use the `backtoback` profile.
- Sanity-check the magnitude against anything independent -- a board
  measurement, a sibling block, the same test on a DUT you believe. A slope of
  3x the codeword is not a subtle defect, it is a broken meter.
- Prefer a test that DISCRIMINATES: the same slope test over the encoder and
  decoder wrappers returned +5.00 and +0.00 on the same profile, which is
  strong evidence it is reading the DUT. A number that comes out the same
  everywhere, or absurd everywhere, is reading the fixture.

The blocking semantic behind this is the same one in
[[blocking-send-deadlock]] -- `send()` returns when the DUT takes the beat, so
a loop of awaited sends is a loop of gaps. Picking the right window to measure
over is [[measure-over-the-window]].

## Where the floor actually is

After all three cuts the floor is the slowest STAGE, not the sum: throughput is
`max(beats, solver_iterations)`. A short codeword with a high correction power
can still be solver-bound -- `beats` is small and `iterations` is not -- and no
amount of boundary work fixes that. That case needs a second solver instance to
ping-pong, which is an area decision, not a bug. Say which it is.

Related: [[streaming-no-fsm]], [[valid-ready-contracts]],
[[registered-status-outputs]], [[sizing-invariants]].
