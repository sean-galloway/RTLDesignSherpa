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

## Account for the slope, do not just threshold it

On the Reed-Solomon decoder (2026-09-30) the slope was above line rate on 8 of
8 profiles, and it was TWO independent mechanisms wearing one number:

| mechanism | cost per block | binds when |
|---|---|---|
| load cycle at the boundary | `beats + 1` | always |
| non-pipelined solver stage | `iterations + 3` | `iterations + 3 > beats + 1` |

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

## Where the floor actually is

After all three cuts the floor is the slowest STAGE, not the sum: throughput is
`max(beats, solver_iterations)`. A short codeword with a high correction power
can still be solver-bound -- `beats` is small and `iterations` is not -- and no
amount of boundary work fixes that. That case needs a second solver instance to
ping-pong, which is an area decision, not a bug. Say which it is.

Related: [[streaming-no-fsm]], [[valid-ready-contracts]],
[[registered-status-outputs]], [[sizing-invariants]].
