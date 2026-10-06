# Campaigns and the Oracle Argument

## Campaign inventory

| Campaign | What it proves | Determinism |
|----------|----------------|-------------|
| `init` | BUILD_ID, SCRATCH round-trip, PROFILE, TOPOLOGY. | Deterministic. |
| `smoke` | Bypass, clean, e=t, e=t+1, deterministic DEBUG walk. | Deterministic. |
| `sweep` | Exact correction counts for e = 0 .. 2t+2. | Deterministic. |
| `random` | Fresh seeds, mixed injector modes, 64 runs x 16 blocks. | Host-seeded; reproducible on demand. |
| `clusters` | Spatially correlated errors. | Deterministic combo matrix. |
| `localized` | Windowed errors. | Deterministic combo matrix. |
| `badblock` | Retention-tail / worn-block behaviour. | Deterministic combo matrix. |
| `erasure` | Marked-symbol runs at f = t, 2t, 2t+1. | Deterministic. |
| `soak` | Long-running mixed-mode stress; the million-block run. | Host-seeded; replayable. |

: Table 3.1: Reed-Solomon board campaign inventory.

## Determinism and cross-solver agreement

The host-side RNG seed defaults to 1. With that default, the random, soak,
clusters, localized, and badblock campaigns are fully deterministic. Because
the riBM and Euclid images run bit-identical workloads, the matching verdict
counts between them are the cross-check. You do not need the on-chip
comparator to know the two solvers agree; the campaigns prove it.

## The dual-solver loop as oracle

The AXIS datapath in simulation feeds the same corrupted blocks to two
`rs_decoder_core` instances, one with `KES_ALGO=RIBM` and one with
`KES_ALGO=EUCLID`. Each decoder's output is compared beat-by-beat against the
generator's regenerated LFSR pattern in its own `axis4_slave_pattern_check`, so
a correction is judged by a reference that never saw the errors. A separate
comparator then requires the two decoders to agree on every beat and on every
block's verdict. On the board images this comparator is absent by construction;
the cross-check is the deterministic campaign battery.
