# Campaigns and the Oracle Argument

## Campaign inventory

| Campaign | What it proves | Determinism |
|----------|----------------|-------------|
| `init` | BUILD_ID, SCRATCH round-trip, PROFILE, TOPOLOGY. | Deterministic. |
| `smoke` | Bypass, clean, e=t, e=t+1, deterministic DEBUG walk. | Deterministic. |
| `sweep` | Exact correction counts for e = 0 .. 2t+2. | Deterministic. |
| `random` | Fresh seeds, mixed injector modes, 64 runs x 16 blocks. | Host-seeded `random.Random`; reproducible on demand. |
| `clusters` | Spatially correlated errors model a bad DRAM row or NAND page. | Deterministic combo matrix. |
| `localized` | Windowed errors model a half-plane failure. | Deterministic combo matrix. |
| `badblock` | Most blocks clean, a hard minority very bad. | Deterministic combo matrix. |
| `soak` | Long-running mixed-mode stress; the million-block run. | Host-seeded; replayable. |

: Table 3.1: BCH board campaign inventory.

## Determinism

Every board campaign is deterministic by default: `gen_seed` and `inj_seed`
start at 1, and the `seq_*.py` scripts produce bit-exact runs in cocotb
simulation and on the board. A failure you can replay is a failure you can
fix. `seq_random.py` still varies its draws, but those draws come from a
host-side `random.Random(seed)` seeded by the caller, so the variation is
reproducible when needed.

## The on-chip oracle

The decoder uses riBM with odd-syndrome computation and even syndromes by
squaring. It runs a second-syndrome recheck (`ENABLE_RECHECK`) and performs
flip-only correction. The checker independently regenerates the expected LFSR
pattern and reports `data_err` on any mismatched beat. Together they form the
on-chip oracle: the decoder decides whether it thinks it corrected the block,
and the checker decides whether the recovered bytes actually match the
reference. That pairing is what makes a silent mis-decode detectable.
