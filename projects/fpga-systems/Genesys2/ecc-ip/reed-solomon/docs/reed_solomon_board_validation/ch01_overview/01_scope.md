# Scope and Claims

## What this book is

This report is the board's statement about the RS(252,236) t=8 codec. The
Genesys 2 harness runs the same campaigns in cocotb simulation and on real
silicon, so when the board passes we have evidence that simulation matches
hardware at 100 MHz with real I/O, real clocks, and real register traffic.

## What is claimed

The 2026-10-05 battery demonstrates that four single-decoder bitstreams
(two flavours times two solvers) pass the same deterministic campaign set:

- `init`, `smoke`, `sweep`, `random`, `clusters`, `localized`, and `badblock`
  all PASS on `axis_ribm`, `axis_euclid`, `axi4_ribm`, and `axi4_euclid`.
- The sweep shows e <= 8 corrected, e = 9 .. 18 uncorrectable, on every image.
- The random campaign recorded 64 runs x 16 blocks with 0 failing runs across
  all images.
- The matching verdict counts between riBM and Euclid images are themselves a
  cross-solver check.
- The 2026-10-05 million-block soak on `axi4_ribm` passed: 0 failing runs,
  and 2 mis-decodes out of 74,240 over-t blocks, below the model's
  approximately 1-in-20,000 bound at e = t + 1.

That is board evidence that both key-equation solvers behave identically under
the same workload and that the codec honours the correction boundary.

## What is not claimed

This book does not replace the component DV matrix. It does not prove every
possible error pattern or every smaller RS profile. The dual-decoder on-chip
comparator is present in simulation but not in the production board matrix;
agreement is proven by running identical deterministic campaigns on the two
single-decoder images. The erasure `f = 2t` boundary is a known open issue
(TASK-005) and is called out in Chapter 3 and Chapter 5. The million-block
soak completed on 2026-10-06; Chapter 4 reports its counters.
