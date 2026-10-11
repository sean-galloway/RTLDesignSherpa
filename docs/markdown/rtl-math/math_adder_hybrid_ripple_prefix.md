# Hybrid Ripple/Prefix Adder

A parameterized hybrid adder in `rtl/math/` that pairs a low-order
ripple-carry chain with a single Kogge-Stone parallel-prefix tree over the
upper bits — the classic "short ripples are cheap, trees are cheap, but a deep
tree over *all* bits is not" compromise.

## Architecture

The lower `RIPPLE_BITS` bits ripple (on FPGAs this maps onto the dedicated
carry-chain logic; on ASICs short ripples are a handful of gates per bit).
The upper `N - RIPPLE_BITS` bits are covered by **one** Kogge-Stone prefix
network built from the `math_prefix_cell` equations.

The boundary is the interesting part, and the reason the module exists: the
prefix network computes group generate/propagate `G_i, P_i` for each upper bit
*as if the segment carry-in were 0*, and both carry-in hypotheses are served
by the same tree through

```
carry_i(c_in) = G_i | (P_i & c_in)
```

so when the low ripple's carry-out `c_lo` arrives, each upper sum bit pays
exactly one 2:1 mux (`G_i | (P_i & c_lo)`). No duplicated prefix tree, no
second evaluation of the tree — the upper tree computes *while* the lower
ripple settles, and total latency is approximately
`max(t_ripple(RIPPLE_BITS), t_prefix(N - RIPPLE_BITS)) + t_mux` instead of the
serial `t_ripple + t_prefix` a naive mixed scheme would pay. This is the
single-tree form of the carry-select idea (Bedrij 1962).

The combination — serial ripple bottom, parallel tree top, single boundary
mux — is a hybrid ALU practice passed down to this repo's owner from a senior
ALU designer (private communication), recommended "even on ASICs": short
carry chains age better than deep prefix trees at the low end, and the tree
only earns its area where the carry would actually have to travel.

## Parameters and instances

Core: `math_adder_hybrid_ripple_prefix #(parameter int N = 32, parameter int RIPPLE_BITS = 8)`.
Constraint: `1 <= RIPPLE_BITS < N` (elaboration-time guard). Width wrappers
follow the repo's per-width idiom:

| Module | N | RIPPLE_BITS (default) | Prefix levels |
|---|---|---|---|
| `math_adder_hybrid_ripple_prefix_008` | 8 | 2 | 3 (M=6) |
| `math_adder_hybrid_ripple_prefix_016` | 16 | 4 | 4 (M=12) |
| `math_adder_hybrid_ripple_prefix_032` | 32 | 8 | 5 (M=24) |
| `math_adder_hybrid_ripple_prefix_064` | 64 | 16 | 6 (M=48) |

The wrappers expose both parameters, so the split point is sweepable in
simulation — `val/math/test_math_adder_hybrid_ripple_prefix.py` sweeps
`RIPPLE_BITS in {1, 2, 3, N/2, N-1}` for `N in {8, 32}` at FULL.

Split guidance: the balanced point is roughly where the ripple delay equals
the prefix depth — for Kogge-Stone on an FPGA, `RIPPLE_BITS` around N/4 is a
reasonable starting estimate, and the measured answer is FPGA-family
specific. Note the Deschamps et al. caveat (ch. 7.5, measured on Virtex-5):
dedicated FPGA carry chains are so fast that plain ripple-carry wins over
logarithmic adders up to surprisingly large N — the hybrid's low section
exploits exactly that, and the prefix tree only carries the bits the carry
chain would struggle with.

## Ports

```systemverilog
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_c,       // carry-in
    output logic [N-1:0] ow_sum,
    output logic         ow_carry
```

## Verification

`val/math/test_math_adder_hybrid_ripple_prefix*.py` (shared checker in
`adder_tb_common.py`, golden model = Python integer addition): directed
corners (all-ones+carry, alternating patterns, MSB carries) plus random sweeps
— gate 500, func 5000, full 50000 vectors per instance, and the FULL
parameter sweep on the core.

## References

- Bedrij, O.J. "Carry-Select Adder." *IRE Transactions on Electronic Computers*, EC-11(3), June 1962. DOI: [10.1109/IRETELC.1962.5407919](https://doi.org/10.1109/IRETELC.1962.5407919) — the boundary-overlap structure (both carry hypotheses resolved by one network plus a mux) in its published form.
- Kogge, P.M., Stone, H.S. "A Parallel Algorithm for the Efficient Solution of a General Class of Recurrence Equations." *IEEE Transactions on Computers*, C-22(8), Aug. 1973. DOI: [10.1109/TC.1973.5009159](https://doi.org/10.1109/TC.1973.5009159) — the upper prefix network (local PDF in `rtl/math/references/`).
- Brent, R.P., Kung, H.T. "A Regular Layout for Parallel Adders." *IEEE Transactions on Computers*, C-31(3), Mar. 1982. DOI: [10.1109/TC.1982.1675982](https://doi.org/10.1109/TC.1982.1675982) — the prefix-addition framework the tree is built in (local PDF in `rtl/math/references/`).
- Deschamps, J.-P., Sutter, G.D., Cantó, E. *Guide to FPGA Implementation of Arithmetic Functions*, Springer (LNEE 149), 2012, ch. 7 — measured evidence that FPGA carry chains favor short ripples over logarithmic trees except at large N (secondary source; indexed in `rtl/math/references/README.md`).
- The specific ripple-low/tree-high single-tree hybrid is repo practice (owner, private communication from a senior ALU designer); no peer paper claiming this exact combination is known to us — recorded here to attribute the practice honestly.

## Navigation

[Back to Math Library](index.md)
