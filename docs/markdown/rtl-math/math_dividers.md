# Integer Dividers: Restoring, Non-Restoring, and the SRT Family

A family of sequential unsigned integer dividers in `rtl/math/`: the two
classical digit-recurrence baselines (restoring, non-restoring) and three SRT
dividers spanning the design space from textbook radix-2 to carry-save
radix-2 and 2-bits-per-cycle radix-4. Parameterized `DATA_WIDTH` (default 32),
with `gate`/`func`/`full` cocotb verification in `val/math/` (FULL includes an
exhaustive 8-bit proof over all 65,280 operand pairs, randomized 32/33-bit
sweeps, back-to-back divisions, and divide-by-zero).

## Interface

All five modules share one handshake:

```systemverilog
module math_divider_<algo> #(
    parameter int DATA_WIDTH = 32
) (
    input  logic                  i_clk,
    input  logic                  i_rst_n,     // active-low, async assert
    input  logic                  i_valid,     // start pulse (idle only)
    output logic                  ow_busy,
    output logic                  ow_done,     // single-cycle completion pulse
    output logic                  ow_dbz,      // divide-by-zero (with ow_done)
    input  logic [DATA_WIDTH-1:0] i_dividend,
    input  logic [DATA_WIDTH-1:0] i_divisor,
    output logic [DATA_WIDTH-1:0] ow_quotient,
    output logic [DATA_WIDTH-1:0] ow_remainder
);
```

Latency (cycles, excluding the one-cycle done pulse): restoring `W`,
non-restoring `W+1` (final correction), SRT radix-2 and radix-2-CSA `W`,
SRT radix-4 `ceil(W/2)`. Divide-by-zero and (radix-4 only) divide-by-one
complete in one cycle.

## The five algorithms

| Module | Digit set | Bits/cycle | Remainder form | Selection |
|---|---|---|---|---|
| `math_divider_restoring` | {0,1} | 1 | non-redundant | full compare + conditional subtract |
| `math_divider_nonrestoring` | {+1,-1} | 1 | signed, final correction | sign only |
| `math_divider_srt_radix2` | {-1,0,+1} | 1 | signed, redundant | exact `2t` vs +/-D/2 |
| `math_divider_srt_radix2_csa` | {-1,0,+1} | 1 | **carry-save** (S,C) | estimate + threshold table |
| `math_divider_srt_radix4` | {-3..+3} | 2 | signed, redundant | exact `2t` vs +/-D/2, +/-3D/2, +/-5D/2 |

All three SRT variants convert the redundant signed-digit quotient to
two's complement **on the fly** (Ercegovac-Lang Q/QM pair registers), so no
post-pass over the digits is ever needed, and a single final conditional add
produces the canonical `0 <= remainder < divisor` result.

## Study notes: what the literature says and what this family does about it

These notes are the outcome of studying Deschamps et al., ch. 9 (SRT),
ch. 10.3 (square root analogues), and Ercegovac-Lang's digit-recurrence
framework against what a practical integer IP needs.

**The 2023 `math_divider_srt` was not SRT.** The module removed from
`rtl/common/` during the 2023 reorganization (commit `c13193656`, derived from
a projectf.io article) implements *restoring* division — quotient digits
{0,1} from a full compare, no redundant representation, no SRT anything. It
re-enters this family honestly named `math_divider_restoring`, alongside the
true SRT family below.

**Why radix-2 SRT needs no divisor normalization here.** The shift-in
formulation streams the dividend MSB-first: `t = 2R + x_i` with invariant
`|R| <= D/2`, so `t in [-D, D+1]`. The digit set {-1,0,+1} with boundaries at
`+/-D/2` covers `[-3D/2, 3D/2]`, which always contains `[-D, D+1]`. The
single-bit "slop" (+1) is the whole story: exact compares `2t >= D` /
`2t <= -D` are cheap, and nothing depends on the divisor's magnitude. This is
the classic teaching SRT (Robertson/Tocher) with the on-the-fly conversion
added.

**Why radix-4 SRT uses digit set {-3..+3} and not {-2..+2}.** Two-bit shift-in
gives `t = 4R + 2*b1 + b0 in [-2D, 2D+3]`. The classic {-2..+2} set covers
only `|t| <= 8D/3`, and the slop (+3) cannot be absorbed by any fixed
redundancy factor `rho` (`4*rho*D + 3 <= (2+rho)D` has no solution at
`rho = 2/3`). Widening the digit set to {-3..+3} with nearest-digit selection
(exact compares of `2t` against the odd multiples `+/-D, +/-3D, +/-5D`)
contains every `t` for all `D >= 2` (`2D+3 <= 7D/2`), maintaining
`|R| <= D/2` by rounding. `D == 1` is special-cased (quotient = dividend).
This is exactly the digit set Deschamps 9.2.5 develops for radix-4.

**Why not a normalized-divisor radix-4?** The textbook radix-4 (normalize
`D` to [1,2), run `ceil(W/2)` recurrence steps, recover the integer quotient
with a shift) has a trap for *integer* outputs: the un-produced low quotient
bits leave a final remainder up to `2Dn/3` — canonically correcting that
costs up to `~2^s/3` subtract iterations for small divisors (large `s`). FP
dividers do not care (the scale is absorbed into the exponent); integer
dividers do. The unnormalized shift-in architecture avoids the whole class
of problem at the price of six comparators instead of a selection table.

**The CSA variant is the performance point.** `math_divider_srt_radix2_csa`
keeps the remainder in carry-save form `(S, C)` through the loop: both the
doubling `t = 2(S+C) + x_i` and the digit subtraction `t - q*D` are 3:2
compressions, so per-iteration carry propagation is a handful of bits, not
`W`. The quotient digit comes from a truncated estimate:

- `est = floor(t / 2^(p-5))` where `p = floor(log2(D))` (exact for `p < 5`),
  on a 1/32 grid; the carry-save estimate adds a second 1/32 uncertainty, so
  `u_tot = 1/16` in units of `2^p`.
- The normalized divisor `D/2^p in [1,2)` is bucketed by its top two bits
  (4 buckets). Per bucket, threshold `T+` must satisfy
  `u_tot + eps <= T+ <= d_lo/2 - u_tot - eps` (choose `+1` iff `est >= T+`;
  containment for `q=+1` needs `t >= 0` certainly, containment for `q=0` needs
  `t <= D/2` certainly), with `eps = 1/128`:

| Bucket | `D/2^p` in | `T+` (est units) |
|---|---|---|
| 0 | [1.00, 1.25) | 8 (1/4) |
| 1 | [1.25, 1.50) | 10 (5/16) |
| 2 | [1.50, 1.75) | 12 (3/8) |
| 3 | [1.75, 2.00) | 14 (7/16) |

  (Window width is ~1/8 per bucket against a 1/32 grid — comfortable margin.)
- The exact remainder is reconstructed once, after the final iteration, by a
  single full-width CPA `S + C` — off the iterative critical path.

This is the classic radix-2 carry-save SRT shape (Deschamps 9.2.4) with the
selection constants derived from the containment window rather than copied
from a P-D plot.

## On-the-fly conversion tables

Radix-2, digits {-1,0,+1} (invariant `QM == Q - 1` maintained per step):

| q | Q_next | QM_next |
|---|---|---|
| +1 | 2Q+1 | 2Q |
| 0 | 2Q | 2QM+1 |
| -1 | 2QM+1 | 2QM |

Radix-4, digits {-3..+3}:

| q | Q_next | QM_next |
|---|---|---|
| +3 | 4Q+3 | 4Q+2 |
| +2 | 4Q+2 | 4Q+1 |
| +1 | 4Q+1 | 4Q |
| 0 | 4Q | 4QM+3 |
| -1 | 4QM+3 | 4QM+2 |
| -2 | 4QM+2 | 4QM+1 |
| -3 | 4QM+1 | 4QM |

Final selection: quotient = `Q` if the remainder is non-negative, else `QM`
(and remainder += D). One step suffices because the recurrence remainder is
already bounded by `D/2`.

## Verification

`val/math/test_math_divider_*.py` (driver/checker shared in
`divider_tb_common.py`, golden model = Python `divmod`):

- **gate**: directed corners + divide-by-zero + 200 random (W=8).
- **func**: directed + dbz + 2000 random (W=32).
- **full**: directed + dbz + exhaustive W=8 (all 65,280 pairs), 5000 random
  W=32, 1000 random W=33 (odd-width elaboration), 500 back-to-back divisions.

## References

- Robertson, J.E. "A New Class of Digital Division Methods." *IRE Transactions on Electronic Computers*, EC-7(3), Sept. 1958. DOI: [10.1109/TEC.1958.5222579](https://doi.org/10.1109/TEC.1958.5222579) — the seminal SRT radix-2 paper (the R in SRT; Sweeney's contribution was never formally published).
- Tocher, K.D. "Techniques of Multiplication and Division for Automatic Binary Computers." *Quarterly Journal of Mechanics and Applied Mathematics*, 11(3), 1958. DOI: [10.1093/qjmam/11.3.364](https://doi.org/10.1093/qjmam/11.3.364) — independent discovery (the T in SRT).
- Atkins, D.E. "Higher-Radix Division Using Estimates of the Divisor and Partial Remainders." *IEEE Transactions on Computers*, C-17(10), Oct. 1968. DOI: [10.1109/TC.1968.226439](https://doi.org/10.1109/TC.1968.226439) — higher-radix SRT selection tables (the radix-4 line).
- Ercegovac, M.D., Lang, T. "On-the-Fly Conversion of Redundant into Conventional Representations." *IEEE Transactions on Computers*, C-36(7), July 1987. DOI: [10.1109/TC.1987.1676986](https://doi.org/10.1109/TC.1987.1676986) — the Q/QM on-the-fly conversion used by all three SRT modules.
- Deschamps, J.-P., Sutter, G.D., Cantó, E. *Guide to FPGA Implementation of Arithmetic Functions*, Springer (LNEE 149), 2012, ch. 9 — textbook treatment (secondary source; measured Virtex-5 data). Indexed in `rtl/math/references/README.md`.
- Restoring and non-restoring division predate the peer literature as textbook primitives; no defensible single origin exists (marked "standard technique" in the references index).

## Navigation

[Back to Math Library](index.md)
