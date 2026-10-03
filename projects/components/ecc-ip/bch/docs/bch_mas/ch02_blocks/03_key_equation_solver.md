<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Key Equation Solver (`bch_key_equation_solver`)

**Module:** `bch_key_equation_solver.sv`
**Location:** `rtl/`
**Category:** datapath + conditional control FSM
**Parent:** `bch_decoder_core`
**Status:** target — no RTL exists; algorithm choice is PRD D11

---

## Purpose

`bch_key_equation_solver` inverts the key equation from the `t` odd syndromes
`S_1, S_3, ..., S_2t-1` to the error-locator polynomial `Lambda(x)`. The
choice of algorithm is PRD D11; this page documents all three candidates and
their microarchitectural implications. Nothing outside the solver knows which
algorithm produced `Lambda`: the Chien search, block buffer, and corrector are
identical in every build.

## Parameters

| Parameter | Type | Range | Default | Meaning | PRD |
|---|---|---|---|---|---|
| `FIELD_DIM` | int | 3..16 | **TBD** | `m`; field is GF(2^m) | D1 |
| `T_BITS` | int | 1..(2^m-1)/2 | **TBD** | correctable bit errors | D2 |
| `KES_ALGO` | string | `"RIBM"`, `"EUCLID"`, `"SMALL_T"` | **TBD** | solver algorithm | D11 |

: Table 2.5: Key-equation solver parameters

## Interface

| Signal | Direction | Width | Description |
|---|---|---|---|
| `aclk` | in | 1 | one clock |
| `aresetn` | in | 1 | active-low synchronous reset |
| `in_valid` | in | 1 | odd syndromes are valid |
| `in_ready` | out | 1 | solver accepts syndromes |
| `in_syndromes` | in | `T_BITS * m` | `{S_2t-1, ..., S_3, S_1}` packed GF values |
| `out_valid` | out | 1 | `Lambda(x)` coefficients are valid |
| `out_ready` | in | 1 | downstream accepts `Lambda` |
| `out_lambda` | out | `(T_BITS + 1) * m` | locator coefficients `Lambda_0 .. Lambda_T_BITS` |
| `out_lambda_degree` | out | `$clog2(T_BITS + 1)` | actual degree of `Lambda` |

: Table 2.6: Key-equation solver ports

## Candidate algorithms

The trade-off table below is copied from `../bch_has/ch03_architecture/03_solver_options.md`.

| | inversionless BM (`"RIBM"`) | modified Euclidean (`"EUCLID"`) | step-by-step / PGZ (`"SMALL_T"`) |
|---|---|---|---|
| Algorithm | reformulated inversionless Berlekamp-Massey, Sarwate and Shanbhag 2001; seeded with the t odd syndromes | Sugiyama's Euclidean algorithm with cross-multiplication in place of division (Shao et al. 1985) | Massey 1965 step-by-step correction, or the Peterson-Gorenstein-Zierler direct matrix solve for small t |
| Array | 3t + 1 processing elements, 2 registers each | four register arrays: R and Q of 2t + 1 symbols, the shifted locator pair of 2t + 3 | control-heavy but small datapath: one or a few GF multipliers and a syndrome update loop |
| GF multipliers | 2 per element: 6t + 2 | 2 per coefficient of each pair: 8t + 8 | O(t^2) logic or a single iterative multiplier |
| Iterations | exactly 2t | data-dependent, t + 1 .. 2t | one per located error position, up to t |
| Critical path per iteration | one multiply and one XOR, no feedback across the array | cross-multiply feeding a degree comparison that drives the swap: longer | depends on implementation; often dominated by syndrome-update MUX tree |
| Control | discrepancy select and gamma update | two nominal degree counters, the normalise / cross / swap rule | position counter, syndrome-test loop, error-counter update |
| Readability | dense; the reformulation is not obvious from the textbook | the textbook algorithm, recognisable step by step | the simplest conceptually for very small t |
| Best fit | general t; the default if no consumer names a small-t profile | a cross-check and a readable alternative | t <= 8 (flash pages often sit here); smallest area at tiny t |

: Table 2.7: Key-equation solver candidates

No default is selected at MAS v0.1. The choice is PRD D11.

## Microarchitecture internals

### `"RIBM"` and `"EUCLID"` — fixed-iteration arrays

Both the reformulated inversionless Berlekamp-Massey array and the modified
Euclidean array are pure datapath structures. They need:

- an iteration counter, 0 .. `2 * T_BITS`
- a start pulse from `in_valid && in_ready`
- a completion qualifier when the iteration count reaches its target

Neither implementation has a state machine in the data path. The control
signals (discrepancy select, gamma update, degree comparison, swap) are
combinational or registered qualifiers derived from the iteration counter and
the array registers.

### `"SMALL_T"` — conditional minimal control FSM

The step-by-step and PGZ approaches are control-heavy. If D11 selects
`"SMALL_T"`, this block is the one place in the decoder datapath where a
minimal control FSM is permitted (per `vault/handbook/design/minimal-fsm.md`).
The target state list is the fewest states that carry real distinctions:

```
IDLE   -> wait for in_valid
RUN    -> execute one iteration / error-position test
TEST   -> evaluate the discrepancy / matrix determinant
DONE   -> out_valid raised, hold until out_ready
```

The IDLE/RUN/TEST/DONE list is conditional on `KES_ALGO == "SMALL_T"` and is
marked as such in the RTL. States that only wait one fixed cycle are merged
into RUN with a sub-counter.

## FSM policy

- For `"RIBM"` and `"EUCLID"`: **no FSM** in the data path; only an
  iteration counter and completion qualifier.
- For `"SMALL_T"`: **one minimal control FSM** is permitted, conditional on
  D11, with the state list above.

## Timing

- `"RIBM"`: exactly `2 * T_BITS` iterations.
- `"EUCLID"`: between `T_BITS + 1` and `2 * T_BITS` iterations, data-dependent.
- `"SMALL_T"`: up to `T_BITS` error-position tests, plus setup cycles.
- Exact cycle counts are placeholders tied to PRD D11 and D6.

## Notes

- Two solvers agreeing as a cross-check is the recommended verification
  posture from the HAS: the golden model runs every candidate on every block
  and requires identical roots, and the RTL is built with whichever algorithm
  the first consumer prefers.
- The locator degree `out_lambda_degree` is produced by the solver and is used
  by the Chien search to determine correctability.
- `Lambda_0` is always 1 for a valid locator; the formal targets include this
  invariant and the relationship to the odd syndromes.
