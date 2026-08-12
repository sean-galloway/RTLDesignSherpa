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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# math_mod_3_compress (`math_mod_3_compress.sv`)

**Location:** `rtl/math/`
**Status:** Production Ready

## Purpose

`math_mod_3_compress` is a purely combinational block that computes `d_in mod 3` for a 16-bit operand, returning the 2-bit remainder (0..2). It's built in the same carry-save-compressor style as `div_by_15_ceil_32compress.sv` — a 3:2 compressor tree feeding a final carry-propagate add and a small fold — but it emits only the remainder, which is exactly what the monbus burst-writer needs to round a beat count **down** to a whole number of 3-beat records: `rounded = X - (X mod 3)`.

There's no `*` or `/` operator anywhere, so it infers no DSP block and no iterative divider — just a shallow tree of carry-save adders and a couple of small adds.

The monbus compressor packs monitor packets into fixed 3-beat records. Working out how many whole records a beat count covers means computing `X - (X mod 3)`, which means you need the remainder `X mod 3`. This module produces that remainder combinationally without a divider, so the burst-writer can round the count down in a single cycle of logic.

- **Combinational, single-cycle:** No clock, no state; pure logic from `d_in` to `rem_out`
- **No multiply / divide:** Avoids inferred DSP and iterative dividers
- **Carry-save tree:** Eight base-4 digits reduced with 3:2 compressors instead of a ripple-add chain
- **Remainder only:** Returns just `d_in mod 3` (0..2), the quantity the monbus record rounding needs
- **Shared style:** Same construction as `div_by_15_ceil_32compress.sv`, reusing `math_adder_carry_save_nbit`

**Use Cases:**

- Rounding a monbus beat count down to a whole number of 3-beat records (`X - (X mod 3)`)
- Any combinational `mod 3` of a 16-bit value where a DSP-free, divider-free implementation is desired
- A worked reference for the base-4 digit-sum residue technique with carry-save reduction

**Key Benefit:** Produces `d_in mod 3` in one combinational stage with a shallow carry-save tree, no multiplier, divider, or DSP block required.

## Parameters

This module has no parameters. The operand width is fixed at 16 bits and the result at 2 bits.

*(Internally, `localparam int BITS = 6` sizes the carry-save datapath so the weight-2 carry left-shifts have headroom.)*

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `d_in` | Input | 16 | Operand whose remainder mod 3 is computed |
| `rem_out` | Output | 2 | `d_in mod 3`, in the range 0..2 |

## Functional Description

### Base-4 Digit-Sum Method

The trick rests on one identity: `4^k ≡ 1 (mod 3)`. Split `d_in` into 2-bit groups and each group is a base-4 digit with weight `4^k`; since every weight is `1 (mod 3)`, the **sum of the eight digits is congruent to `d_in (mod 3)`**. The problem therefore collapses to summing eight small digits and taking that sum mod 3.

The eight 2-bit groups are zero-extended to the 6-bit carry-save width:

```systemverilog
assign w_g0 = {{(BITS-2){1'b0}}, d_in[1:0]};
assign w_g1 = {{(BITS-2){1'b0}}, d_in[3:2]};
// ... through ...
assign w_g7 = {{(BITS-2){1'b0}}, d_in[15:14]};
```

### 3:2 Compressor Tree

Rather than a ripple-add chain, the eight digits are reduced with a tree of `math_adder_carry_save_nbit` 3:2 compressors. Each carry output has weight 2, so wherever a carry feeds the next level it is left-shifted by one (`{carry[BITS-2:0], 1'b0}`); the always-zero top carry bit is dropped, exactly as the div-by-15 reference does:

- **Level 1:** three compressors reduce the eight digits three at a time (the last triple padded with 0)
- **Level 2:** two compressors combine the level-1 sums and shifted carries
- **Level 3:** one compressor, holding `w_carryE2` for the next level
- **Level 4:** one compressor folds in the held carry

A final carry-propagate add collapses the last sum/carry pair into the digit sum (0..24, still `≡ d_in (mod 3)`):

```systemverilog
assign w_grp_sum = w_sumG4 + {w_carryG4[BITS-2:0], 1'b0};
```

### Final Fold and Conditional Subtract

The digit sum `w_grp_sum` tops out at 24, so it is folded once more onto its own base-4 digits (same residue mod 3), giving a value in 0..7, and then a conditional subtract brings it into the final 0..2 range:

```systemverilog
assign w_fold = {2'b0, w_grp_sum[1:0]} + {2'b0, w_grp_sum[3:2]} + {3'b0, w_grp_sum[4]};
assign rem_out = 2'((w_fold >= 4'd6) ? (w_fold - 4'd6)
                  : (w_fold >= 4'd3) ? (w_fold - 4'd3)
                                     : w_fold);
```

The two-branch subtract handles `w_fold` values up to 7 (subtract 6, subtract 3, or pass through), yielding the exact remainder 0, 1, or 2.

## Usage Examples

```systemverilog
// Round a beat count down to a whole number of 3-beat monbus records.
logic [15:0] beat_count;
logic [1:0]  beat_rem;
logic [15:0] rounded_count;

math_mod_3_compress u_mod3 (
    .d_in    (beat_count),
    .rem_out (beat_rem)
);

// rounded = X - (X mod 3)
assign rounded_count = beat_count - {14'b0, beat_rem};
```

## Design Notes

- **Why remainder only?** The div-by-15 reference computes a quotient; here only the residue is needed, so the quotient machinery is dropped, keeping the logic shallow.
- **Datapath width headroom.** `BITS = 6` (rather than the minimum 5 needed for a 0..24 sum) gives the weight-2 carry left-shifts room so the dropped top carry is always 0, matching the div-by-15 construction.
- **No inferred arithmetic primitives.** Because there is no `*` or `/`, synthesis produces adders and LUTs only, no DSP slices, no multi-cycle divider.
- **Purely combinational.** `rem_out` tracks `d_in` with no clock; register the result externally if a pipeline stage is desired.

## Testing

From the test suite (`val/math/test_math_mod_3_compress.py`):

- **Key test scenarios**:
  - Check rem_out == d_in % 3 across the 16-bit input space.

Run levels come from the standard grid: `REG_LEVEL=GATE|FUNC|FULL` selects the
parameter set, `TEST_LEVEL` the per-test depth. Run the whole area with
`make -C val/math run-all-func-parallel`, never bare pytest for suites.

## Related Modules

### Used By

- [monbus_compressor](../rtl-amba/monitor/monbus_compressor.md) - Rounds a beat count down to whole 3-beat records when packing monitor packets
- [monbus_group_core](../rtl-amba/monitor/monbus_group_core.md) - Shared filter/FIFO core of the monbus group wrappers

### Uses

- [math_adder_carry_save](../rtl-math/math_adder_carry_save.md) - The N-bit carry-save (3:2) compressor instantiated throughout the tree

### See Also

- `div_by_15_ceil_32compress.sv` - The reference implementation this module's compressor style follows

## References

### Source Code

- `rtl/math/math_mod_3_compress.sv`
- `rtl/math/math_adder_carry_save.sv` (instantiated submodule)
- `rtl/common/div_by_15_ceil_32compress.sv` (style reference)

### Documentation

- `docs/markdown/rtl-common/index.md`

**Last Updated:** 2026-07-15

## Navigation

- [Back to rtl-common Index](index.md)
