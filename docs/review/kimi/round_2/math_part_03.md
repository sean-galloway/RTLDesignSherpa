# Review: math_part_03 (RTL Math Library, part 3 of 3)

Scope: 4 doc files (`math_multiplier_wallace_tree.md`, `math_prefix_cell_gray.md`, `math_prefix_cell.md`, `math_subtractor.md`) against the supplied RTL. I recomputed instance counts, layer counts, and the formula table, and traced every module declaration and code example against the RTL port lists.

## Findings

```
[CONFIRMED] math_subtractor_ripple_carry documented with port names that do not exist; every usage example would fail to compile
  File:     docs/markdown/RTLCommon/math_subtractor.md
  Says:     "module math_subtractor_ripple_carry #( ... ) (
             input  logic         i_b_in,    // Borrow input
             output logic [N-1:0] ow_d,      // Difference
             output logic         ow_b       // Borrow output );"
            and three examples instantiate it as
            ".i_b_in(1'b0), .ow_d(diff), .ow_b(borrow)"
  Actually: rtl/math/math_subtractor_ripple_carry.sv declares
            "input logic i_borrow_in, output logic [N-1:0] ow_difference,
             output logic ow_carry_out". None of i_b_in, ow_d, ow_b exists,
            so all four instantiations in the doc (Basic Subtraction,
            Detecting Underflow, and both halves of Multi-Precision
            Subtraction) fail elaboration with unknown-port errors.
            Note: the documented interface is an exact match for
            math_subtractor_full_nbit (i_b_in/ow_d/ow_b) -- the declaration
            appears to have been written against that module and mislabeled.
  Impact:   Copy-pasted code does not compile; the borrow/underflow semantics
            the page is teaching cannot be exercised as written.
```

```
[CONFIRMED] math_subtractor_carry_lookahead documented input port i_b_in does not exist
  File:     docs/markdown/RTLCommon/math_subtractor.md
  Says:     "module math_subtractor_carry_lookahead #( ... ) (
             input  logic         i_b_in,    // Borrow input ...)"
  Actually: rtl/math/math_subtractor_carry_lookahead.sv has
            "input logic i_borrow_in". The documented outputs ow_d/ow_b do
            exist, but the RTL also exposes ow_difference and ow_borrow_out
            (aliased: "assign ow_d = ow_difference; assign ow_b =
            ow_borrow_out;"), which the doc's declaration and port table
            omit entirely.
  Impact:   An instantiation following the documented port list fails to
            elaborate. Secondary gap: two real output ports undocumented.
```

```
[CONFIRMED] "The _csa_ Variant" table claims the final CPA cell is math_adder_full, contradicting the RTL and the same page
  File:     docs/markdown/RTLCommon/math_multiplier_wallace_tree.md
  Says:     "| Final CPA cell | `math_adder_full` | `math_adder_full` |"
  Actually: The RTL instantiates "math_adder_brent_kung_016 #(.N(16))
            u_final_cpa" (and _032/_064 in the wider variants) as the final
            CPA. The same page states twice that "The final CPA is the same
            `math_adder_brent_kung_{2N}` instance in **both** variants", and
            the whole page's thesis is the Brent-Kung final adder. This row
            is stale text (the _csa_ RTL is not in the bundle, but the
            "Plain variant" column is directly falsified by
            rtl/math/math_multiplier_wallace_tree_008.sv).
  Impact:   A reader comparing the two variants is told the CPA is built
            from full adders, undermining the page's area/delay accounting.
```

```
[CONFIRMED] Gray-cell page asserts Brent-Kung reverse-tree gray cells "never" take a single-bit generate -- the library's Brent-Kung does exactly that in its fill level
  File:     docs/markdown/RTLCommon/math_prefix_cell_gray.md
  Says:     "A gray cell in the Brent-Kung reverse tree always pairs a
            *group* generate/propagate with an already-complete carry; it
            never takes a single-bit `G[i:i]` against `G[i-1:-1]`. That
            single-bit pattern is the Han-Carlson final fill-in stage shown
            above, not Brent-Kung."
  Actually: rtl/math/math_adder_brent_kung_grouppg_016.sv contains
            gray_block_2_1, gray_block_4_3, gray_block_6_5, gray_block_8_7,
            gray_block_10_9, gray_block_12_11, gray_block_14_13,
            gray_block_16_15, e.g.
            "math_adder_brent_kung_gray gray_block_2_1 (
                .i_g(i_g[2]), .i_p(i_p[2]), .i_g_km1(ow_gg[1]), ...)"
            -- single-bit i_g[2] against complete carry ow_gg[1], the exact
            pattern claimed not to exist in Brent-Kung. The same paragraph
            also says "Positions 2, 4, 8 are exactly what the reverse tree
            still has to fill", and those positions are filled by these
            single-bit cells, so the section contradicts itself as well.
            (The span-2 example given, gray_block_5_3 wiring G_5_4/P_5_4
            against ow_gg[3], is accurate.)
  Impact:   Reader learns a false structural rule about this library's
            Brent-Kung adders and a wrong Brent-Kung/Han-Carlson distinction.
```

```
[SUSPECTED] Cited file math_adder_brent_kung_grouppg_008.sv is not in the RTL bundle
  File:     docs/markdown/RTLCommon/math_prefix_cell_gray.md
  Says:     "This mirrors `gray_block_5_3` in
            `math_adder_brent_kung_grouppg_008.sv`, which wires `G_5_4`/
            `P_5_4` against `ow_gg[3]`."
  Actually: No grouppg_008 file is present in the supplied RTL (only
            grouppg_016/032/064). An instance named gray_block_5_3 with
            exactly those connections does exist in
            math_adder_brent_kung_grouppg_016.sv, so the substance is
            correct; I could not confirm the 008 file exists.
  Impact:   Possibly a dangling reference to a file that was never generated.
```

```
[SUSPECTED] "Speed (relative)" column in the architecture comparison table is internally inconsistent and inconsistent with the rest of the page
  File:     docs/markdown/RTLCommon/math_multiplier_wallace_tree.md
  Says:     "| Array Multiplier | 0.8× | 2.5× | Low-speed, minimal area |
             | Booth (radix-4)  | 0.9× | 1.5× | Signed, reduced ... |"
            with Wallace at "1.0×" speed.
  Actually: Read as speed, this claims an array multiplier is 2.5x faster
            than a Wallace tree -- contradicting the row's own "Low-speed"
            use case and the page's O(log N) vs O(N) depth analysis. The
            numbers are plausibly relative *delay* mislabeled. Unsourced
            either way (timing-table estimates are a known weak area; the
            new detail here is the self-contradiction).
  Impact:   Reader comparing architectures gets the speed ordering backwards.
```

## POSSIBLE RTL BUGS

No functional bugs found. One lint-level observation: the Wallace-tree RTL leaves the carry output of the last column's final half adder unread -- `w_carry_15_4_01` in `_008`, `w_carry_31_4_01`, `w_carry_31_5_01`, `w_carry_31_6_01` in `_016`, and five `w_carry_63_{4..8}_01` wires in `_032`. These are driven but unconsumed (UNUSEDSIGNAL warnings; only the CPA's carry-out is covered by a lint waiver). They are functionally harmless -- each represents product bit 2N, which is always 0 since (2^N−1)² < 2^(2N) -- but the doc's "carry-out is left unread on `w_cpa_carry_unused`" note describes only one unread carry, not N/4−1 of them. The counts cross-check: for `_016`, 256 partial products − 196 full adders = 60 surviving bits = 57 CPA inputs + 3 unread carries, exactly as traced.

## Overall accuracy

The Wallace tree page is unusually well-verified and almost everything checkable passed: layer counts (4/6/8) match the RTL layer comments; I counted the reduction cells exactly for `_008` (36 FA / 25 HA) and `_016` (196 FA / 78 HA), matching the doc's tables; the `_032` FA count (900) is consistent with bit conservation; the layer-count formula table recomputes correctly (⌈log₁.₅(N)⌉ = 6/7/9, ⌈log₁.₅(N/2)⌉ = 4/6/7 vs measured 4/6/8); the "verbatim" RTL excerpts are verbatim; and the Brent-Kung CPA identities, widths, and unused-carry wiring all match. The prefix-cell pages are correct on equations, port lists, and the grouppg_016 cell census (I counted 11 black / 16 gray, matching). The black-cell page is clean. The two real defect clusters are the subtractor page's port names (declaration and all ripple-carry examples use the `math_subtractor_full_nbit` interface, not the actual `math_subtractor_ripple_carry` interface, so none of them compile) and the two stale/overreaching claims noted above. Claims I could not verify from the supplied bundle (the `_csa_` multiplier variants, Dadda cell counts, Han-Carlson files, `math_adder_carry_save`) are marked as such; everything flagged CONFIRMED points at a specific contradicting RTL line.