# Review: math_part_03 (3 docs, 2 RTL modules)

## Findings

```
[CONFIRMED] Entire subtractor page documents five modules that do not exist in the RTL
  File:     docs/markdown/RTLCommon/math_subtractor.md
  Says:     "This document covers the complete subtractor module family:
             - math_subtractor_half ... - math_subtractor_full ...
             - math_subtractor_full_nbit ... - math_subtractor_ripple_carry ...
             - math_subtractor_carry_lookahead"
            followed by full module declarations, parameter tables (N, default 4,
            range 1-64), port tables, and instantiation examples for these modules,
            plus "math_addsub_full_nbit.sv - Combined add/subtract unit" in Related Modules.
  Actually: RTL.sv for this unit contains exactly two modules, math_prefix_cell and
            math_prefix_cell_gray, and its banner states "2 documented modules +
            0 dependencies". None of the five subtractor modules (or
            math_addsub_full_nbit) are present in the ground truth. The page's
            primary subjects were never matched to any RTL.
  Impact:   A reader will instantiate math_subtractor_ripple_carry etc. with the
            documented ports and parameters and get elaboration errors. Every port
            table, parameter default, timing figure, and example on this page is
            unverifiable and likely describes unwritten modules. This is the most
            damaging defect in the unit.
```

```
[CONFIRMED] Brent-Kung "reverse tree" example mislabels every signal; the pairing is not Brent-Kung
  File:     docs/markdown/RTLCommon/math_prefix_cell_gray.md
  Says:     "// Example: Position 5 gets carry from positions 5 and 4
             math_prefix_cell_gray u_bk_gray_5 (
                 .i_g_hi(w_g[5]),    // G[5:5] (from forward tree)
                 .i_p_hi(w_p[5]),    // P[5:5] (original propagate)
                 .i_g_lo(w_g[4]),    // G[4:-1] (computed in forward tree)
                 .ow_g(w_g_5_final)  // G[5:-1] (carry into position 6));"
  Actually: In a Brent-Kung network the forward tree computes, in stage 1, all odd
            positions: position 5 holds G[5:4]/P[5:4], not G[5:5]/P[5:5]. Position 4
            never receives a complete carry from the forward tree; it is filled in the
            final reverse stage. The reverse-tree cell at position 5 pairs with
            position 3: G[5:0] = G[5:4] | (P[5:4] & G[3:0]). The documented pattern
            (single-bit G/P at position 5 combined with a complete G[4:-1]) is the
            Han-Carlson final-stage pattern the page itself describes in the previous
            example, not a Brent-Kung reverse tree.
  Impact:   A reader building a Brent-Kung adder from this example will wire the wrong
            spans and mislabel the group signals; the example contradicts the algorithm
            the page claims to illustrate.
```

```
[CONFIRMED] Prefix-network cell-count table overcounts, Brent-Kung by more than 2x
  File:     docs/markdown/RTLCommon/math_prefix_cell_gray.md
  Says:     "| Kogge-Stone N=16 | 64 | 0 | 64 |
             | Brent-Kung N=16 | ~30 | ~30 | ~60 |
             | Han-Carlson N=16 | ~32 | 8 | ~40 |"
  Actually: Recomputation for 16-bit networks:
            - Kogge-Stone: 15+14+12+8 = 49 black cells (N·log2N − N + 1 = 64 − 15).
              64 counts buffered grid positions, not cells.
            - Brent-Kung: forward 8+4+2+1 = 15 cells, reverse 1+3+7 = 11 cells,
              total 26 (2N − 2 − log2N). "~30 black + ~30 gray = ~60" is ~2.3x the
              real total; a realistic split is ~15 black / ~11 gray.
            - Han-Carlson in the page's own orientation (black cells on even
              positions, gray fill on odd): 7 + 6+5+3 = 21 black, 8 gray, total 29
              (the alternate parity gives 25 black / 7 gray / 32 total) — not ~40.
  Impact:   Readers sizing an adder or comparing architectures get area figures
            inflated 30–130%, and the "area savings" narrative built on the table is
            quantitatively wrong.
```

```
[CONFIRMED] "Only power-of-2 positions have complete carries" after the Brent-Kung forward tree — wrong positions
  File:     docs/markdown/RTLCommon/math_prefix_cell_gray.md
  Says:     "After forward tree, only power-of-2 positions have complete carries"
  Actually: With the 0-based bit indexing used throughout the page (w_g[5], w_g[4]),
            the positions holding complete carries after a BK16 forward tree are
            1, 3, 7, 15 (i.e., 2^k − 1): stage 1 completes position 1, stage 2
            completes position 3, stage 3 position 7, stage 4 position 15. Powers of
            two (2, 4, 8) are precisely the positions filled last by the reverse tree.
            The sentence is only true under a 1-based carry indexing, which the page's
            own examples do not use — and the very next example relies on the incorrect
            reading by claiming G[4:-1] comes from the forward tree.
  Impact:   Reinforces the incorrect example above; a reader mislearns the structure
            of the Brent-Kung forward tree.
```

```
[CONFIRMED] (minor) Black-cell critical path names the wrong input
  File:     docs/markdown/RTLCommon/math_prefix_cell.md
  Says:     "| Critical Path | AND-OR | i_g_hi/i_p_hi -> ow_g |"
  Actually: RTL: "assign ow_g = i_g_hi | (i_p_hi & i_g_lo);" — i_g_hi passes through
            only the OR gate (depth 1), so it cannot be on the AND-OR critical path.
            The depth-2 paths are i_p_hi -> ow_g and i_g_lo -> ow_g. The gray-cell
            page correctly states "i_g_lo -> ow_g", so the two sibling pages also
            disagree.
  Impact:   Minor; a designer balancing input arrival times would optimize the wrong
            pin.
```

```
[CONFIRMED] (minor) Subtractor "Modern Approach" example uses an undeclared signal
  File:     docs/markdown/RTLCommon/math_subtractor.md
  Says:     "logic [7:0] a, b, diff;
             logic borrow;
             math_adder_ripple_carry #(.N(8)) u_add (
                 ... .ow_sum(diff), .ow_carry(carry_out) );
             assign borrow = ~carry_out;"
  Actually: carry_out is never declared in the snippet (only a, b, diff, borrow are),
            so the example does not compile as written. (The referenced adder's ports
            cannot be checked — it is not in this unit's RTL either.)
  Impact:   Minor; a copy-paste user hits an immediate compile error. Moot if finding
            1 removes the page, since the same undeclared-variable style recurs in it.
```

## POSSIBLE RTL BUGS

- `rtl/common/math_prefix_cell_gray.sv` header comment reads "Module: math_prefix_cell" — a copy-paste from `math_prefix_cell.sv`; it should name `math_prefix_cell_gray`. Comment-only, trivial, but it is exactly the kind of thing that confuses file-level searches.

## Overall accuracy

The two prefix-cell pages are, at the module level, excellent: port lists, module declarations, and logic equations match the RTL verbatim, the black/gray theory is correct, and the gate-count (2 vs 3, ~33%) and delay claims check out. Their defects are in the architectural narrative around the cells — a wrong Brent-Kung reverse-tree example, a wrong statement of which positions the BK forward tree completes, and a cell-count table that overcounts every row (Brent-Kung by more than 2x) — plus one mislabeled critical-path input. The third page, `math_subtractor.md`, is wholly unsupported: it documents five modules with full interfaces and examples, none of which exist in the RTL. Until those modules are written, that page should be pulled or clearly marked as aspirational; it is the only finding here that would send a reader after hardware that does not exist.