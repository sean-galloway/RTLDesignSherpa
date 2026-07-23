# Review: common_part_05 (sort.md, sync_pulse.md)

## Method

For `sort` I hand-simulated the RTL compare-swap network on the doc's worked example and verified the packing, pass parity, latency, and valid-propagation table line by line. For `sync_pulse` I compared every code excerpt in the doc against the RTL (toggle register, shift synchronizer, XOR edge detect, assertions) and checked the arithmetic in the worked spacing examples. Both docs are unusually close to the RTL; the confirmed defects are few and mostly minor.

## Findings

```
[CONFIRMED] Reset polarity wording is inverted (says stages clear when rst_n is "deasserted")
  File:     docs/markdown/RTLCommon/sort.md
  Says:     "| `rst_n` | 1 | Reset | Active-low asynchronous reset. Clears all
            pipeline stages when deasserted. |"
            and "- **Asynchronous Reset**: All pipeline stages are cleared when
            `rst_n` is deasserted"
  Actually: The RTL clears the pipeline when rst_n is *asserted* (driven low):
            `ALWAYS_FF_RST(clk, rst_n, if (`RST_ASSERTED(rst_n)) begin
            r_stage_data[stage] <= '0; ...` — the macro's active-low semantics
            are confirmed by the sync_pulse doc's expansion of the same macro:
            `always_ff @(posedge i_src_clk or negedge i_src_rst_n) if (!i_src_rst_n)`.
            Deassertion (rst_n → 1) is when the pipeline starts running.
  Impact:   The sentence contradicts itself ("active-low ... when deasserted").
            A reader skimming the second half gets the reset polarity backwards.
```

```
[CONFIRMED] Documented NUM_VALS range (2-32) disagrees with the RTL header (2 to 16)
  File:     docs/markdown/RTLCommon/sort.md
  Says:     "| `NUM_VALS` | 5 | 2-32 | ..." and "`NUM_VALS` can be any reasonable
            value (tested 3-32)"
  Actually: rtl/common/sort.sv header: "//     Range: 2 to 16". Nothing in the
            RTL enforces either bound (there is no parameter-validation block,
            unlike sync_pulse), and the generate logic works for any NUM_VALS≥2,
            so this is purely a documentation-of-support mismatch: the doc
            vouches for 17–32 (and claims testing to 32) while the module's own
            header caps the range at 16.
  Impact:   A reader may instantiate NUM_VALS=24 believing it is a tested,
            supported configuration when the RTL author only warrants ≤16
            (or, reading both sources, cannot tell which to believe).
```

```
[SUSPECTED] "Critical path ... typically 1-2 gate delays" is implausible and
            inconsistent with the doc's own numbers
  File:     docs/markdown/RTLCommon/sort.md
  Says:     "- **Critical Path**: One compare-swap operation (typically 1-2 gate delays)"
  Actually: A compare-swap is a SIZE-bit unsigned comparator feeding a 2:1 swap
            mux. For the default SIZE=16 that is several logic levels, not 1-2
            gate delays; the doc's own synthesis table two sections later gives
            ~1.5 ns for 5×16-bit, which is tens of gate delays in any modern
            process. (Falls under the already-known "unsourced timing numbers"
            weakness; reported only because it is internally inconsistent prose,
            not a table.)
  Impact:   Minor; may mislead a reader doing back-of-envelope frequency planning.
```

```
[SUSPECTED] MTBF figure presented as fact with no derivation
  File:     docs/markdown/RTLCommon/sync_pulse.md
  Says:     "- **MTBF**: >10^12 hours @ SYNC_STAGES=3, 100MHz" and "**3 stages**:
            Recommended for most applications (>10^12 hours MTBF)"
  Actually: No calculation, process parameters (τ, T0), or measurement backs
            this number; it is restated from the sync_pulse.sv header. MTBF is
            strongly process- and temperature-dependent, so a single number for
            all targets is not supportable.
  Impact:   Low for hobby use, but a reader in a high-reliability context could
            cite a number that has no basis for their silicon.
```

## POSSIBLE RTL BUGS (comment-level only; no functional bugs found)

1. **`rtl/common/sort.sv` header states the wrong sort order.** Header says: "Sorts NUM_VALS values in **ascending order**" and "Output: Sorted ascending order (**smallest at LSB**)". The implemented logic does the opposite: each compare swaps when `w_values[stage-1][i] < w_values[stage-1][i+1]`, placing the *larger* value at the lower index, so after NUM_VALS passes element 0 (bits `[SIZE-1:0]`, the LSB slice) holds the **maximum**. I hand-traced the doc's example `[5,3,8,1,9]` through all five stages of the actual RTL and got `[9,8,5,3,1]` at elements [0..4] — descending, largest at LSB — matching the doc exactly. The doc is correct; the RTL header comment contradicts the RTL logic. Either the comment or a stale intent should be fixed.

2. **`rtl/common/sync_pulse.sv` header describes logic that does not exist.** Protocol item 4: "Destination toggle is synchronized back to source for ready." The module has no source-domain synchronizer and no ready output — only `r_src_toggle`, `r_sync`, `r_sync_prev`, and the XOR. The doc (correctly) does not repeat this claim. Header comment should be deleted.

3. Minor: the `sort.sv` header documents only `NUM_VALS`; the `SIZE` parameter is absent from its parameter section.

## What I checked that was correct

- The full worked example in sort.md (all 5 passes) matches a stage-by-stage simulation of the RTL, including pass parity (`IS_ODD_PASS = ((stage-1) % 2) == 0`), swap condition, and final result.
- Latency claim "NUM_VALS cycles from valid_in to done" and the 6-cycle valid-propagation table for NUM_VALS=5: `done = r_stage_valid[STAGES]`, and valid shifts one stage per clock — exact match.
- Packing format `data[i*SIZE +: SIZE]`, combinational stage 0, descending order, throughput of 1 array/cycle, compare-swap code excerpt, and signal naming conventions — all verbatim-accurate against the RTL.
- sync_pulse: module declaration, parameter default/range (enforced by the RTL's `initial` validation block), all three code excerpts (toggle, shift synchronizer, XOR edge detect), both `FORMAL` assertions, FF count (SYNC_STAGES+2), and both min-spacing arithmetic examples (140 ns = 14 src clocks; 230 ns → round up to 3 src clocks) check out. Latency "(SYNC_STAGES+2) dst cycles" matches the RTL header and is a defensible bound; the "Latency Breakdown" subsection's separate "+1 dst clock" each for edge detection and output generation is muddled (the XOR is combinational and asserts the same cycle `r_sync[SYNC_STAGES-1]` changes) but the totals agree, so I did not count it as a defect.

## Overall

This is one of the more accurate units in the library: both documents track their RTL closely, the sort example is genuinely correct rather than decorative, and the sync_pulse excerpts compile against the real ports and logic. The confirmed doc defects are two: an inverted "cleared when deasserted" reset phrase in sort.md, and a NUM_VALS range (2–32, "tested 3–32") that exceeds the RTL header's stated 2–16. The more interesting findings are on the RTL side — the sort header documents the opposite sort order from what the logic implements, and the sync_pulse header describes a feedback synchronizer that was never built — both of which the documentation got *right* by ignoring. Fix the two RTL header comments and the reset wording, and reconcile the NUM_VALS range, and this pair of pages is in good shape.