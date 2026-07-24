# Review: common_part_05 (`sort.md`, `sync_pulse.md`)

Two modules reviewed against `rtl/common/sort.sv` and `rtl/common/sync_pulse.sv`. I traced the sort example pass-by-pass against the compare-swap logic, recomputed the sync_pulse latency from the shift-register structure, and checked the pulse-spacing arithmetic in both worked examples.

---

## Findings

```
[CONFIRMED] Reset described as clearing "when deasserted" — polarity inverted, twice
  File:     docs/markdown/RTLCommon/sort.md
  Says:     "| rst_n | 1 | Reset | Active-low asynchronous reset. Clears all pipeline
            stages when deasserted. |" and "**Asynchronous Reset**: All pipeline
            stages are cleared when rst_n is deasserted"
  Actually: The RTL clears the pipeline while rst_n is ASSERTED (low):
            `ALWAYS_FF_RST(clk, rst_n, if (`RST_ASSERTED(rst_n)) begin
                r_stage_data[stage] <= '0; ...`
            Deassertion (rst_n high) is the normal operating state.
  Impact:   A reader gets the reset polarity backwards — thinks clearing happens when
            rst_n goes high. Exactly the kind of error that propagates into a
            testbench or integration.
```

```
[CONFIRMED] NUM_VALS documented range 2-32 / "tested 3-32" vs RTL range 2 to 16
  File:     docs/markdown/RTLCommon/sort.md
  Says:     "| NUM_VALS | 5 | 2-32 | ..." (parameter table) and "NUM_VALS can be any
            reasonable value (tested 3-32)" (Special Features)
  Actually: RTL header: "NUM_VALS ... Range: 2 to 16". There is no enforcement in
            the code, so the header's stated range is the only ground truth, and
            the doc disagrees with it twice (2-32 vs 2-16; also "tested 3-32"
            excludes the documented minimum of 2).
  Impact:   Low — the generate logic is generic so 32 would likely function, but a
            reader cannot tell which range is actually supported/validated.
```

```
[CONFIRMED] "1-2 gate delays" critical path contradicts the doc's own synthesis table
  File:     docs/markdown/RTLCommon/sort.md
  Says:     "**Critical Path**: One compare-swap operation (typically 1-2 gate delays)"
            vs. its own table three sections later: "5×16-bit ... Critical Path
            ~1.5ns", "8×32-bit ... ~2.0ns"
  Actually: A compare-swap is a SIZE-bit magnitude comparator feeding a 2:1 mux —
            several logic levels. At typical FPGA gate delays (~50-100 ps), the
            doc's own ~1.5 ns figure corresponds to roughly 15-30 gate delays, not
            1-2. The prose and the table cannot both be true.
  Impact:   A reader budgeting timing at high frequency gets a wildly optimistic
            picture from the prose.
```

```
[CONFIRMED] Algorithm table claims O(1) space for a network the RTL says is O(N^2)
  File:     docs/markdown/RTLCommon/sort.md
  Says:     "| **Odd-Even Sort** | O(n²) | O(1) | ⭐⭐⭐⭐⭐ Excellent | n | ..."
            (Space Complexity column)
  Actually: RTL header: "Resource usage: O(NUM_VALS^2) comparators,
            O(NUM_VALS^2 * SIZE) registers" — confirmed by the structure: ~NUM_VALS/2
            compare-swap pairs per stage × NUM_VALS flopped stages. O(1) space
            describes the software in-place algorithm, not this pipelined network,
            in a table whose other columns (Pipeline Stages, Hardware Efficiency)
            are explicitly about hardware.
  Impact:   Moderate — a reader estimating area from this table expects constant
            space; actual area grows quadratically with NUM_VALS.
```

```
[SUSPECTED] sync_pulse latency "(SYNC_STAGES + 2)" overcounts; breakdown invents two registered stages
  File:     docs/markdown/RTLCommon/sync_pulse.md
  Says:     "**Latency**: `(SYNC_STAGES + 2)` destination clock cycles" and the
            breakdown: "2. Synchronizer stages: 3 ... 3. Edge detection: 1
            destination clock 4. Output pulse generation: 1 destination clock"
  Actually: o_pulse = r_sync[SYNC_STAGES-1] ^ r_sync_prev is combinational; the
            pulse STARTS the same dst cycle r_sync[SYNC_STAGES-1] updates — only
            the pulse END waits for r_sync_prev. Recomputation for SYNC_STAGES=3:
            toggle flips at src edge; worst case ~1 T_dst alignment to capture
            into r_sync[0]; r_sync[1] at edge 2; r_sync[2] at edge 3, and o_pulse
            goes high at that moment. So 2-3 T_dst from the toggle flip (plus up
            to 1 T_src from i_pulse), not 5 T_dst. The doc's own timing diagram
            shows o_pulse rising aligned with r_sync[2], consistent with my count,
            not with the "+2". The RTL header repeats the same formula, so the doc
            is faithful to its source; the number errs conservatively by ~1 cycle.
  Impact:   Low — conservative latency is harmless for design, but the breakdown
            teaches a wrong mental model (edge detection is not a pipeline stage).
```

```
[SUSPECTED] MTBF ">10^12 hours" stated as fact with no basis
  File:     docs/markdown/RTLCommon/sync_pulse.md
  Says:     "**MTBF**: >10^12 hours @ SYNC_STAGES=3, 100MHz" (and "3 stages:
            Recommended for most applications (>10^12 hours MTBF)")
  Actually: No metastability parameters (τ, T0), process node, or measurement is
            cited anywhere; the RTL header repeats the identical figure. MTBF
            cannot be stated as a bare constant — it depends on flop technology
            and data rate. Unsupported claim presented as a specification.
  Impact:   Low-moderate — readers doing safety/reliability analysis may quote it.
```

Checked and **found correct** (no findings): the full sort example trace (I re-ran all 5 passes against the swap condition `w_values[i] < w_values[i+1]` → larger to lower index; every intermediate result matches); latency NUM_VALS cycles for sort; port/parameter lists for both modules; the formal assertions quoted in sync_pulse.md (present verbatim under `` `ifdef FORMAL``); the spacing-example arithmetic (3×40+2×10=140 ns = 14 src clocks ✓; 3×10+2×100=230 ns = 2.3 src clocks ✓); the FF count SYNC_STAGES+2 in the resource table; packing convention (element 0 at LSB ✓).

---

## POSSIBLE RTL BUGS

1. **`rtl/common/sort.sv` header comment states the wrong sort direction.** Header says "Sorts NUM_VALS values in **ascending order**" and "Output: Sorted **ascending order (smallest at LSB)**". The compare-swap logic swaps when `w_values[i] < w_values[i+1]`, placing the **larger** value at the **lower** index, and element 0 maps to the LSB (`w_values[0][i] = w_stage_data_0[i*SIZE +: SIZE]`). The output is therefore **descending with the largest value at the LSB**. The documentation (sort.md) correctly says descending — it is the RTL header comment that is inverted. Verified by tracing `[5,3,8,1,9]` → `[9,8,5,3,1]` through the actual logic.

2. **`rtl/common/sync_pulse.sv` header documents a feedback path that does not exist.** Protocol step 4: "Destination toggle is synchronized back to source for ready." The module has no reverse synchronizer, no `ready`/`o_ready` port, and no source-domain logic beyond `r_src_toggle`. The doc page under review does **not** repeat this claim (good), but the RTL header advertises a phantom handshake feature.

3. **`rtl/common/sync_pulse.sv` header is internally inconsistent on minimum spacing:** "Min Pulse Gap: 3 destination clock cycles" in the Timing section vs. "Minimum spacing = 3*T_dst + 2*T_src" in the Protocol section of the same header.

4. **Minor:** the `sort.sv` header parameter section documents only `NUM_VALS`; `SIZE` is omitted from the RTL header entirely (the doc page covers it, so no reader-facing gap, but the RTL self-documentation is incomplete).

---

## Overall accuracy

This unit is in good shape relative to most of the corpus. The structural claims — pipeline organization, pass parity, packing, port lists, parameter defaults, the quoted code snippets, and the formal assertions — all check out against the RTL, and the worked examples (sort trace, spacing arithmetic) are numerically correct. The defects that remain are concentrated in quantitative prose: an inverted reset-polarity description (the most damaging item, appearing twice), a parameter range that disagrees with the RTL header, a physically implausible "1-2 gate delays" critical-path claim that contradicts the doc's own synthesis table, an O(1) space claim that contradicts the O(N²) reality of the network, and a sync_pulse latency formula that double-counts the combinational edge detector. The most interesting findings are on the RTL side: the sort header states the sort direction backwards (the doc is right, the comment is wrong), and the sync_pulse header describes a nonexistent ready-feedback path.