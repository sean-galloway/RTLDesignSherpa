# Review: common_part_04 (18 files)

I checked every documented port list, parameter, truth table, and worked numeric example against `RTL.sv`. Truth tables for `hex_to_7seg` (all 16 rows), `gray2bin` (all 8 rows), `find_first_set`/`find_last_set`, `reset_sync` state sequence, `shifter_barrel` rotation examples, `shifter_universal` waveforms, and the `shifter_lfsr_fibonacci` cycle example all verify clean. The failures cluster in worked numeric examples that contradict the (correct) code shown on the same page.

## Findings

```
[CONFIRMED] johnson2bin.md — both worked decode examples use wrong position values and produce wrong binary results
  File:     docs/markdown/RTLCommon/johnson2bin.md
  Says:     "Johnson: 001111 (w_leading_one = 5, w_trailing_one = 2) ... position = w_leading_one + 1 = 5 + 1 = 6 ... Binary: 000110"
            and "Johnson: 111000 (w_leading_one = 0, w_trailing_one = 2) ... Binary: 100010"
  Actually: For 6'b001111 the set bits are {0,1,2,3}, so find_last_set → w_leading_one = 3 (not 5) and
            find_first_set → w_trailing_one = 0 (not 2). gray[5]=0 → first half →
            w_binary = leading_one+1 = 4 → binary = {1'b0, 000100} = 000100, not 000110.
            For 6'b111000 the set bits are {3,4,5} → w_leading_one = 5 (not 0), w_trailing_one = 3 (not 2).
            gray[5]=1 → second half → w_binary = trailing_one = 3 → binary = {1'b1, 000011} = 100011, not 100010.
            The page's own sequence table confirms this: 001111 is "State 4" and 111000 is "State 9"
            (second-half address = 9−6 = 3), matching the RTL, not the examples.
  Impact:   A reader building a reference model from these examples gets wrong expected values. The
            examples also contradict the page's own (correct) algorithm code block two sections up.
```

```
[CONFIRMED] johnson2bin.md — special-case table claims all-ones decodes to 000000; RTL forces the wrap MSB to 1
  File:     docs/markdown/RTLCommon/johnson2bin.md
  Says:     "Johnson: 111111 → Binary: 000000 (all ones case - same as zeros)"
  Actually: The RTL sets the lower bits to 0 for all-ones but then unconditionally does
            `assign binary[WIDTH-1] = gray[JCW-1];` — and gray[JCW-1] = 1 for 111111.
            So 111111 → binary = 1000 (WIDTH=4), not 000000. Only all-zeros yields 0.
            The page itself states "MSB = wrap indicator" in the Three-Part Binary Construction section.
  Impact:   FIFO full detection relies on all-ones decoding to {wrap=1, addr=0} — the exact opposite of
            "same as zeros". A reader implementing the doc's table breaks full/empty comparison.
```

```
[CONFIRMED] pwm.md — repeat-count examples contradict RTL: RTL emits repeat_count+1 periods, doc shows repeat_count
  File:     docs/markdown/RTLCommon/pwm.md
  Says:     "Multi-Repeat Example (repeat_count=2): Period: 1     2     DONE" and the servo example
            "repeat_count = 1;         // Single pulse"
  Actually: RTL: w_all_repeats_done = (r_repeat_value >= local_repeat), and r_repeat_value only
            increments at a period boundary. Trace for local_repeat=2:
              period 1 ends: 0>=2 false → r_repeat_value→1
              period 2 ends: 1>=2 false → r_repeat_value→2
              period 3 ends: 2>=2 true  → DONE
            → 3 periods for repeat_count=2, and 2 pulses for repeat_count=1 ("single pulse").
  Impact:   Every finite-repeat user gets one extra period per channel; the single-shot servo use
            case produces two pulses. See also POSSIBLE RTL BUGS — the RTL header's own waveform
            also depicts 2 periods for repeat=2, so the RTL is likely the buggy side.
```

```
[CONFIRMED] pwm.md — sync_rst_n port is missing from the documentation entirely
  File:     docs/markdown/RTLCommon/pwm.md
  Says:     Inputs table lists only "clk, rst_n, start, duty, period, repeat_count"; the Reset Behavior
            note mentions only "Asynchronous reset".
  Actually: RTL port list includes `input logic sync_rst_n, // Synchronous reset`, and all four
            always blocks have `else if (!sync_rst_n)` branches resetting state, counters, and
            edge-detect. It is a functional reset, not a tie-off.
  Impact:   A user instantiating per the doc leaves sync_rst_n unconnected (X in simulation, spurious
            resets in hardware) and never learns the synchronous reset exists.
```

```
[CONFIRMED] INSTANCE_NAME parameter documented for three modules; it exists in none of them
  File:     docs/markdown/RTLCommon/find_first_set.md — "INSTANCE_NAME - String identifier for debug (default: "FFS")"
            docs/markdown/RTLCommon/find_last_set.md  — same, default "FLS"
            docs/markdown/RTLCommon/leading_one_trailing_one.md — "INSTANCE_NAME: ... (default: "")"
  Actually: All three RTL modules declare exactly one parameter: `parameter int WIDTH`.
            No INSTANCE_NAME (or any string parameter) exists.
  Impact:   A reader passing .INSTANCE_NAME("...") gets an elaboration error; readers may also
            expect debug output that does not exist.
```

```
[CONFIRMED] shifter_lfsr.md — worked 3-bit sequence is wrong at step 3 and implies a period-3 cycle
  File:     docs/markdown/RTLCommon/shifter_lfsr.md
  Says:     "Step 3: 101 | ~(1^0)=1 | 011" (and step 4 then shows 011 → 110, closing a 011→110→101 loop)
  Actually: r_lfsr=101, taps [3,2] → w_taps=3'b110. 101 & 110 = 100; ^100 = 1; ~^ = 0.
            Feedback is 0, so next = {r_lfsr[1:0], 1'b0} = 010, not 011. The doc's own arithmetic
            is also wrong: ~(1^0) = ~1 = 0, not 1. Correct RTL sequence from 001:
            011, 110, 101, 010, 100, 000, 001 — period 7, matching the page's "Max Period 7" claim,
            which the doc's broken loop (period 3) contradicts.
  Impact:   A reader hand-checking the module against the example concludes the RTL is broken when
            it is the example that is wrong.
```

```
[CONFIRMED] shifter_lfsr_galois.md — worked timing example diverges from the RTL on the very first transition
  File:     docs/markdown/RTLCommon/shifter_lfsr_galois.md
  Says:     Cycle 0: LFSR=1001, taps [4,3], LSB=1 → "Next LFSR 1110"; cycle 2: 0111 → 1010.
  Actually: From 1001: right-shift gives 0100; LSB=1 so the RTL toggles index 3 (0100→1100) then
            index 2 (1100→1000). Next state = 1000, not 1110. From 0111: shift → 0011, toggle
            index 3 → 1011, toggle index 2 → 1111; doc says 1010. Every XOR-affected row diverges.
  Impact:   Same class as above — the example teaches a sequence this RTL never produces.
```

```
[CONFIRMED] glitch_free_n_dff_arn.md — prose claims "Synchronous reset"; the module is asynchronous-reset
  File:     docs/markdown/RTLCommon/glitch_free_n_dff_arn.md
  Says:     "### Reset Behavior — **Synchronous reset**: Uses destination domain reset"
  Actually: The RTL uses `ALWAYS_FF_RST(clk, rst_n, ...)`; the RTL header states "Asynchronous reset
            for all pipeline stages", and the doc's own code block on the same page shows
            `always_ff @(posedge clk or negedge rst_n)`. The module name suffix "arn" itself means
            async reset, active-low.
  Impact:   Reader is misinformed about reset assertion behavior, contradicting the code on the
            same page.
```

```
[CONFIRMED] glitch_free_n_dff_arn.md — "Further reduces MTBF" states the opposite of the truth
  File:     docs/markdown/RTLCommon/glitch_free_n_dff_arn.md
  Says:     "**Stage 3+ (FFN)**: Further reduces MTBF (Mean Time Between Failures)"
  Actually: Additional stages increase MTBF — the page's own table two sections later shows
            1× / ~1000× / ~1,000,000× / ~1,000,000,000× for 1/2/3/4 stages.
  Impact:   Reversed meaning (less reliability with more stages); internally contradicted by the
            adjacent table, so mostly confusing rather than dangerous.
```

```
[CONFIRMED] johnson2bin.md — "Filling/Emptying from left" contradicts the page's own sequence table and callout
  File:     docs/markdown/RTLCommon/johnson2bin.md
  Says:     "**First half** (0 to DEPTH-1): Filling with 1s from left" and "**Second half** ... Emptying 1s from left"
  Actually: The page's sequence table (000000 → 000001 → 000011 → ... → 111111 → 111110 → ...) and
            its highlighted callout ("ones enter at bit 0 and march upward... An earlier revision of
            this page showed the mirror image") both show fill/empty starting at the LSB — the right
            end as written. "From left" is exactly the mirror-image error the callout warns about.
  Impact:   Low, but it reintroduces the very confusion the page's correction note was added to fix.
```

```
[CONFIRMED] leading_one_trailing_one.md — claims index outputs are "undefined" for all-zero input; they are deterministically 0
  File:     docs/markdown/RTLCommon/leading_one_trailing_one.md
  Says:     "Index values are undefined but bounded" (and the edge-case table: "leadingone = undefined")
  Actually: find_first_set/find_last_set initialize `index = {N{1'b0}}` and simply never reassign it
            when no bit is set, so both indices are 0 for input 0 — fully deterministic. (The RTL
            header even documents "0 if all zeros".)
  Impact:   Low; a reader may add needless guarding or X-checking around a defined output.
```

```
[SUSPECTED] icg.md — power-savings percentages presented as fact with no source or conditions
  File:     docs/markdown/RTLCommon/icg.md
  Says:     "Typical power savings achievable: Clock Network: 20-40% ... Sequential Logic: 30-60% ...
            Overall Dynamic Power: 10-30% depending on gating efficiency"
  Actually: No measurement, synthesis data, citation, or conditions (process, activity factor,
            gating ratio) back these numbers, yet they appear under the heading "Power Savings
            Calculation". Unverifiable from the material provided.
  Impact:   Readers may quote library-specific numbers that have no basis in this library.
```

## POSSIBLE RTL BUGS

**1. pwm repeat-count off-by-one (likely).** As traced in the findings, `repeat_count = N` produces N+1 periods because `w_all_repeats_done = (r_repeat_value >= local_repeat)` is evaluated against the pre-increment count. Evidence this is unintended: the RTL's own header waveform ("WIDTH=8, duty=50, period=100, repeat=2") shows two periods then `done`, and both doc examples agree with the header. A minimal fix is `(r_repeat_value >= local_repeat - 1)` (the `local_repeat == 0` infinite-mode guard already exists).

**2. johnson2bin default parameters are self-inconsistent.** The RTL header says `WIDTH` "Must be $clog2(JCW) + 1", but the defaults are `JCW=10, WIDTH=4` while $clog2(10)+1 = 5. With defaults: N = $clog2(10) = 4 = WIDTH, so `{{(WIDTH-N){1'b0}}, ...}` is a zero-width replication (tool-dependent legality — SUSPECTED), and `binary[WIDTH-2:0]` truncates the 4-bit position field to 3 bits, so states with position ≥ 8 alias (e.g., first-half state 9 → w_binary = 9 = 4'b1001 → binary = {0, 001} = 1, colliding with state 1) — CONFIRMED by construction. Anyone overriding both parameters per the constraint is unaffected. Incidental: the RTL's inline comments "Second half: use leading one position directly" / "First half: use trailing one + 1" are swapped relative to the code, and localparam `PAD_WIDTH` is computed but never used.

## Overall accuracy

The bulk of this part is solid: structural descriptions, port lists, and the `hex_to_7seg`, `gray2bin`, `shifter_barrel`, `shifter_universal`, `reset_sync`, `reverse_vector`, `shifter_beat_pack`, `mod_3_compress`, and `shifter_lfsr_fibonacci` pages verified line-by-line against the RTL with no discrepancies found. The recurring defect pattern is wrong worked arithmetic: `johnson2bin` (two bad examples plus a bad special case), `shifter_lfsr`, and `shifter_lfsr_galois` all contain hand-computed examples that contradict the correct code printed on the same page — these are the highest-value fixes because readers use examples to build reference models. The three phantom `INSTANCE_NAME` parameters and the undocumented `pwm.sync_rst_n` are compile-time-visible gaps. The `pwm` repeat-count mismatch between every piece of prose (docs and RTL header alike) and the actual RTL behavior deserves an RTL-side look, not just a doc edit.