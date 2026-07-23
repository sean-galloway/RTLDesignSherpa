# Review: common_part_01 (RTL Common Library, part 1 of 5)

I checked all 10 documents against the 9 RTL modules provided. The most significant result is a functional RTL bug in `arbiter_round_robin_simple` that the documentation's own example table contradicts. Several numeric and behavioral errors were confirmed by recomputation.

---

## Findings

```
[CONFIRMED] RTL rotates the wrong direction: arbiter_round_robin_simple does not
            implement round-robin and starves agents
  File:     docs/markdown/RTLCommon/arbiter_round_robin_simple.md (doc table),
            rtl/common/arbiter_round_robin_simple.sv (RTL)
  Says:     Arbitration Sequence Example, cycle 1: "Last Grant 0 | Requests 1110 |
            Rotated 1101 | Selected 0001 | Grant 0010 | Grant ID 1" — i.e., grants
            rotate 0 → 1 → 2 → 3.
  Actually: The RTL rotates the request LEFT by (last_grant+1), isolates the lowest
            set bit, then rotates the result RIGHT back:
              w_rot_req  = (request << w_shift_amount) | (request >> (N - w_shift_amount));
              w_nxt_grant= (w_rot_sel >> w_shift_amount) | (w_rot_sel << (N - w_shift_amount));
            Recomputing doc cycle 1 (last=0, shift=1, request=1110):
              rot = 1101, sel = 0001, grant = (0001>>1)|(0001<<3) = 1000 → agent 3,
            not agent 1. Rotating left by L+1 puts agent (N−L−1) at priority, not
            agent L+1. Simulating the RTL with all agents requesting (N=4):
              L=3→shift 0→grant 0;  L=0→shift 1→rot=1111→grant 3;  L=3→grant 0; ...
            Grants alternate 0,3,0,3 forever — agents 1 and 2 are NEVER served.
            Doc cycle 3 (last=2, requests=1011) is likewise wrong: RTL gives
            grant 0010 (agent 1), doc says 1000 (agent 3). Note the doc's own
            "Selected" column (0001) cannot produce its "Grant" column for cycles
            1 and 3, so the table is internally inconsistent too.
  Impact:   Readers believe the module provides fair round-robin ("Fair Arbitration:
            Ensures all requesting agents get equal opportunity over time"). The RTL
            starves agents under the most common use case. See POSSIBLE RTL BUGS.
```

```
[CONFIRMED] bin_to_bcd conversion-latency formula and table are ~2x too low
  File:     docs/markdown/RTLCommon/bin_to_bcd.md
  Says:     "Formula: Latency = WIDTH + (WIDTH-1) × DIGITS clock cycles" and
            "8 | 3 | 8 + 7×3 = 29 | 290ns @100MHz"; also "State transitions:
            CK_S_IDX and CK_D_IDX states (included in above counts)".
  Actually: The FSM spends 1 cycle each in SHIFT and CK_S_IDX per input bit, and
            2 cycles (ADD + CK_D_IDX) per digit per bit. Tracing the states:
            total = 4 + (WIDTH−1)×(2 + 2×DIGITS) cycles. For WIDTH=8, DIGITS=3:
            4 + 7×8 = 60 cycles (~600 ns @100 MHz), not 29. CK_S_IDX and CK_D_IDX
            are NOT "included in above counts" — the doc's formula omits them
            entirely. Every table row inherits the error (e.g., 16/5: actual ≈183,
            doc says 91; 4/2: actual ≈22, doc says 10).
  Impact:   A reader budgeting display-update or UART/LCD timing underestimates
            conversion time by 2x.
```

```
[CONFIRMED] bin_to_bcd worked example 1 arrives at the wrong answer and skips a
            mandatory add-3
  File:     docs/markdown/RTLCommon/bin_to_bcd.md
  Says:     "Iteration 7: ... ADD phase: Tens = 9, Ones = 4 - none ≥ 5" and
            "Final Result: BCD = 000100101000 = 4'h1, 4'h5, 4'h6 = 156 decimal ✓"
  Actually: 000100101000 split into nibbles is (1, 2, 8) = decimal 128, not
            (1,5,6) = 156 — the hex value contradicts the doc's own digit claim.
            The root cause is visible in the trace: at Iteration 7 the tens digit
            is 9, which is ≥ 5, so the Double-Dabble algorithm REQUIRES add-3;
            the trace says "none ≥ 5" and shifts anyway, producing the wrong
            result. (I re-ran the algorithm by hand: correct sequence ends
            (0,10,11) → add-3 → shift → 0001_0101_0110 = 156.)
  Impact:   The only end-to-end worked example teaches an incorrect trace and an
            incorrect final value.
```

```
[CONFIRMED] bin_to_bcd worked example 2 omits half the FSM states
  File:     docs/markdown/RTLCommon/bin_to_bcd.md
  Says:     Example 2 cycle table: "0 IDLE, 1 SHIFT, 2 ADD, 3 SHIFT, 4 ADD,
            5 SHIFT, 6 ADD, 7 SHIFT, 8 DONE" for WIDTH=4, DIGITS=2.
  Actually: The FSM sequence is SHIFT → CK_S_IDX → (ADD → CK_D_IDX) × DIGITS per
            bit, so a 4-bit/2-digit conversion takes ~22 cycles and must pass
            through 2 ADD states per shift. The example shows 8 cycles, one ADD
            per shift, and no CK_* states — contradicting the doc's own FSM
            section and state diagram.
  Impact:   Reinforces the incorrect latency story; confusing for anyone
            wave-debugging against the real FSM.
```

```
[CONFIRMED] arbiter_round_robin fairness description has the rotation direction
            backwards
  File:     docs/markdown/RTLCommon/arbiter_round_robin.md
  Says:     "2. After serving a client, giving priority to all lower-indexed
            clients; 3. When no lower-indexed clients are requesting, wrapping
            around to serve from the top"
  Actually: The mask is w_win_mask_decode[i] = ~((1 << (i+1)) − 1), which selects
            clients i+1 .. CLIENTS−1 (HIGHER indices), and masked requests are
            checked first; wrap-around goes to client 0 (the bottom). The RTL
            header itself states "Rotation order: 0 → 1 → 2 → ... → (CLIENTS-1)
            → 0". After serving client i, priority goes to higher-indexed clients,
            wrapping to the lowest indices.
  Impact:   A reader predicting grant order gets the sequence reversed.
```

```
[CONFIRMED] arbiter_round_robin mask-LUT descriptions are off by one (and one LUT
            is dead logic)
  File:     docs/markdown/RTLCommon/arbiter_round_robin.md
  Says:     "w_mask_decode[i]: Mask for clients 0 through i (give priority after
            i)" and "w_win_mask_decode[i]: Mask to give priority to clients
            above i+1"
  Actually: w_mask_decode[i] = (1<<i)−1 covers clients 0..i−1, not 0..i.
            w_win_mask_decode[i] = ~((1<<(i+1))−1) selects clients ≥ i+1 ("above
            i"), not "above i+1". Additionally, w_mask_decode is generated but
            never read anywhere in the RTL — only w_win_mask_decode feeds
            w_curr_mask_decode — so the documented "pre-computed mask lookup"
            mechanism is half dead logic.
  Impact:   Minor; misleads anyone mapping the description to waveforms.
```

```
[CONFIRMED] Weighted arbiter "consecutive grants" pattern is not what the RTL does
  File:     docs/markdown/RTLCommon/arbiter_round_robin_weighted.md
  Says:     "Client 0: 4 credits → gets 4 consecutive grants" and
            "Pattern: C0, C0, C0, C0, C1, C1, C2, C3, [replenish], repeat..."
  Actually: The request mask excludes the previously granted client whenever
            multiple clients are eligible (w_mask_multi_req[j] =
            w_requesting_eligible[j] && !grant[j], applied unconditionally).
            Simulating weights [4,2,1,1] with all clients requesting gives an
            interleaved sequence: C0, C1, C2, C3, C0, C1, C0, (bubble), C0, then
            replenish — never 4 consecutive C0 grants while others are eligible.
            The per-round bandwidth (4:2:1:1 = 50/25/12.5/12.5 %) does hold.
  Impact:   A reader expecting bursty per-client grants (e.g., for burst-friendly
            bus behavior) gets round-robin interleaving instead.
```

```
[CONFIRMED] Weighted arbiter masking code in the doc does not match the RTL (and
            as written would deadlock a lone client)
  File:     docs/markdown/RTLCommon/arbiter_round_robin_weighted.md
  Says:     "assign w_mask_req[i] = (multiple_eligible) ?
                      (w_requesting_eligible[i] && !grant[i]) :
                      (w_requesting_eligible[i] && r_credit_counter[i] > 1);"
  Actually: The RTL is w_mask_req[j] = w_mask_multi_req[j] || w_mask_last_client[j],
            i.e., (eligible && !grant[j]) || (!multiple && eligible && credit>1).
            The doc's single-eligible branch drops the "&& !grant[i]" alternative;
            taken literally, a lone eligible client on its last credit would get
            mask=0 forever (no grant, no decrement, no replenish). The RTL grants
            it every other cycle.
  Impact:   The documented algorithm, if re-implemented from the doc, deadlocks.
```

```
[CONFIRMED] MAX_LEVELS documented as the maximum weight value, but it is not
            representable
  File:     docs/markdown/RTLCommon/arbiter_round_robin_weighted.md
  Says:     "MAX_LEVELS | int | 16 | Maximum weight value per client (range: 1-256)"
  Actually: Weight fields and credit counters are MAX_LEVELS_WIDTH =
            $clog2(MAX_LEVELS) bits (4 bits for the default 16), so the largest
            usable weight is MAX_LEVELS−1 = 15. Writing weight = 16 into the
            4-bit field of max_thresh truncates to 0, which DISABLES the client
            (w_valid_clients[j] = client_weight[j] > 0).
  Impact:   A user who sets a weight equal to MAX_LEVELS silently disables that
            client. The doc should state the usable range is 0..MAX_LEVELS−1.
```

```
[CONFIRMED] cam_tag allocates the lowest free slot, not the highest
  File:     docs/markdown/RTLCommon/cam_tag.md
  Says:     "Returns the highest-indexed free location" and "Allocation Strategy:
            First Available: Uses highest-indexed free location"
  Actually: The search loop runs i = DEPTH-1 downto 0 and assigns
            w_next_valid_loc = i on every free slot; the last assignment wins, so
            the result is the LOWEST-indexed free location (e.g., all-free →
            slot 0).
  Impact:   Readers tracking allocation order (e.g., for debug or for matching
            tags to waveforms) get the indexing backwards. Functional behavior is
            otherwise correct either way.
```

```
[CONFIRMED] cam_tag "Debug Support" section documents logic that does not exist
  File:     docs/markdown/RTLCommon/cam_tag.md
  Says:     "The module includes simulation-only logic for waveform viewing:
            // synopsys translate_off
            logic [(N*DEPTH)-1:0] flat_r_tag_array; ..."
  Actually: The RTL contains no flat_r_tag_array signal and no translate_off
            region; the module ends after the tag/valid always_ff and the three
            status assigns.
  Impact:   A documented (if minor) feature that isn't there; suggests the doc was
            written against a different revision.
```

```
[CONFIRMED] clock_divider parameter-relationship constraint contradicts the RTL
            check and the doc's own parameter section
  File:     docs/markdown/RTLCommon/clock_divider.md
  Says:     "Parameter Relationships — Addressing Constraint: PO_WIDTH ≥
            $clog2(COUNTER_WIDTH)"
  Actually: The RTL elaboration check is "if (PO_WIDTH <= $clog2(COUNTER_WIDTH))
            $fatal", i.e., PO_WIDTH must be strictly greater (≥ $clog2(CW)+1).
            The doc's own PO_WIDTH section says so correctly ("Must be >
            $clog2(COUNTER_WIDTH) ... CW=16 needs PO≥5"). The relationships line
            would permit PO_WIDTH=4 for COUNTER_WIDTH=16, which the RTL rejects
            at elaboration.
  Impact:   A reader following the summary line picks an illegal parameter
            combination.
```

```
[CONFIRMED] overview code example is broken (missing module name) and would not
            compile
  File:     docs/markdown/RTLCommon/overview.md
  Says:     "// High-speed addition using parallel prefix
                 .N(DATA_WIDTH)
             ) u_adder (
                 .a(operand_a), .b(operand_b), .cin(1'b0), ..."
  Actually: The instantiation has no module identifier or "#(" — the adder module
            name was dropped. As printed, the example cannot compile.
  Impact:   The library's flagship "Integration Best Practices" example is
            unusable as written.
```

```
[CONFIRMED] Unsourced quantitative power claim in the overview
  File:     docs/markdown/RTLCommon/overview.md
  Says:     "Up to 40% dynamic power reduction with clock gating"
  Actually: No measurement, citation, or synthesis data is provided anywhere in
            the supplied material to support this figure; it is presented as
            fact. (Same page also asserts "Synthesis Proven: Validated across
            multiple technology nodes and vendors" with no evidence.)
  Impact:   Readers may quote a fabricated-sounding number in design reviews.
```

```
[SUSPECTED] 9600-baud clock_divider example is ~27 % off and unusable for a real
            UART
  File:     docs/markdown/RTLCommon/clock_divider.md
  Says:     "Closest: 2^13 = 8192 → 100MHz/8192 = 12.2kHz (≈9600 baud)" used for
            "uart_baud_x16  // 16× oversampling clock"
  Actually: The arithmetic is consistent (2^13 = 8192, 100 MHz/8192 = 12.2 kHz),
            but 12.2 kHz vs 9.6 kHz is a 27 % baud error — far beyond the ~2–3 %
            a UART can tolerate, and 12.2 kHz is not a 16× oversampling clock for
            9600 baud either. The doc does caveat "Approximate" and points to
            counter_load_clear, but the parenthetical "(≈9600 baud)" makes the
            example look usable.
  Impact:   Low; misleading example rather than a spec error.
```

```
[SUSPECTED] Weighted-arbiter ACK example relies on implicit port-width truncation
  File:     docs/markdown/RTLCommon/arbiter_round_robin_weighted.md
  Says:     ".MAX_LEVELS(8), ... .max_thresh ({4'd3, 4'd5}),  // Weights [5, 3]"
  Actually: With MAX_LEVELS=8, MAX_LEVELS_WIDTH = $clog2(8) = 3, so max_thresh is
            CXMTW = 2×3 = 6 bits; the literal {4'd3, 4'd5} is 8 bits. It happens
            to truncate to the intended values (6'b11_0101 → weights 3 and 5), but
            the example depends on implicit truncation and will draw width
            warnings. (The main example with MAX_LEVELS=16/4-bit fields is
            correct.)
  Impact:   Low; compiles with warnings, but models a sloppy pattern.
```

---

## POSSIBLE RTL BUGS

**`arbiter_round_robin_simple` — rotation direction is wrong; module starves agents (high confidence).**
The module intends: rotate the request so the agent after `r_last_grant` lands at bit 0, isolate the lowest set bit, rotate back. To do that the request must be rotated **right** by `last_grant+1` (or left by `N−last_grant−1`). The RTL rotates **left** by `last_grant+1` and restores right, which places agent `(N−last_grant−1) mod N` at the priority position. Verified by hand-simulation of the exact RTL expressions, N=4, all agents requesting:

- `r_last_grant=3` (reset) → shift=0 → grant agent **0**
- `r_last_grant=0` → shift=1 → `rot = (1111<<1)|(1111>>3) = 1111` → `sel=0001` → `grant = (0001>>1)|(0001<<3) = 1000` → agent **3**
- alternates 0, 3, 0, 3 … — agents 1 and 2 never granted → **starvation**, violating the module's stated purpose ("Ensures all requesting agents get equal opportunity over time").

The rotation only comes out right when `2·(L+1) ≡ 0 (mod N)`, which is why some sequences (e.g., the doc's cycle 2) look correct. Fix: swap the shift directions (`>>`/`<<`) in the two rotate operations, or rotate left by `(N − w_shift_amount)`.

Secondary, non-blocking RTL observations (not doc defects): `w_mask_decode` in `arbiter_round_robin` is generated but never used; `w_last_credit` in `arbiter_round_robin_weighted` is computed but never used.

---

## Overall assessment

The module-reference material in this part is largely solid: the `arbiter_priority_encoder`, `arbiter_single_client`, `bin2gray`, and most of the `clock_divider` pages match their RTL closely, including parameters, ports, and encoding tables (I spot-verified the Gray-code tables and the full division-ratio table — all correct). The defects cluster in worked examples and behavioral prose: the `bin_to_bcd` page has a 2× latency error and a wrong worked example; the `arbiter_round_robin` page describes rotation backwards; the weighted-arbiter page promises consecutive-grant bursts the masking logic prevents; and the `cam_tag` page gets the allocation direction wrong and documents debug logic that isn't in the source. Most seriously, the `arbiter_round_robin_simple` example table describes correct round-robin behavior that the RTL does not implement — the RTL itself appears buggy and starves agents, which the author should treat as the highest-priority item in this batch.