# Review: common_part_01 (10 docs, 9 modules)

I verified every port list, parameter table, code example, and numeric claim against the supplied RTL. FSM traces and rotation arithmetic were recomputed by hand. Timing/frequency estimates, "Production Ready" markers, and placeholder diagrams were skipped per the known-weak-areas list.

---

## Findings

```
[CONFIRMED] Weighted arbiter: "consecutive grants" pattern contradicted by the masking logic
  File:     docs/markdown/RTLCommon/arbiter_round_robin_weighted.md
  Says:     "**Client 0**: 4 credits → gets 4 consecutive grants ... **Pattern**: C0, C0, C0, C0, C1, C1, C2, C3, [replenish], repeat..."
  Actually: The RTL explicitly masks the currently granted client out of the request vector
            whenever multiple clients are eligible:
              assign w_mask_multi_req[j] = w_requesting_eligible[j] && !grant[j];
            (`grant` is the registered output of u_base_arbiter). So with weights [4,2,1,1]
            and all clients requesting, back-to-back grants to one client cannot occur while
            others are eligible; grants interleave (e.g. C0,C1,C0,C1,C0,C2,C0,C3). The
            aggregate 4:2:1:1 proportions still hold, so the bandwidth percentages are fine.
            Note the RTL's own header comment repeats the same incorrect pattern, but the
            logic is ground truth. This is also an internal contradiction: the doc's
            "Request Masking for Fairness" section shows the very code that forbids the
            pattern its prose describes.
  Impact:   A reader expects bursty, consecutive grant behavior (matters for latency-sensitive
            clients, burst-oriented buses); actual behavior is interleaved.
```

```
[CONFIRMED] bin_to_bcd latency formula/table off by ~2x; check states not counted
  File:     docs/markdown/RTLCommon/bin_to_bcd.md
  Says:     "**Formula**: `Latency = WIDTH + (WIDTH-1) × DIGITS` clock cycles" and
            "State transitions: CK_S_IDX and CK_D_IDX states (included in above counts)";
            table: 8-bit/3-digit = "8 + 7×3 = 29" cycles (290 ns @100 MHz)
  Actually: Tracing the FSM in rtl/common/bin_to_bcd.sv: each non-final bit iteration visits
            SHIFT + CK_S_IDX + DIGITS×(ADD + CK_D_IDX) = 2 + 2·DIGITS cycles; the final
            iteration adds SHIFT + CK_S_IDX + BCD_DONE = 3. Actual latency is
            (WIDTH-1)·(2·DIGITS+2) + 3 = 59 cycles for WIDTH=8/DIGITS=3 (vs documented 29),
            and 21 cycles for WIDTH=4/DIGITS=2 (vs documented 10). The check states are NOT
            included in the formula, directly contradicting the parenthetical claim. The
            "Example 2" cycle table has the same defect: it shows SHIFT→ADD with no CK_S_IDX
            or CK_D_IDX states and only one ADD per shift (the FSM performs DIGITS=2 ADDs
            per shift), so the 9-cycle trace shown would really take ~21 cycles. The final
            BCD results in the examples are still correct.
  Impact:   Conversion-time budgets and any downstream logic sized off the documented latency
            are wrong by roughly a factor of two.
```

```
[CONFIRMED] cam_tag free-slot search direction documented backwards
  File:     docs/markdown/RTLCommon/cam_tag.md
  Says:     "- Searches from highest to lowest index / - Returns the highest-indexed free
            location" and under Allocation Strategy: "**First Available**: Uses
            highest-indexed free location"
  Actually: The RTL loop is
              w_next_valid_loc = -1;
              for (int i=DEPTH-1; i >= 0; i--)
                  if (r_valid[i] == 1'b0) w_next_valid_loc = i;
            It iterates high→low but overwrites on every free slot, so the surviving value
            is the LOWEST-indexed free location (e.g. slots {2,5} free → 2, not 5).
  Impact:   Readers tracking allocation order (debug, occupancy analysis) get the wrong
            direction. Functional behavior is otherwise as documented.
```

```
[CONFIRMED] Round-robin fairness description states the rotation direction backwards
  File:     docs/markdown/RTLCommon/arbiter_round_robin.md
  Says:     "2. After serving a client, giving priority to all lower-indexed clients
            3. When no lower-indexed clients are requesting, wrapping around to serve from
            the top"
  Actually: The mask is  w_win_mask_decode[i] = ~((CLIENTS'(1) << (i + 1)) - CLIENTS'(1)),
            which sets bits i+1..CLIENTS-1: after client i wins, priority goes to
            HIGHER-indexed clients (i+1 first). Wrap-around falls back to the unmasked
            vector, so the lowest-indexed requester wins — it wraps to client 0 (the bottom),
            not "the top".
  Impact:   Reader predicts grant order incorrectly when debugging arbitration.
```

```
[CONFIRMED] arbiter_round_robin_simple example table contradicts the RTL's restore rotation
  File:     docs/markdown/RTLCommon/arbiter_round_robin_simple.md
  Says:     "| 1 | 0 | 1110 | 1101 | 0001 | 0010 | 1 |"  (cycle 1: grant 0010, id 1)
            "| 3 | 2 | 1011 | 1101 | 0001 | 1000 | 3 |"  (cycle 3: grant 1000, id 3)
  Actually: The table's "Rotated" and "Selected" columns DO match the RTL, but the restore
            step  w_nxt_grant = (w_rot_sel >> s) | (w_rot_sel << (N - s))  gives:
            cycle 1 (s=1): (0001>>1)|(0001<<3) = 1000 (agent 3), not 0010;
            cycle 3 (s=3): (0001>>3)|(0001<<1) = 0010 (agent 1), not 1000.
            The table shows intended ascending round-robin; the RTL computes a mirror order.
            See POSSIBLE RTL BUGS — the RTL is what is wrong here.
  Impact:   The documented example does not describe the hardware as built.
```

```
[CONFIRMED] clock_divider baud-rate example is arithmetically wrong and mislabeled
  File:     docs/markdown/RTLCommon/clock_divider.md
  Says:     "// Closest: 2^13 = 8192 → 100MHz/8192 = 12.2kHz (≈9600 baud)" and the instance
            output is named ".divided_clk (uart_baud_x16)  // 16× oversampling clock"
  Actually: 100 MHz / 8192 = 12,207 Hz. That is 27% above 9600 (UART tolerance is ~2-3%),
            so "(≈9600 baud)" is false; and a 16× oversampling clock for 9600 baud must be
            153,600 Hz, which 12.2 kHz misses by 12.6x. Calling it "uart_baud_x16" is wrong
            under either interpretation. (The doc's advice to use counter_load_clear for
            precise baud rates is correct; the example numbers are not.)
  Impact:   A reader copying the example builds a non-functional UART clock.
```

```
[CONFIRMED] Overview "Integration Best Practices" example would not compile — adder instantiation has no module name
  File:     docs/markdown/RTLCommon/overview.md
  Says:     "    // High-speed addition using parallel prefix
                    .N(DATA_WIDTH)
                ) u_adder ( ..."
  Actually: The instantiation is missing both the module identifier and the `#(` — it begins
            mid-parameter-list. No module in any book could elaborate this.
  Impact:   The library's headline integration example is broken; a reader must guess the
            intended adder module.
```

```
[CONFIRMED] Weighted arbiter credit reset value misdocumented
  File:     docs/markdown/RTLCommon/arbiter_round_robin_weighted.md
  Says:     "1. **Credit Initialization**: Each client's credit counter is initialized to its
            weight value"
  Actually: RTL: `r_credit_counter[i] <= MTW'(1);  // Start with 1 credit (will be corrected
            on first replenish)`. All counters reset to 1 regardless of weight; weights are
            only loaded on global replenish or WEIGHT_STABILIZE. The first arbitration round
            after reset therefore gives every requesting client exactly one grant.
  Impact:   Minor; behavioral nuance immediately out of reset.
```

```
[CONFIRMED] arbiter_round_robin_simple reset behavior misdescribed
  File:     docs/markdown/RTLCommon/arbiter_round_robin_simple.md
  Says:     "Active Reset: All state registers cleared, grant outputs become invalid"
  Actually: The only state register is set to N-1, not cleared
            (`r_last_grant <= (W)'(N-1);`), and the grant outputs are purely combinational
            (`assign grant = w_nxt_grant; assign grant_valid = |w_nxt_grant;`) with no reset
            gating — they track `request` even while reset is asserted.
  Impact:   Minor; wrong expectation of output behavior during reset.
```

```
[CONFIRMED] Round-robin mask LUT descriptions off by one (and one table is unused)
  File:     docs/markdown/RTLCommon/arbiter_round_robin.md
  Says:     "`w_mask_decode[i]`: Mask for clients 0 through i (give priority after i)"
            "`w_win_mask_decode[i]`: Mask to give priority to clients above i+1"
  Actually: w_mask_decode[i] = (1<<i)-1 covers clients 0..i-1, not 0..i; and it is never
            referenced anywhere else in the module (dead generate code). w_win_mask_decode[i]
            = ~((1<<(i+1))-1) covers clients i+1 and above — priority above i, not above i+1.
  Impact:   Trivial, but the doc presents an unused structure as part of the mechanism.
```

```
[CONFIRMED] arbiter_round_robin_simple module declaration omits the W parameter
  File:     docs/markdown/RTLCommon/arbiter_round_robin_simple.md
  Says:     "module arbiter_round_robin_simple #( parameter int unsigned N = 4 ) ( ..."
            and the Parameters table lists only N.
  Actually: RTL declares two parameters:
            `parameter int unsigned N = 4, parameter int unsigned W = $clog2(N)`
            and types grant_id as [W-1:0].
  Impact:   Trivial; the declaration block and parameter table are not faithful.
```

```
[SUSPECTED] Weighted arbiter latency claim
  File:     docs/markdown/RTLCommon/arbiter_round_robin_weighted.md
  Says:     "Latency: 2 cycles (credit calculation + round-robin arbitration)"
  Actually: The request→grant path contains exactly one register stage: eligibility/masking
            is combinational into u_base_arbiter, whose grant/grant_valid are the registered
            outputs. That is 1-cycle latency by the usual definition. (The RTL header comment
            also says 2, but the logic shows a single registered stage; I could not construct
            a 2-cycle path in either ACK mode.)
  Impact:   Minor; pipeline planning off by one cycle.
```

```
[SUSPECTED] Overview module-count hierarchy appears to undercount arbitration modules
  File:     docs/markdown/RTLCommon/overview.md
  Says:     "├── Control & Arbitration (4 modules) │   ├── Round-Robin Arbiters │   └──
            Priority Arbiters"
  Actually: This review unit alone contains five arbiter_* modules in rtl/common
            (priority_encoder, round_robin, round_robin_simple, round_robin_weighted,
            single_client). I cannot see the full library tree, so the "4" may reflect a
            different categorization, but five arbitration modules demonstrably exist.
  Impact:   Minor; catalog inaccuracy.
```

```
[SUSPECTED] Unsourced quantitative power claim in overview
  File:     docs/markdown/RTLCommon/overview.md
  Says:     "Up to 40% dynamic power reduction with clock gating"
  Actually: No measurement, source, or conditions given anywhere in the material.
  Impact:   A specific number presented as fact with nothing behind it.
```

---

## POSSIBLE RTL BUGS

**arbiter_round_robin_simple rotates in the wrong direction — mirror-order grants, starvation of intermediate agents.**

The intent (per the module header and the doc's example table) is ascending round-robin: after granting agent g, priority should start at agent g+1. The RTL does:

```
w_shift_amount = (r_last_grant == N-1) ? 0 : r_last_grant + 1;   // s = g+1
w_rot_req   = (request << s) | (request >> (N - s));             // rotate LEFT: rot[j] = req[(j-s) mod N]
w_rot_sel   = w_rot_req & (~w_rot_req + 1);                      // lowest set bit
w_nxt_grant = (w_rot_sel >> s) | (w_rot_sel << (N - s));         // restore
```

Rotate-left by s places agent (N−s) at priority position 0, so with all agents requesting the winner after grant g is agent (N−1−g) — a reflection, not a rotation. Symbolic trace, N=4, request=4'b1111 held:

- reset: r_last_grant=3 → s=0 → grant agent 0
- g=0 → s=1 → rot=1111 → sel=0001 → grant=(0001>>1)|(0001<<3)=1000 → agent 3
- g=3 → s=0 → agent 0 …

Grants alternate 0,3,0,3 forever; agents 1 and 2 starve despite requesting continuously. The correct construction is rotate-right by g+1 (or rotate-left by N−1−g). Supporting evidence that the RTL (not the doc) is at fault: the doc's example table reproduces the RTL's intermediate "Rotated"/"Selected" values exactly, but its "Grant" column follows proper ascending round-robin — i.e., the table documents the intended algorithm the RTL fails to implement. This also invalidates the doc's fairness claims ("Ensures all requesting agents get equal opportunity over time"). Confidence: high (hand symbolic simulation of the exact expressions, including the `(W)'(N)` casts, which I verified collapse correctly mod 2^W and are not a separate bug). Not run on a simulator.

Minor RTL note (not a functional bug): `w_mask_decode` in `arbiter_round_robin.sv` is generated but never used.

---

## Overall assessment

Port lists, parameters, state-machine structures, and the detailed prose for `arbiter_single_client`, `bin2gray`, `arbiter_priority_encoder`, and most of `clock_divider` are accurate and match the RTL closely — the module-level docs are generally reliable at the interface level. The defects cluster in *behavioral* claims: the weighted arbiter's "consecutive grants" pattern, a 2x error in the bin_to_bcd latency model, the cam_tag allocation direction, the round-robin rotation direction described backwards, and a broken flagship code example in the overview. Most significant is the likely RTL bug in `arbiter_round_robin_simple` (mirror-order granting with starvation), which the doc's example table inadvertently exposes — that module should be re-verified before release, since its documentation currently describes the correct intended behavior rather than the implemented one.