# Review: common_part_02 (9 docs, 9 RTL modules)

I checked every parameter table, port list, timing claim, code snippet, and formal property against the RTL. All 9 docs have matching modules. Findings below, roughly in severity order.

---

```
[CONFIRMED] counter_johnson doc claims the counter is self-starting; the RTL has no recovery
            logic and invalid states form a closed parasitic cycle
  File:     docs/markdown/RTLCommon/counter_johnson.md
  Says:     "**Self-Starting**: Johnson counters are self-starting from most invalid states ...
             **Recovery**: Most invalid states naturally converge to valid sequence"
            also "**Self-Starting**: Recovers from most error states",
            "**No Invalid States**: All reachable states are functional", and in the WaveDrom
            section "**Self-Starting**: Recovers from invalid states automatically"
  Actually: The RTL is a bare twisted-ring shift register:
              counter_gray <= {counter_gray[WIDTH-2:0], ~counter_gray[WIDTH-1]};
            with no state-correction logic. For WIDTH=4 the 8 invalid states form a closed
            cycle and NEVER converge to the valid sequence:
              0010→0101→1011→0110→1101→1010→0100→1001→0010
            (WIDTH=3 is the same: 010↔101 is a parasitic 2-cycle.) Zero of the 8 invalid
            states "naturally converge". The verification section even lists "Self-Starting:
            Verify recovery from invalid states" as a test scenario — that test would fail.
  Impact:   A reader who relies on automatic recovery (e.g., after a glitch or SEU in an
            async-FIFO pointer) will omit reset/correction logic and can lock permanently
            into the parasitic cycle. This is the most damaging claim in the unit.
```

```
[CONFIRMED] clock_pulse doc describes the pulse phase one cycle early; its own formal
            properties would fail against the RTL
  File:     docs/markdown/RTLCommon/clock_pulse.md
  Says:     "Pulse Generation: Pulse asserted when counter reaches WIDTH-1" and
            "Phase: Pulse occurs on last count (WIDTH-1)"; and the Formal Properties section:
              property pulse_at_max_count;
                @(posedge clk) disable iff (!rst_n) (dut.r_counter == WIDTH-1) |-> pulse;
              property pulse_only_at_max;
                @(posedge clk) disable iff (!rst_n) pulse |-> (dut.r_counter == WIDTH-1);
  Actually: The RTL registers the comparison:  pulse <= (r_counter == w_width_minus_one);
            Cycle-by-cycle trace (WIDTH=4):
              cyc: r_counter=3, pulse=0  → next: r_counter=0, pulse<=1
              cyc: r_counter=0, pulse=1  → next: r_counter=1, pulse<=0
            So pulse is HIGH during the cycle when r_counter==0, i.e., one cycle AFTER the
            counter reaches WIDTH-1. With SVA preponed sampling, pulse_at_max_count and
            pulse_only_at_max both fail every period. The "Basic Operation (WIDTH=4)" timing
            diagram also aligns the pulse with counter=< 3 > rather than < 0 >.
            (Period WIDTH and duty 1/WIDTH are correct; only the phase is wrong.)
  Impact:   Reader gets the pulse phase wrong by one cycle; anyone pasting the doc's
            assertions into a verification environment gets immediate failures on correct RTL.
```

```
[CONFIRMED] clock_pulse resource table assumes a $clog2(WIDTH) counter; the RTL counter is
            WIDTH bits wide
  File:     docs/markdown/RTLCommon/clock_pulse.md
  Says:     "Resource Utilization
             | WIDTH | Counter Bits | LUTs | FFs | Max Freq |
             | 8     | 3            | 8    | 4   | 500MHz   |
             | 16    | 4            | 12   | 5   | 450MHz   |
             | 32    | 5            | 18   | 6   | 400MHz   |
             | 1024  | 10           | 28   | 11  | 350MHz   |"
  Actually: RTL declares  logic [WIDTH-1:0] r_counter;  — the counter is WIDTH bits, not
            $clog2(WIDTH) bits. Recompute: WIDTH=8 → 8 counter FFs + 1 pulse FF = 9 FFs
            (doc: 4); WIDTH=1024 → 1025 FFs and a 1024-bit comparator (doc: 11 FFs, 28 LUTs).
            Off by ~100x at WIDTH=1024.
  Impact:   Resource estimates are wildly optimistic for any realistic period. See the RTL
            bug section — the underlying sizing is itself the real problem.
```

```
[CONFIRMED] clock_gate_ctrl documents N as an overridable parameter; in the RTL it is a
            localparam in the module body
  File:     docs/markdown/RTLCommon/clock_gate_ctrl.md
  Says:     Module declaration:
              module clock_gate_ctrl #(
                  parameter int IDLE_CNTR_WIDTH = 4,
                  parameter int N = IDLE_CNTR_WIDTH
              ) (
            and a Parameters section: "### N - Type: int - Default: IDLE_CNTR_WIDTH -
            Description: Alias for counter width (convenience parameter)"
  Actually: RTL has only one parameter:
              module clock_gate_ctrl #(
                  parameter int IDLE_CNTR_WIDTH = 4
              ) ( ... );
              localparam int N = IDLE_CNTR_WIDTH;  // in the module body
            N cannot be overridden. (Elsewhere in this book, e.g. counter_freq_invariant.md,
            the docs correctly mark derived values "do not override"; this page does the
            opposite.)
  Impact:   A reader instantiating #(.IDLE_CNTR_WIDTH(8), .N(8)) per the documented
            interface gets an elaboration error.
```

```
[CONFIRMED] clock_pulse "pipelined" optimization example changes the period to WIDTH+1
  File:     docs/markdown/RTLCommon/clock_pulse.md
  Says:     "// For high-frequency applications, pipeline the comparison
             module clock_pulse_pipelined #(parameter int WIDTH = 1000) ..."
  Actually: In the example, compare_result is registered and then used to wrap the counter:
            the counter sequences 0,1,...,WIDTH-1,WIDTH,0 → WIDTH+1 states, and pulse fires
            once per WIDTH+1 clocks. Trace: at r_counter=WIDTH-1, compare_result is still 0
            (previous count was WIDTH-2), so the counter increments to WIDTH; it wraps only
            on the next cycle when compare_result=1. The base module's documented period is
            "WIDTH clock cycles".
  Impact:   A reader swapping in this "equivalent, faster" variant silently changes the
            pulse frequency by one clock per period.
```

```
[CONFIRMED] counter_bin parameter table excludes exactly the configuration its own
            examples use
  File:     docs/markdown/RTLCommon/counter_bin.md
  Says:     MAX parameter: "Range: Should be < 2^(WIDTH-1) for proper operation"
  Actually: The RTL supports MAX = 2^(WIDTH-1): w_max_val = (WIDTH-1)'(MAX - 1) fits exactly
            (MAX-1 = 2^(WIDTH-1)-1). The RTL header documents "Range: 2 to (2^(WIDTH-1))",
            the doc's own validation snippet asserts MAX <= (2**(WIDTH-1)), and both doc
            examples use equality: counter_bin #(.WIDTH(4), .MAX(8)) and #(.WIDTH(11),
            .MAX(1024)). The companion page counter_bin_load.md correctly states MAX ≤ 8
            for WIDTH=4.
  Impact:   Minor internal contradiction; power-of-2 FIFO depths (the primary use case)
            sit exactly at MAX = 2^(WIDTH-1), which the table implies is improper.
```

```
[CONFIRMED] counter_load_clear "Load During Count" timing diagram is not reproducible from
            the RTL
  File:     docs/markdown/RTLCommon/counter_load_clear.md
  Says:     Timing diagram with Increment high throughout and r_match=3 initially:
              Count : < 0 >< 1 >< 2 >< 2 >< 3 >< 4 >< 5 >< 0 >
  Actually: In the RTL, load only writes r_match_val and never stalls the count:
              if (load) r_match_val <= loadval;
              if (clear) count <= 'b0;
              else if (increment) count <= (count == r_match_val) ? 'b0 : count + 1;
            With increment drawn high, count increments every cycle (including during load)
            and would wrap at the OLD match value 3 before the load takes effect — the drawn
            sequence (a repeated <2> during load, and no wrap at 3) cannot occur.
            (Minor ASCII-alignment caveat, but the doubled <2> plus the missing wrap point
            at "load pauses counting".)
  Impact:   Low; the doc's prose ("Load can occur simultaneously with other operations") is
            correct — only the diagram contradicts it.
```

```
[CONFIRMED] counter_load_clear assertion "count never exceeds match value" does not hold
  File:     docs/markdown/RTLCommon/counter_load_clear.md
  Says:     "// Count should never exceed match value
             property count_bounds;
                 @(posedge clk) disable iff (!rst_n) count <= r_match_val;"
  Actually: If a smaller match value is loaded while the count is above it, count >
            r_match_val: e.g. load 5, count up to 5, then load 2 → count=5 > r_match_val=2,
            done deasserts, and the counter free-runs modulo 2^width until it happens to
            equal 2 again (there is no terminal-count clamp other than equality).
  Impact:   Low-moderate; the property holds for the load-then-count usage pattern but a
            reader copying the assertion into a testbench that dynamically reduces the
            terminal count will see failures on correct RTL.
```

## POSSIBLE RTL BUGS

1. **`clock_pulse` counter sized as WIDTH bits instead of $clog2(WIDTH) (likely bug).**
   `logic [WIDTH-1:0] r_counter;` and `w_width_minus_one = WIDTH[WIDTH-1:0] - 1'b1` make the
   counter as wide as the *period*. Functionally correct, but the doc's own first example
   (`system_heartbeat`, 100 MHz clock, 1 Hz heartbeat) sets `WIDTH = 100_000_000`, which
   would infer ~100 million flip-flops — unsynthesizable. The intended declaration is
   almost certainly `logic [$clog2(WIDTH)-1:0] r_counter;` (with the constant sized to
   match). The doc's resource table appears to have been written against that intended
   implementation.

2. **`clock_gate_ctrl` uses `N` in the ANSI port list before declaring it (suspected
   LRM violation).** `input logic [N-1:0] cfg_cg_idle_count` appears in the port list, but
   `localparam int N = IDLE_CNTR_WIDTH;` is declared in the module body *after* the port
   list. Per IEEE 1800, body localparams are not visible in the port list; strict tools
   reject this. SUSPECTED — I cannot compile here, and tool tolerance for forward
   localparam references varies (or `reset_defs.svh` could conceivably define `N`, which
   would be worse). The robust fix is `[IDLE_CNTR_WIDTH-1:0]` in the port.

3. **`counter_freq_invariant` header comment LUT has off-by-one values (trivial).** The RTL
   comment example says "idx 9: 133 MHz" and "idx 12: 176 MHz"; the actual `linear_freq`
   gives 5+1935/15 = **134** and 5+2580/15 = **177** (and `DEBUG_LUT` would print 134/177).
   The documentation page has the correct values (134, 177), so this is a stale RTL comment,
   not a doc defect.

## What I checked that is correct

- `counter_freq_invariant.md`: I recomputed all 16 default LINEAR LUT entries from
  `linear_freq` (5, 19, 33, 48, 62, 76, 91, 105, 119, 134, 148, 162, 177, 191, 205, 220) —
  every table value matches; POW2 sequence (5,10,20,40,80,160,220…) matches; derived
  parameters (SEL_WIDTH=4, DIV_WIDTH=8, PRESCALER_MAX=256), the `o_counter` port name, the
  `r_clear_pulse` reset-to-1 note, and the prescaler wiring all match the RTL.
- `counter_bingray.md`: Gray table, conversion formula, registered dual outputs,
  combinational `counter_bin_next`, 2×WIDTH FF count — all match.
- `counter_bin_load.md`: priority order (load > add > enable), WRAP_BOUNDARY=2×MAX, MSB
  toggle for +1, modular-wrap arithmetic for add (verified the truncation/subtraction is
  equivalent mod 2^WIDTH for in-range sums) — all match.
- `counter_bin.md`: wrap behavior and the WIDTH=4/MAX=6 counting sequence match the RTL
  exactly.
- `counter.md`: period MAX+1, $clog2(MAX+1) width table (7→3, 15→4, 99→7, 999→10),
  combinational tick — all match.
- All doc examples that instantiate the reviewed modules use correct port names and legal
  parameter values.

## Overall

The unit is mid-quality. The counter trio (`counter_bin`, `counter_bin_load`,
`counter_bingray`), `counter`, and the rewritten `counter_freq_invariant` page are accurate
and clearly checked against the current RTL. The two clock pages are the weak spot:
`clock_pulse.md` gets the pulse phase wrong, ships formal properties that fail on the
shipped RTL, and carries a resource table written against a counter the RTL doesn't
contain; `clock_gate_ctrl.md` documents a parameter (`N`) that doesn't exist. The
`counter_johnson.md` self-starting claim is the single most dangerous statement in the
unit, since it invites readers to skip error-recovery logic the design actually needs.
Independently of the docs, the `clock_pulse` counter sizing looks like a genuine RTL bug
worth fixing before announcement — the doc's own heartbeat example is unsynthesizable
against it.