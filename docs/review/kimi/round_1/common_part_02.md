# Review: `common` (part 2 of 5) — 9 pages

I checked every page against the RTL in `RTL.sv`, recomputing counter sequences, register widths, and tick/gating behavior from the actual always blocks.

---

## Findings

### 1. `counter_freq_invariant.md` documents an obsolete implementation

This is the most damaging defect in the unit: the entire page describes a module that no longer exists. The RTL header itself notes "Updated: 2026-04-09 -- parametric LUT replaces hardcoded frequency table"; the doc still describes the hardcoded table.

```
[CONFIRMED] counter_freq_invariant: wrong parameters, wrong port name, wrong frequency table, wrong tick logic
  File:     docs/markdown/RTLCommon/counter_freq_invariant.md
  Says:     "parameter int COUNTER_WIDTH = 5,      // Width of the output counter
             parameter int PRESCALER_MAX = 65536   // Maximum value of the pre-scaler"
            and port "output logic [COUNTER_WIDTH-1:0]    counter,"
            and frequency table "| 4'b0000 | 1 | 1000MHz (1GHz) | 1ns | ..." through
            "| 4'b1111 | 10000 | 100kHz | 10μs | ..."
  Actually: RTL declares six user parameters the doc never mentions
            (COUNTER_WIDTH=16, MIN_FREQ_MHZ=5, MAX_FREQ_MHZ=220, NUM_FREQ_ENTRIES=16,
            FREQ_STRATEGY=0, DEBUG_LUT=0) plus derived SEL_WIDTH, DIV_WIDTH, and
            PRESCALER_MAX = 2**DIV_WIDTH (=256 with defaults, not 65536, and marked
            "do not override"). The output port is named `o_counter`, not `counter`.
            The division factors are not the documented 1/10/20/.../10000 table; they
            are elaborated from the MHz range (default LINEAR 5→220 MHz in 16 steps:
            idx0=5, idx1=19, ... idx15=220, via linear_freq()/pow2_freq()).
  Impact:   A reader instantiating per the doc gets the wrong module entirely. The
            documented freq_sel→frequency mapping is wrong in every row; the module's
            actual purpose (parametric 1 MHz microsecond tick from an arbitrary clock)
            is not what the page describes.
```

```
[CONFIRMED] counter_freq_invariant: all code examples use a nonexistent port `.counter` — would not compile
  File:     docs/markdown/RTLCommon/counter_freq_invariant.md
  Says:     "counter_freq_invariant #(...) tick_1mhz ( ... .counter(timer_count), .tick(tick_1mhz) );"
            (same in the baud-rate and multi-rate examples: ".counter(), // Unused")
  Actually: RTL port list is "output logic [COUNTER_WIDTH-1:0]  o_counter". There is no
            `counter` port. Every instantiation example on the page fails elaboration.
  Impact:   Copy-paste examples do not compile.
```

```
[CONFIRMED] counter_freq_invariant: documented tick logic contradicts the RTL (and the page contradicts itself)
  File:     docs/markdown/RTLCommon/counter_freq_invariant.md
  Says:     "Tick Generation: One cycle when counter is all 1's and prescaler completes"
            with code "if (w_prescaler_done && &counter) tick <= 'b1;"
            — but the same page's port table says tick is a "Pulse every time counter
            increments" and its Timing Analysis says "Tick Period: division_factor
            input clock cycles".
  Actually: RTL pulses tick on EVERY prescaler completion:
            "end else if (w_prescaler_done && sync_reset_n) begin
                 o_counter <= o_counter + 1'b1;  tick <= 1'b1;"
            Tick is a 1-cycle pulse every microsecond (every division_factor clocks),
            not only at counter rollover. The code snippet and the "all 1's" sentence
            are stale; the port table/Timing Analysis rows happen to match the new RTL,
            so the page is also internally contradictory.
  Impact:   A reader building a watchdog or periodic strobe off the documented
            "tick at rollover" behavior gets a tick 2^COUNTER_WIDTH times more often
            than they expect.
```

---

### 2. `clock_gate_ctrl.md` — `N` documented as a parameter; it is a localparam

```
[CONFIRMED] clock_gate_ctrl: parameter `N` does not exist as a parameter
  File:     docs/markdown/RTLCommon/clock_gate_ctrl.md
  Says:     Module declaration shows "parameter int IDLE_CNTR_WIDTH = 4,
            parameter int N = IDLE_CNTR_WIDTH" and a parameter table entry
            "### N - Type: int - Default: IDLE_CNTR_WIDTH - Description: Alias for
            counter width (convenience parameter)".
  Actually: RTL declares only one parameter:
            "module clock_gate_ctrl #( parameter int IDLE_CNTR_WIDTH = 4 )"
            and inside the body: "localparam int N = IDLE_CNTR_WIDTH;  // Alias for
            backwards compatibility". The RTL header explicitly calls N a "Derived
            Parameter (localparam - computed automatically)".
  Impact:   `clock_gate_ctrl #(.IDLE_CNTR_WIDTH(6), .N(6))` fails with "no such
            parameter". Anyone trusting the documented declaration mischaracterizes
            the module's interface.
```

---

### 3. `counter_johnson.md` — "self-starting" claim is false for this RTL

```
[CONFIRMED] counter_johnson: claims of self-starting / recovery from invalid states are wrong
  File:     docs/markdown/RTLCommon/counter_johnson.md
  Says:     "Self-Starting: Johnson counters are self-starting from most invalid states
            ... Recovery: Most invalid states naturally converge to valid sequence";
            Advantages: "Self-Starting: Recovers from most error states",
            "No Invalid States: All reachable states are functional"; waveform section:
            "Self-Starting: Recovers from invalid states automatically".
  Actually: The RTL is a bare twisted-ring shift register with no correction logic:
            "counter_gray <= {counter_gray[WIDTH-2:0], ~counter_gray[WIDTH-1]};".
            Tracing the RTL from an invalid state (WIDTH=4, start 4'b0010):
            0010→0101→1011→0110→1101→1010→0100→1001→0010 — all 8 invalid states form
            a disjoint parasitic ring that NEVER enters the valid 8-state sequence.
            (WIDTH=3: 010↔101 oscillates forever.) No invalid state converges; the
            claim is exactly backwards. Only the asynchronous reset to all-zeros
            guarantees entry into the valid ring.
  Impact:   A reader relying on automatic recovery (e.g., for the fifo_async
            USE_JOHNSON=1 CDC path the page cross-references) has no protection after
            a glitch or upset; the "verify recovery from invalid states" test the page
            suggests would fail.
```

---

### 4. `clock_pulse.md` — resource table is wrong by up to ~100×

```
[CONFIRMED] clock_pulse: Counter Bits / FF columns contradict the RTL's register declaration
  File:     docs/markdown/RTLCommon/clock_pulse.md
  Says:     "| WIDTH | Counter Bits | LUTs | FFs | Max Freq |
             | 8     | 3            | 8    | 4   | 500MHz |
             | 1024  | 10           | 28   | 11  | 350MHz |"
  Actually: RTL declares "logic [WIDTH-1:0] r_counter;" — the counter register is
            WIDTH bits, not ceil(log2(WIDTH)) bits, plus 1 FF for the registered
            pulse. Recomputed FFs: WIDTH=8 → 9, WIDTH=16 → 17, WIDTH=32 → 33,
            WIDTH=1024 → 1025 (doc says 4/5/6/11). LUT/comparator logic also scales
            with WIDTH, not log2(WIDTH).
  Impact:   Resource estimates are off by up to two orders of magnitude. Worse, the
            page's own application examples instantiate huge WIDTHs as if they were
            cheap — e.g. the heartbeat example uses WIDTH = 100_000_000 (1 Hz from
            100 MHz), which under this RTL allocates a 100-million-bit counter
            register. The examples compile but are physically unrealizable as written.
```

---

### 5. `clock_pulse.md` — pulse phase is off by one cycle; the formal properties would fail

```
[CONFIRMED] clock_pulse: "pulse occurs on last count" and two SVA properties contradict the registered pulse
  File:     docs/markdown/RTLCommon/clock_pulse.md
  Says:     "Phase: Pulse occurs on last count (WIDTH-1)"; and in Formal Properties:
            "property pulse_at_max_count; @(posedge clk) ... (dut.r_counter == WIDTH-1) |-> pulse;"
            "property pulse_only_at_max; ... pulse |-> (dut.r_counter == WIDTH-1);"
  Actually: pulse is a registered output: "pulse <= (r_counter == w_width_minus_one);"
            inside the clocked block. Tracing it: during the cycle in which
            r_counter == WIDTH-1, pulse == 0; at the next edge pulse is set and the
            counter wraps — so pulse is high during the cycle in which r_counter == 0.
            Both assertions fail on the first pulse; the prose phase is off by one count.
  Impact:   A reader who binds the page's verification properties to the DUT gets
            immediate assertion failures on a correctly functioning module, and anyone
            gating logic on "pulse coincides with count WIDTH-1" builds an off-by-one.
```

---

### 6. `counter_load_clear.md` — "Load During Count" timing diagram shows a stall the RTL cannot produce

```
[CONFIRMED] counter_load_clear: diagram shows count holding during load; RTL increments regardless
  File:     docs/markdown/RTLCommon/counter_load_clear.md
  Says:     Under "Load During Count", with Increment drawn continuously high:
            "Count : < 0 >< 1 >< 2 >< 2 >< 3 >< 4 >< 5 >< 0 >" (note the repeated 2).
  Actually: RTL count logic is "if (clear) count <= 'b0; else if (increment)
            count <= (count == r_match_val) ? 'b0 : count + 'b1;" — load only updates
            r_match_val and has no effect on count. With increment held high the
            sequence must be 0,1,2,3,4,5,0; there is no hold cycle. (The same page's
            first diagram also shows done low from reset, but after reset
            count==r_match_val==0 so done is actually high until the first load —
            the RTL header itself documents "Reset state: count=0, r_match_val=0, done=1".)
  Impact:   Minor — a reader inferring "load stalls the counter" from the diagram is
            wrong; functional prose elsewhere on the page is correct.
```

---

### 7. Minor / unverifiable

```
[SUSPECTED] counter_bingray: example instantiates a module named `synchronizer` that may not exist in the library
  File:     docs/markdown/RTLCommon/counter_bingray.md
  Says:     "synchronizer #(.WIDTH(ADDR_WIDTH+1)) rd_sync ( .clk(wr_clk), ... .data_in(rd_gray), .data_out(rd_gray_sync) );"
  Actually: The module's own RTL header demonstrates CDC with
            "glitch_free_n_dff_arn #(.WIDTH(ADDR_WIDTH), .FLOP_COUNT(2))". No module
            named `synchronizer` appears in this review unit; I could not verify
            whether one exists elsewhere in the library.
  Impact:   If no such wrapper exists, the FIFO example does not compile as written.
```

---

## POSSIBLE RTL BUGS / RTL OBSERVATIONS

These are issues in the RTL itself, surfaced while verifying doc claims:

1. **`clock_pulse` counter register is O(WIDTH) instead of O(log2 WIDTH).**
   `logic [WIDTH-1:0] r_counter;` with `w_width_minus_one = WIDTH[WIDTH-1:0] - 1'b1` is functionally correct but allocates WIDTH flip-flops for a count that needs only `$clog2(WIDTH)`. A 1024-cycle period costs 1024 FFs instead of 10. Additionally, the bit-select `WIDTH[WIDTH-1:0]` on the 32-bit `int` parameter is out of range for WIDTH > 32. Suggest `logic [$clog2(WIDTH)-1:0] r_counter;`.

2. **`clock_gate_ctrl`: `N` used before declaration in the ANSI port list.**
   The port `input logic [N-1:0] cfg_cg_idle_count` references `N`, which is only declared as a `localparam` in the module body *after* the port list. Some tools accept this; others reject use-before-declaration here. Moving `localparam int N = IDLE_CNTR_WIDTH;` into the parameter port list (as a derived parameter) or using `IDLE_CNTR_WIDTH` directly in the port width removes the portability risk. (This likely also explains why the doc author believed `N` was a parameter.)

3. **`counter_freq_invariant`: unguarded LUT index when `NUM_FREQ_ENTRIES` is not a power of two.**
   `SEL_WIDTH = $clog2(NUM_FREQ_ENTRIES)`, so e.g. with 10 entries `freq_sel` is 4 bits and values 10–15 index out of bounds in `w_div_table[freq_sel]` → X in simulation, undefined after synthesis. The elaboration-time `param_check` validates other parameters but not this case.

---

## Overall accuracy

Seven of the nine pages (`counter`, `counter_bin`, `counter_bin_load`, `counter_bingray`, `counter_johnson` aside from the self-starting claim, `counter_load_clear` aside from one diagram, `clock_gate_ctrl` aside from the `N` parameter) are solid: module declarations, parameters, ports, priority behavior, wraparound sequences, and code snippets all match the RTL when traced. The two pages needing real work are `counter_freq_invariant.md`, which is wholesale stale — it documents the pre-2026-04-09 hardcoded-LUT implementation, and every parameter, the output port name, the frequency table, and the tick description are wrong for the current RTL — and `clock_pulse.md`, whose resource table describes a logarithmic-width counter the RTL does not have (off by ~100× at the largest tabulated WIDTH) and whose pulse-phase prose and formal properties are off by one cycle relative to the registered `pulse` output. The `counter_johnson` self-starting claim is a subtle but real functional misstatement worth fixing given the page explicitly ties the module to CDC-safe FIFO use.