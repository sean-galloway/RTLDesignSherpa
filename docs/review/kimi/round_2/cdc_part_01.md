# Review: `cdc_part_01` (RTL Clock Domain Crossing, part 1 of 2)

I checked every parameter table, port list, state table, worked example, and code snippet against the RTL in `RTL.sv`. The headline reset-behavior analysis (2-phase phantom-transfer mechanism, per-flop reset domains, async-FIFO local-reset robustness) verified line-by-line against `cdc_2_phase_handshake.sv`, `cdc_4_phase_handshake.sv`, `fifo_async.sv`, and `gaxi_fifo_async.sv` and is correct. The defects I found cluster in the Johnson-code pages and the `clock_pulse`/`glitch_free_n_dff_arn` pages.

---

## Findings

```
[CONFIRMED] cdc.md claims johnson2bin is "registered"; the module is purely combinational
  File:     docs/markdown/RTLAmba/cdc/cdc.md
  Says:     "| 1 | Johnson | `DEPTH` | `johnson2bin` (registered) | any even depth |"
            and "| Per domain: gray->bin converter | 0 (combinational) | 6 (registered) |"
            and "| Per domain: bin converter | 0 (combinational) | 7 (registered) |"
            and "a combinational `gray2bin` instead of a registered `johnson2bin`"
  Actually: rtl/common/johnson2bin.sv declares `clk`/`rst_n` but never uses them;
            the entire decode is one `always_comb` block feeding continuous assigns
            (`assign binary[WIDTH-1] = gray[JCW-1];`). johnson2bin.md states this
            explicitly: "The conversion is entirely combinational... Do not expect
            a cycle of latency."
  Impact:   The two flop-cost walkthroughs are wrong. 512-bit example, Johnson
            depth 20: per domain = 6 (bin) + 20 (Johnson) + 2x20 (sync) + 0 (comb
            converter) = 66, so both domains = ~132, not "~144", and the delta vs
            Gray is +84, not "+96 flops". ASIC depth-36 example: per domain =
            7 + 36 + 72 = 115, both = ~230, not "~244"; delta = +174, not "+188".
            A reader may also budget a nonexistent pipeline stage of latency.
```

```
[CONFIRMED] Both worked conversion examples on the johnson2bin page are wrong
            (mirror-image convention the page itself disclaims)
  File:     docs/markdown/RTLCommon/johnson2bin.md
  Says:     "Johnson: 001111 (w_leading_one = 5, w_trailing_one = 2) ...
            Binary: 000110" and "Johnson: 111000 (w_leading_one = 0,
            w_trailing_one = 2) ... Binary: 100010"; also Key Properties:
            "First half (0 to DEPTH-1): Filling with 1s from left" and
            "Second half (DEPTH to 2xDEPTH-1): Emptying 1s from left"
  Actually: counter_johnson.sv shifts `{counter_gray[WIDTH-2:0],
            ~counter_gray[WIDTH-1]}` — ones enter at bit 0 (the RIGHT), matching
            the page's own JCW=6 sequence and its "Fill direction" erratum note.
            For input 001111: find_last_set gives leading_one=3, find_first_set
            gives trailing_one=0; first-half decode = leading_one+1 = 4, so
            binary = 000100 (state 4 of the sequence — correct). The doc's 000110
            is count 6, which for DEPTH=6 is the all-ones state the RTL
            special-cases to 0. For input 111000: leading_one=5, trailing_one=3;
            second-half decode = trailing_one = 3, so binary = 100011 (wrap bit +
            3 = state 9 — correct). The doc's 100010 decodes to state 8 (111100).
            The values the doc cites (5/2 and 0/2) are the leading/trailing
            positions of the MSB-fill mirror images.
  Impact:   A reader verifying the module or reimplementing the decode against
            these examples gets wrong position values and wrong binary outputs.
            The page's erratum note says the examples "inherited the error" —
            they still contain it.
```

```
[CONFIRMED] glitch_free_n_dff_arn page calls the reset "synchronous"; it is
            asynchronous active-low
  File:     docs/markdown/RTLCommon/glitch_free_n_dff_arn.md
  Says:     "- **Synchronous reset**: Uses destination domain reset"
  Actually: rtl/common/glitch_free_n_dff_arn.sv uses `ALWAYS_FF_RST(clk, rst_n,
            ...)`, which expands to `always_ff @(posedge clk or negedge rst_n)`
            (confirmed by the macro-free formal copy of cdc_handshake in the
            bundle). The page's own code block immediately above shows
            `always_ff @(posedge clk or negedge rst_n)`, and the RTL header says
            "Asynchronous reset for all pipeline stages".
  Impact:   A reader is misinformed about assertion behavior — relevant to
            recovery/removal analysis and to the page's own reset-synchronizer
            example pattern.
```

```
[CONFIRMED] "Further reduces MTBF" is backwards
  File:     docs/markdown/RTLCommon/glitch_free_n_dff_arn.md
  Says:     "3. **Stage 3+ (FFN)**: Further reduces MTBF (Mean Time Between
            Failures)"
  Actually: Extra stages increase MTBF — the page's own table says 3 stages ->
            "Years", 4 stages -> "Millennia".
  Impact:   Inverts the latency-vs-reliability trade-off for a reader sizing a
            synchronizer chain. One-word slip, but actively misleading.
```

```
[CONFIRMED] clock_pulse resource table assumes a clog2(WIDTH) counter; the RTL
            counter is WIDTH bits
  File:     docs/markdown/RTLCommon/clock_pulse.md
  Says:     "| WIDTH | Counter Bits | LUTs | FFs | Max Freq |" with rows
            "| 8 | 3 | 8 | 4 | 500MHz |" ... "| 1024 | 10 | 28 | 11 | 350MHz |"
  Actually: rtl/common/clock_pulse.sv declares `logic [WIDTH-1:0] r_counter;` —
            a WIDTH-bit counter. So WIDTH=8 -> 9 FFs (not 4), WIDTH=16 -> 17
            (not 5), WIDTH=32 -> 33 (not 6), WIDTH=1024 -> ~1025 FFs (not 11).
            The page's own "Internal Counter" code block shows the WIDTH-bit
            declaration, so the table contradicts the page as well as the RTL.
  Impact:   Area underestimated by ~2x at WIDTH=8 and ~100x at WIDTH=1024; LUT
            columns are likewise off. Anyone sizing from this table gets wrong
            numbers on every row.
```

```
[CONFIRMED] clock_pulse formal properties are off by one cycle and would fail
  File:     docs/markdown/RTLCommon/clock_pulse.md
  Says:     "property pulse_at_max_count; @(posedge clk) disable iff (!rst_n)
            (dut.r_counter == WIDTH-1) |-> pulse;" and
            "property pulse_only_at_max; ... pulse |-> (dut.r_counter == WIDTH-1);"
  Actually: RTL registers the pulse: `pulse <= (r_counter ==
            w_width_minus_one);`. Tracing from reset: when r_counter==WIDTH-1
            (sampled), pulse is still 0; pulse is 1 during the following cycle,
            when r_counter==0. Both overlapped implications therefore fail on
            the real timing. They need `|=>` (and the second property's
            consequent should be r_counter == 0).
  Impact:   Copy-pasted formal checks fail immediately; a reader "verifying" the
            module would chase a nonexistent bug.
```

```
[SUSPECTED] fifo_async test path disagrees with the RTL headers
  File:     docs/markdown/RTLAmba/cdc/cdc.md
  Says:     "| `fifo_async` | `rtl/common/fifo_async.sv` |
            `rtl/common/filelists/fifo_async.f` | `val/common/test_fifo_buffer_async.py` |"
  Actually: The fifo_async.sv header gives "Location:
            val/common/test_fifo_async.py"; fifo_control.sv's header likewise
            references `val/common/test_fifo_async*.py`. Nothing in the RTL
            bundle references test_fifo_buffer_async.py. I could not check the
            filesystem, so this stays SUSPECTED.
  Impact:   Possibly a broken test pointer in the module-reference table.
```

```
[SUSPECTED] Examples instantiate a `synchronizer` module that does not exist
            in the library
  File:     docs/markdown/RTLCommon/bin2gray.md (cross_domain_counter example);
            same pattern in docs/markdown/RTLCommon/counter_bingray.md
            (Cross-Domain Synchronization example)
  Says:     "synchronizer #(.WIDTH(WIDTH)) gray_sync ( .clk(dst_clk),
            .rst_n(dst_rst_n), .data_in(src_gray), .data_out(dst_gray_sync) );"
  Actually: No module named `synchronizer` exists in the provided RTL. The
            library equivalents are `cdc_synchronizer` (ports `async_in`/
            `sync_out`) and `glitch_free_n_dff_arn` (ports `d`/`q`) — and
            bin2gray.md itself recommends those two modules elsewhere on the
            same page.
  Impact:   The example does not compile against the library as written; a
            reader must rename the module and remap the ports.
```

```
[SUSPECTED] 4-phase latency claims look ~3x low relative to the doc's own model
  File:     docs/markdown/RTLAmba/cdc/cdc.md
  Says:     "| 2-phase -> 4-phase | Costs ~2 destination clocks of latency.
            Always safe. |" and "**Latency:** ~7-8 destination clocks per
            transfer (vs ~5-6 for 2-phase)."
  Actually: The doc's own framing is "two synchronizer crossings per transfer
            instead of four", and each crossing costs SYNC_STAGES clocks
            (default 3). The two extra crossings (ack return in src clocks,
            req-clear in dst clocks) add ~6 clock periods of round-trip at the
            default depth, not ~2. I could not derive any SYNC_STAGES/clock-
            ratio combination that yields "7-8 vs 5-6", so I leave this
            SUSPECTED rather than CONFIRMED.
  Impact:   Latency budget for the variant swap is understated; low severity
            since the figures are explicitly approximate.
```

---

## POSSIBLE RTL BUGS

Nothing that changes logic behavior. Two comment-level defects worth fixing because they are the likely source of doc finding #1:

- `rtl/common/fifo_async.sv` and `rtl/amba/gaxi/gaxi_fifo_async.sv` both carry the stale comment `// johnson2bin is registered (takes clk/rst_n).` above the Johnson converter instantiations, and `fifo_async.sv`'s `USE_JOHNSON` parameter comment says "converted with johnson2bin (registered)". The module is combinational; the comments are wrong.
- `rtl/common/clock_pulse.sv` uses a `WIDTH`-bit counter (`logic [WIDTH-1:0] r_counter;`) to count to `WIDTH-1`. Functionally correct, but it wastes `WIDTH - clog2(WIDTH)` registers — a 1024-bit counter at `WIDTH=1024` where 10 bits suffice. Not a doc defect, but the doc's resource table (finding #5) conceals it rather than revealing it.

---

## Overall assessment

This part of the book is in good shape, and unusually honest: the verification-status section scopes the formal proofs correctly, the 2-phase asymmetric-reset hazard is explained precisely and matches the RTL flop-by-flop (the `w_req_event = w_req_sync ^ r_req_sync_d` XOR, the per-domain reset table, and the phantom-transfer waveform narrative all check out), and the Gray/Johnson state-walk table is exactly right — I re-deriving every row against `counter_johnson.sv`'s recurrence. The parameter and port tables for `cdc_synchronizer`, `cdc_open_loop`, both handshakes, `apb_slave_cdc`, and `apb_slave_cdc_cg` match the RTL without exception, and every arithmetic entry in the depth-sizing and storage-overhead tables recomputes cleanly. The real problems are concentrated: (1) the stale "johnson2bin is registered" premise that infects both flop-cost walkthroughs in `cdc.md` and directly contradicts `johnson2bin.md`; (2) the two still-broken worked examples on the `johnson2bin` page, which sit directly beneath an erratum note saying they were the problem; and (3) the `clock_pulse` page, whose resource table and formal properties both fail against a trivially traceable RTL. Fix those and the two reset/MTBF mislabels in `glitch_free_n_dff_arn.md`, and this book is accurate.