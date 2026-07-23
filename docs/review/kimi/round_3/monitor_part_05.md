# Review: monitor_part_05

I checked every parameter table, port list, code example, and numeric table in the 12 pages against the RTL. The unit is mostly strong — the four `monbus_*_group` wrappers, `axi_monitor_trans_mgr`, `axi_monitor_timeout`, and the reporter sub-block pages are meticulous and match the RTL almost line-for-line. The serious defects are concentrated in `axi_monitor_timer.md` and `monbus_arbiter.md`.

## Findings

```
[CONFIRMED] The entire cfg_freq_sel tick-period table — and every configuration
            example derived from it — is fabricated. The RTL generates a ~1 MHz
            (1 µs) tick via a LINEAR frequency LUT (division factor = 5..220
            cycles), not a 2^sel cycle prescaler.
  File:     docs/markdown/RTLAmba/monitor/axi_monitor_timer.md
  Says:     "| cfg_freq_sel | Tick Period (cycles) | 100 MHz Period | 1 GHz Period |
             | 0 | 1 | 10 ns | 1 ns |  ... | 15 | 32768 | 327.68 us | 32.768 us |"
            plus: "cfg_freq_sel = 4'd6;  // 64 cycles per tick",
            "Recommended Range: cfg_freq_sel = 4-8 for most applications
            (16-256 cycles per tick)", and the usage math
            "At cfg_freq_sel=6 (64 cycles/tick): addr timeout = 8 ticks * 64
            cycles = 512 cycles" and "cfg_freq_sel = 10 (1024 cycles ~ 10us)".
  Actually: axi_monitor_timer instantiates counter_freq_invariant with
            MIN_FREQ_MHZ=5, MAX_FREQ_MHZ=220, NUM_FREQ_ENTRIES=16,
            FREQ_STRATEGY=0 (LINEAR). The LUT is
            freq[i] = 5 + (220-5)*i/15  =  5, 19, 33, 48, 62, 76, 91, 105, 119,
            134, 148, 162, ~176, 191, 205, 220 (integer division), and per the
            RTL "the division factor == cycles per microsecond == clock MHz,
            these values ARE the division factors directly." So sel=0 divides
            by 5 (not 1), sel=6 divides by 91 (not 64), sel=15 divides by 220
            (not 32768). The tick is ~1 µs when the chosen entry matches the
            real clock; at 100 MHz you would pick sel=6 or 7 (0.91/1.05 µs),
            not "640 ns". No FREQ_STRATEGY produces the documented table
            (POW2 would give 5,10,20,40,80,160,220,220...). Even the doc's own
            guideline is self-contradictory: "1us = 100 cycles -> cfg_freq_sel
            = 10 (1024 cycles ~ 10us)" — 1024 cycles is not 100.
  Impact:   The single most damaging defect in the unit. Anyone configuring
            timeout ticks from this table gets tick periods wrong by 5x
            (sel=0) up to ~149x (sel=15: documented 32768 cycles, actual 220).
            All four "Configuration Strategy" snippets and the timeout-duration
            example in the usage section are likewise wrong. Note this page is
            dated 2025-10-24 while the rest of the unit is 2026-07-15 — it
            appears to predate the counter_freq_invariant refactor and was
            never updated.
```

```
[CONFIRMED] The counter_freq_invariant instantiation example would not
            elaborate: wrong parameter name/value and wrong port name.
  File:     docs/markdown/RTLAmba/monitor/axi_monitor_timer.md
  Says:     "counter_freq_invariant #(
                 .COUNTER_WIDTH (1),        // Only need 1-bit counter (tick pulse)
                 .PRESCALER_MAX (65536)     // Maximum prescaler value
             ) timer_counter ( ... .freq_sel (cfg_freq_sel), .tick (w_timer_tick),
                 .counter ()             // Counter output unused );"
            and "PRESCALER_MAX=65536: Supports full frequency selection range"
  Actually: The RTL instantiation passes .MIN_FREQ_MHZ/.MAX_FREQ_MHZ/
            .NUM_FREQ_ENTRIES/.FREQ_STRATEGY (no PRESCALER_MAX), and the
            counter port is .o_counter(). In counter_freq_invariant,
            PRESCALER_MAX is a *derived* parameter ("do not override"):
            DIV_WIDTH = $clog2(220+1) = 8, so PRESCALER_MAX = 2**8 = 256,
            not 65536. There is no port named `counter`.
  Impact:   A reader copying the example hits an elaboration error on the
            port name and misleads themselves about the prescaler range.
```

```
[CONFIRMED] Reporter documented as driving a monbus_timestamp output that
            does not exist.
  File:     docs/markdown/RTLAmba/monitor/axi_monitor_reporter.md
  Says:     "The reporter drives `monbus_packet` (128b) and `monbus_timestamp`
            (64b) together so the side-band timestamp travels paired with each
            packet through the arbiter and into the monbus_group family."
  Actually: The axi_monitor_reporter port list contains only monbus_ready,
            monbus_valid and monbus_packet on the MonBus side — there is no
            monbus_timestamp port anywhere in the module. (monbus_arbiter and
            monbus_group_core do carry timestamps, but the reporter produces
            none.)
  Impact:   A reader instantiating the reporter per this doc looks for a
            nonexistent port; misunderstanding of where the side-band
            timestamp enters the MonBus path.
```

```
[CONFIRMED] Documented grant_ack equation omits the downstream-ready term —
            it shows exactly the pre-fix buggy form the RTL comments call out.
  File:     docs/markdown/RTLAmba/monitor/monbus_arbiter.md
  Says:     "Grant ACK Logic: ACK occurs when both grant is asserted AND client
            has valid data:  grant_ack[i] = grant[i] && monbus_valid_in[i]"
            (repeated verbatim in the ACK Mode Operation design note).
  Actually: RTL: "grant_ack[i] = grant[i] && int_monbus_valid_in[i] &&
            int_monbus_ready;" with an explicit comment: "Omitting the ready
            term (the original `grant[i] && int_monbus_valid_in[i]`) made the
            ack fire every cycle while the sink was backpressuring, so the
            grant rotated continuously with ZERO transfers taking place...
            Regression: val/amba/test_monbus_arbiter_grant_hold.py".
  Impact:   A reader learns the grant-rotation semantics of the buggy
            revision: they would expect the grant to advance under
            backpressure (it does not) and could design a client that drops
            packets. This doc page documents behavior the RTL explicitly
            fixed.
```

```
[CONFIRMED] "Zero-latency pass-through when skid buffers disabled" is false;
            the valid path always passes through a registered grant.
  File:     docs/markdown/RTLAmba/monitor/monbus_arbiter.md
  Says:     "Zero-latency pass-through when skid buffers disabled" and
            "This provides direct combinational paths:
             - monbus_valid_in[grant_id] -> monbus_valid (combinational)
             - monbus_packet_in[grant_id] -> monbus_packet (combinational)
             - monbus_ready -> monbus_ready_in[grant_id] (combinational)"
  Actually: monbus_valid = int_monbus_valid = grant_valid, and grant_valid is
            a *registered* output of arbiter_round_robin ("grant_valid <=
            w_next_grant_valid" in the always_ff). A client's valid must first
            be granted (one registered cycle) before appearing at the output,
            skid or no skid. The data and ready paths are combinational *given
            a grant*, but the valid path is not.
  Impact:   Latency budgeting / event-ordering assumptions based on
            "zero-latency" are off by at least one cycle; the key-feature
            bullet advertises a configuration that does not exist.
```

```
[CONFIRMED] Documented latency-over-threshold predicate includes a term the
            RTL deliberately removed because it made the flag self-clearing.
  File:     docs/markdown/RTLAmba/monitor/axi_monitor_reporter_threshold.md
  Says:     "a companion flag `r_latency_over_thresh[idx]` is set when the slot
            is valid, in `TRANS_COMPLETE` state, its latency exceeds
            `latency_threshold`, and the latency edge flag is not already set."
  Actually: RTL: "r_latency_over_thresh[idx] <= trans_table[idx].valid &&
            (trans_table[idx].state == TRANS_COMPLETE) && (lat >
            latency_threshold);" — with the comment "NOTE: deliberately NOT
            qualified by r_latency_crossed ... Folding the flag in here made
            the condition self-clearing." (r_latency_crossed gates the *output
            mux* instead: "w_has_lat && !r_latency_crossed && !output_busy".)
  Impact:   Anyone reimplementing or formally modeling the block from this doc
            reproduces the exact bug the RTL comment describes: a
            self-clearing flag and exactly one latency packet ever emitted.
```

```
[CONFIRMED] Perf doc claims pkt_taken is observational and tied to an unused
            net; in the RTL it functionally gates the FSM state advance.
  File:     docs/markdown/RTLAmba/monitor/axi_monitor_reporter_perf.md
  Says:     Port table: "pkt_taken ... (currently observational — see Design
            Notes)"; Design Notes: "`pkt_taken` is on the port list but does
            not gate the counters today ... The port is retained for future
            hooks ... The RTL ties it to an `unused` net to keep lint clean."
  Actually: In axi_monitor_reporter_perf: "if (!(pkt_valid && !pkt_taken))
            begin r_state <= w_next_state; end" — pkt_taken holds the FSM when
            a presented packet loses arbitration (the RTL comment: "Advancing
            regardless silently dropped the packet"). There is no unused-net
            tie for pkt_taken in this module (that tie exists in
            axi_monitor_reporter_debug, not here). The narrower claim that it
            "does not gate the counters" is true.
  Impact:   A reader believes pkt_taken can be ignored; in fact it is part of
            the correctness path that prevents perf packets from being dropped
            when threshold wins the output mux. The "tied to unused" statement
            is verifiably false.
```

```
[CONFIRMED] (minor) Threshold doc's pkt_taken port description contradicts the
            same page's functional description and the RTL.
  File:     docs/markdown/RTLAmba/monitor/axi_monitor_reporter_threshold.md
  Says:     Port table: "pkt_taken ... Pulsed by the top reporter when this
            block's packet was accepted; clears the edge flag and arms the
            next detection" — while the same page's Edge-Sticky Flags section
            says "r_active_crossed — *set* when an active-count packet is
            accepted (pkt_taken with matching type/event code)".
  Actually: RTL: on pkt_taken the flags are SET ("r_active_crossed <= 1'b1" /
            "r_latency_crossed <= 1'b1"); they clear later when the crossing
            condition lifts ("w_active_count <= active_trans_threshold" /
            "!w_has_lat").
  Impact:   Internal contradiction; a reader trusting the port table inverts
            the flag polarity.
```

```
[CONFIRMED] (minor) Timer doc claims combinational/zero-latency outputs that
            are registered.
  File:     docs/markdown/RTLAmba/monitor/axi_monitor_timer.md
  Says:     Key Features: "Zero-latency timestamp (combinational output)";
            Functional Description: "Combinational output (w_timer_tick)" —
            yet the same page also says "Registered output (r_timestamp)".
  Actually: "assign timestamp = r_timestamp;" where r_timestamp is a flop, and
            timer_tick = w_timer_tick comes from counter_freq_invariant's
            `tick`, which is assigned inside an always_ff there ("tick <=
            1'b1"). Neither output is combinational from any input.
  Impact:   Low — mostly a self-contradiction on the page; the "registered
            output" phrasing elsewhere on the same page is the accurate one.
```

```
[CONFIRMED] (minor) Reporter Key Features advertise multi-protocol
            identification the module does not perform.
  File:     docs/markdown/RTLAmba/monitor/axi_monitor_reporter.md
  Says:     "Protocol identification (AXI4, AXI5, APB, AXIS, CORE)"
  Actually: "monbus_packet = create_monitor_packet(r_packet_type,
            PROTOCOL_AXI, ...)" — the protocol field is hardwired to
            PROTOCOL_AXI; this reporter can never emit AXI5/APB/AXIS/CORE
            packets (the format supports them; this module does not tag them).
  Impact:   Low-moderate — overstates the module's role in a multi-protocol
            monitor system.
```

```
[SUSPECTED] Arbiter usage example connects output ports with assignment
            patterns, which are not legal lvalues for output port connections.
  File:     docs/markdown/RTLAmba/monitor/monbus_arbiter.md
  Says:     ".monbus_ready_in ('{mon0_ready, mon1_ready, mon2_ready,
            mon3_ready}),"
  Actually: monbus_ready_in is an output. IEEE 1800 permits only
            concatenations ({...}) as port lvalues; an assignment pattern
            ('{...}) is an rvalue construct. Strict tools reject this. (The
            same patterns on the *input* ports are fine.) I could not compile
            to confirm, hence SUSPECTED.
  Impact:   Copy-paste of the example fails to compile on compliant tools.
```

## POSSIBLE RTL BUGS

None found beyond those the RTL already documents in its own comments. One latent fragility noted but **not** a live bug: in `axi_monitor_reporter_perf`, the counters are updated by a for-loop of non-blocking assignments (`if (error_marked_mask[idx]) r_error_count <= r_error_count + 1'b1;`), which increments at most once per cycle regardless of how many mask bits are set. The top reporter guarantees a single-bit mask by construction (one FIFO accept per cycle), so behavior is correct today, but the loop shape would silently under-count if that contract ever changed.

## Overall assessment

This unit is a tale of two halves. The newer pages (dated 2026-07-15) — the four `monbus_*_group` wrappers, `axi_monitor_trans_mgr`, `axi_monitor_timeout`, `axi_monitor_reporter` and its `timeout`/`threshold` sub-blocks — are excellent: every parameter default, port width, FSM state, auto-retire rule, and serializer mechanism I recomputed matched the RTL, and the design-note narrative (saturation recovery, same-cycle AW+W bypass, 2:1 drain serializer) faithfully mirrors the RTL comments. Against that, `axi_monitor_timer.md` is stale to the point of being dangerous — its frequency-selection table, all four configuration snippets, and the instantiation example describe hardware that does not exist (wrong division model, wrong port name, wrong derived parameter) — and `monbus_arbiter.md` documents the pre-fix `grant_ack` equation that the RTL explicitly calls out as a resolved bug, plus a "zero-latency" claim contradicted by the registered grant. Fixing those two pages, the reporter's phantom `monbus_timestamp` port, the threshold predicate, and the perf `pkt_taken` note would bring the unit to the same standard as its best pages.