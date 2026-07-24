# Review: monitor_part_03 (AXI5 monitor wrappers)

Scope checked: all 7 doc files against their wrapper RTL plus the shared dependencies (`axi_monitor_base`, `axi_monitor_filtered`, reporter sub-blocks, `axi_monitor_trans_mgr`, `amba_clock_gate_ctrl`, `clock_gate_ctrl`, `axi_monitor_addr_check`). All parameter tables (names + defaults, incl. AGENT_ID 0xA/0xB/0xC/0xD = 10/11/12/13), the perfmon port lists, the 128-bit packet field layout, the `block_ready`/saturation-recovery prose, the `cfg_timeout_cycles` 0/1–15/>15 encoding, and the addr-range checker encoding were verified and are **accurate** unless listed below. Numeric recomputations are shown per finding.

---

## Findings

```
[CONFIRMED] Level-1 filter mask documented with inverted polarity and wrong bit indices
  File:     docs/markdown/RTLAmba/monitor/axi5_master_rd_mon.md
  Says:     "cfg_axi_pkt_mask[0] = 1 → Enable ERROR packets ... [2] → Enable TIMEOUT
             packets [3] → Enable THRESH packets ... [5] → Enable ADDR packets
             [6] → Enable DEBUG packets"
  Actually: RTL in axi_monitor_filtered: "pkt_drop = cfg_axi_pkt_mask[pkt_type];" —
            a set bit DROPS the type, it does not enable it. The same page's own
            packet-format diagram says 0x2=THRESH, 0x3=TIMEOUT, 0x8=ADDR_MATCH,
            0xF=DEBUG, and its own usage example says ".cfg_axi_pkt_mask(16'hFFF4)
            // Drop all but ERROR|COMPL|TIMEOUT (set bit = drop)". 16'hFFF4 has
            bit2=1/bit3=0, consistent only with THRESH=2 dropped, TIMEOUT=3 passed.
  Impact:   A reader following the Level-1 block writes an inverted mask targeting
            the wrong bits: timeouts silently dropped, thresholds passed, and the
            ADDR/DEBUG bits written to reserved slots ([5]/[6]) instead of [8]/[15].
```

```
[CONFIRMED] cfg_axi_err_select ("Level 2") documented as functional error routing; RTL ignores it
  File:     docs/markdown/RTLAmba/monitor/axi5_master_rd_mon.md
  Says:     "Level 2: Error Routing (cfg_axi_err_select) — Determines whether errors
             generate ERROR packets or COMPL packets with error status."
  Actually: In axi_monitor_filtered, cfg_axi_err_select appears in exactly one place:
            "assign cfg_conflict_error = |(cfg_axi_pkt_mask & cfg_axi_err_select);"
            Its port comment states "Error select for packet types (unused in this
            context)". It is not forwarded to axi_monitor_base (which has no such
            port) and no error→COMPL re-routing logic exists anywhere.
  Impact:   A reader configures err_select expecting error re-routing and gets none;
            the only observable effect is a spurious cfg_conflict_error when bits
            overlap pkt_mask. The page even prints the conflict formula, which
            contradicts the routing claim on its face.
```

```
[CONFIRMED] ENABLE_PERF_LOGIC does not gate the perfmon window/counters; perfmon outputs are NOT tied to 0 when it is 0
  File:     docs/markdown/RTLAmba/monitor/axi5_master_rd_mon.md (also axi5_master_wr_mon.md,
            axi5_slave_rd_mon.md, axi5_slave_wr_mon.md; same wrong description forwarded in
            all three *_mon_cg.md parameter tables)
  Says:     "ENABLE_PERF_LOGIC | bit | 1 | Compile-in the perfmon measurement window and
             utilization/throughput counters" and "When USE_MONITOR = 0
             (or ENABLE_PERF_LOGIC = 0) all perfmon outputs are tied to 0."
  Actually: In axi_monitor_base the window state machine (r_win_state, edge detect,
            start/end muxes) and the bucket/beat/byte/burst counters are unconditional
            module-body RTL — no generate guard. ENABLE_PERF_LOGIC only gates the
            reporter's legacy count-rollup sub-block ("if (ENABLE_PERF_LOGIC) begin :
            g_perf ... axi_monitor_reporter_perf"), i.e. perf_completed_count/
            perf_error_count and the PktTypePerf count packets. With
            ENABLE_PERF_LOGIC=0 and USE_MONITOR=1, window_active/window_cycles/
            perf_prod/bp/starv/idle/beat/byte/burst all still operate.
  Impact:   A user sets ENABLE_PERF_LOGIC=0 to strip the perfmon cone for area (or to
            silence it) and gets neither: the window/counters remain fully synthesised
            and live. (Related imprecision in the same section: the window is also not
            gated by cfg_perf_enable — start events 000/001/011/100 fire without it.)
```

```
[CONFIRMED] Detection claims with no implementing logic: poison, tag mismatch, missing WLAST, ATOP monitoring, handshake/alignment/strobe/ID-width violations
  File:     docs/markdown/RTLAmba/monitor/axi5_slave_wr_mon.md, axi5_master_wr_mon.md,
            axi5_slave_rd_mon.md, axi5_master_rd_mon.md, axi5_slave_wr_mon_cg.md
  Says:     "0x5 | Poison detected", "0x6 | Tag mismatch", "0x7 | Missing WLAST"
            (slave event tables); "Poison Detection: WPOISON indicator tracked per
            beat ... Generates error packet when poison detected"; "Detects missing
            WLAST errors"; "Monitors AWATOP field when ENABLE_ATOMIC=1"; "Atomic
            operation type (from AWATOP) ... Tag validation (BTAGMATCH)"; "AR/R
            handshake violations, ID width mismatches, Burst length violations,
            Unaligned addresses, Strobe violations"; example decoder
            "if (mon_packet[104:97] == 8'h5)  // AXI5_POISON_DETECTED".
  Actually: The monitor's only taps are cmd_addr/cmd_id/cmd_len/cmd_size/cmd_burst +
            valid/ready, data_id/data_last/data_resp + valid/ready, and
            resp_id/resp_code + valid/ready (axi_monitor_filtered port list). No
            poison, tag, ATOP, WSTRB or WLAST-checking signal reaches the monitor,
            and axi_monitor_trans_mgr/reporter_error contain no such checks — the
            complete emitted error set is SLVERR, DECERR, DATA_ORPHAN, RESP_ORPHAN,
            EVT_PROTOCOL (response-before-data), the three timeouts, threshold
            crossings, and ADDR_RANGE. No event codes 0x5/0x6/0x7 are ever emitted.
  Impact:   Users enable poison/MTE/atomic monitoring expecting the documented error
            packets and decode a stream that never contains them; compliance
            checklists built on these tables are wrong.
```

```
[CONFIRMED] Slave-doc event tables: Timeout listed as Type=2 (contradicts same page), and every Event Data column is wrong
  File:     docs/markdown/RTLAmba/monitor/axi5_slave_rd_mon.md, axi5_slave_wr_mon.md
  Says:     "#### Timeout Packets (Type=2)"; error event data "Transaction ID,
             address[18:0]"; completion data "Transaction ID, burst length,
             latency"; timeout data "Transaction ID, cycles elapsed"; perf table
             "0x1 High latency | ... 0x2 Bandwidth sample ... 0x3 Outstanding count".
  Actually: (a) The same pages' format diagram and filter list say 0x2=THRESH,
            0x3=TIMEOUT; RTL emits PktTypeTimeout for timeouts (reporter_timeout)
            and PktTypeThreshold for threshold events. (b) RTL packet payloads:
            reporter_error/timeout/compl all drive "pkt_data = pad_address(...)" —
            a 64-bit zero-extended 32-bit address. No ID, burst length, latency, or
            cycle count is in event_data (the ID appears only as channel = id % 64
            in the channel field). (c) The perf FSM (axi_monitor_reporter_perf)
            emits exactly two packet kinds — AXI_PERF_COMPLETED_COUNT and
            AXI_PERF_ERROR_COUNT, data = the 16-bit counts; states 0–2 emit nothing.
            High-latency events exist only as PktTypeThreshold/AXI_THRESH_LATENCY.
            "Bandwidth sample" and "Outstanding count" perf packets do not exist.
  Impact:   Any monbus decoder written from these tables mislabels every packet and
            parses garbage from the payload field.
```

```
[CONFIRMED] Clock-gating activity formula uses BREADY; RTL uses BVALID (and forbids READY in the activity term)
  File:     docs/markdown/RTLAmba/monitor/axi5_master_wr_mon_cg.md,
            docs/markdown/RTLAmba/monitor/axi5_slave_wr_mon_cg.md
  Says:     "user_valid = fub_axi_awvalid || fub_axi_wvalid || fub_axi_bready || int_busy;"
            and "user_valid: Asserted when slave interface has activity (awvalid,
            wvalid, bready, or internal busy)".
  Actually: RTL: "assign user_valid = fub_axi_awvalid || fub_axi_wvalid ||
            fub_axi_bvalid || int_busy;" (slave: s_axi_bvalid). The RTL comment states
            explicitly: "A peer's READY must never appear in the activity term: a
            consumer that parks its response-ready high while idle ... would pin this
            block permanently awake and defeat gating entirely."
  Impact:   A reader modelling or replicating the gating logic builds in the exact
            anti-pattern the RTL was written to avoid.
```

```
[CONFIRMED] "Monitor continues operating/tracking when gated" and "monitor stays awake while a window is open" are false — the monitor is on the gated clock
  File:     docs/markdown/RTLAmba/monitor/axi5_master_wr_mon_cg.md,
            axi5_slave_rd_mon_cg.md, axi5_slave_wr_mon_cg.md
  Says:     "Monitor continues to track transactions even when gated" (Key Points,
            both slave _cg pages); "The monitor continues operating during clock
            gating transitions"; "// - Monitor has pending packets (implicit in
            int_busy)"; "Clock gating never suppresses these paths: while a
            measurement window is open the monitor stays awake, so window cycle
            accounting remains exact regardless of the idle-count setting."
  Actually: The inner monitor is instantiated with ".aclk(gated_aclk)". The activity
            terms are only valids + int_busy, and int_busy is the CORE's busy
            (skid counts + port valids) — in the mon wrappers the monitor's own
            .busy() output is left unconnected (PINCONNECTEMPTY). window_active,
            reporter-FIFO occupancy and monbus_valid appear nowhere in user_valid/
            axi_valid. When the clock gates, the monitor is frozen: pending monbus
            packets are not emitted, an open perf window stops counting, and
            cfg_window_force_close / cfg_end_trigger (sampled on the gated clock)
            have no effect until AXI activity resumes.
  Impact:   Software that opens a window or queues packets and then idles the bus
            waits indefinitely for results the docs say will keep flowing; the
            claimed exactness of window accounting under gating does not hold.
```

```
[CONFIRMED] "Gate after 8 idle cycles" comment contradicts the idle-count value (4'd3 → 4 cycles)
  File:     docs/markdown/RTLAmba/monitor/axi5_slave_rd_mon_cg.md,
            docs/markdown/RTLAmba/monitor/axi5_slave_wr_mon_cg.md
  Says:     ".cfg_cg_idle_count  (4'd3),          // Gate after 8 idle cycles"
  Actually: clock_gate_ctrl decrements the loaded count to zero and gates at zero;
            its own header documents "Gating latency: cfg_cg_idle_count + 1 clocks".
            Recompute: 3+1 = 4 cycles (the axi5_master_wr_mon_cg.md example in this
            same book correctly comments "4'd3 // Gate after 4 idle cycles").
            8 looks like someone read the literal 3 as a 2^3 exponent.
  Impact:   Power/latency budgeting off by 2x; contradicts the sibling page.
```

```
[CONFIRMED] "Oldest packets dropped if buffer full" — the RTL never drops; it retries and back-pressures
  File:     docs/markdown/RTLAmba/monitor/axi5_master_rd_mon.md
  Says:     "The monitor respects monbus_ready backpressure: - Packets buffered
             internally when monbus_ready = 0 - Oldest packets dropped if buffer full"
  Actually: In axi_monitor_reporter, an event is only marked reported on an accepted
            FIFO write ("w_fifo_wr_accept = w_fifo_wr_valid && w_fifo_wr_ready"); if
            the FIFO is full the transaction-table entry stays unmarked and the
            packet is re-offered every cycle until accepted. No drop path exists
            (the only retirements without emission are the documented auto-retire of
            runtime-disabled classes and per-range coalescing in addr_check). Sustained
            congestion propagates to block_ready and stalls the AXI channel instead.
  Impact:   A reader sizes downstream buffering believing loss is possible (or,
            worse, believes loss is bounded) when the real failure mode is datapath
            back-pressure, not packet loss.
```

```
[CONFIRMED] "Error count saturates at max value (does not wrap)" — the counters wrap
  File:     docs/markdown/RTLAmba/monitor/axi5_slave_rd_mon.md,
            docs/markdown/RTLAmba/monitor/axi5_slave_wr_mon.md
  Says:     "- Error count saturates at max value (does not wrap)"
  Actually: axi_monitor_reporter_perf: "if (error_marked_mask[idx]) r_error_count <=
            r_error_count + 1'b1;" — a plain 16-bit increment with no saturation
            term; same for r_completed_count. They wrap through 16'hFFFF.
  Impact:   Long-running soak tests reading error_count near 2^16 events will see a
            wrap the docs say cannot happen.
```

```
[CONFIRMED] Mermaid diagrams label monbus_packet as 64-bit; the packet is 128-bit
  File:     docs/markdown/RTLAmba/monitor/axi5_master_rd_mon.md ("monbus_packet<br/>[63:0]"),
            axi5_master_wr_mon.md (same), axi5_slave_rd_mon.md ("monbus_packet[63:0]"),
            axi5_slave_wr_mon.md (same)
  Says:     MONBUS subgraph shows monbus_packet[63:0].
  Actually: All four wrappers output "monitor_common_pkg::monitor_packet_t monbus_packet
            // Monitor packet (128-bit)", and the same pages' own text/format diagram
            describe 128 bits ([127:124] packet type ... [63:0] event data). The three
            *_mon_cg diagrams correctly show [127:0].
  Impact:   Contradicts the same page's packet-format section; stale label from the
            old 64-bit format.
```

```
[CONFIRMED] Status outputs mislabelled "(placeholder)" — they are live counters
  File:     docs/markdown/RTLAmba/monitor/axi5_master_wr_mon_cg.md
  Says:     "error_count | 16 | Output | Cumulative error count (placeholder)";
            "transaction_count | 32 | Output | Total transaction count (placeholder)"
  Actually: The cg wrapper forwards error_count/transaction_count from
            axi5_master_wr_mon, which drives them from the reporter's lifetime
            perf counters (w_perf_error_count / {16'h0, w_perf_completed_count}).
            The base-module page (axi5_master_wr_mon.md) documents the real
            semantics correctly.
  Impact:   A reader treats working telemetry as unimplemented.
```

```
[CONFIRMED] (minor) Protocol field written as 3'b000 in the addr-range encoding; the field is 4 bits
  File:     all four base docs (master_rd_mon, master_wr_mon, slave_rd_mon, slave_wr_mon),
            "Address-Range Checker" section
  Says:     "- `protocol`    = AXI (3'b000)"
  Actually: The format diagram on the same pages and the RTL comment in
            axi_monitor_addr_check ("protocol_type_t'(PROTOCOL_FIELD), // [108:105]
            protocol ... PROTOCOL_AXI = 4'h0") define a 4-bit field, value 4'h0.
  Impact:   Cosmetic width typo; value is right.
```

```
[CONFIRMED] (minor) Usage example uses undeclared signal power_cycles_saved
  File:     docs/markdown/RTLAmba/monitor/axi5_master_wr_mon_cg.md
  Says:     Example declares "logic [31:0] write_count, write_errors, write_timeouts;
             logic [63:0] total_write_latency;" then uses "power_cycles_saved <= '0;"
             and "power_cycles_saved <= power_cycles_saved + 1;" and reads it in the
             $display at the bottom.
  Actually: power_cycles_saved is never declared in the snippet; the example would
            not compile as written (implicit-wire tools would silently create a
            1-bit net, corrupting the power-savings math).
  Impact:   Copy-paste compile failure / silent 1-bit truncation.
```

```
[SUSPECTED] (minor gap) Timeout tick period is not derivable from the docs
  File:     all four base docs, cfg_timeout_cycles row
  Says:     "...measured in `cfg_freq_sel`-scaled timer ticks, not raw clock cycles"
  Actually: The wrappers hardwire cfg_freq_sel = 4'b0001 into axi_monitor_base. With
            the default counter_freq_invariant LUT (LINEAR, 5–220 MHz, 16 entries),
            index 1 = 5 + (220-5)*1/15 = 19, i.e. one timer tick = 19 aclk cycles.
            No page states this, so cfg_timeout_cycles cannot be converted to a time
            or even to clock cycles from the documentation. (The timer fires when
            the per-phase timer reaches cfg_cnt, i.e. roughly (cnt+1) ticks.)
  Impact:   Readers cannot size timeouts; the "frequency-invariant" property is
            also silently lost because freq_sel is fixed rather than set from the
            real clock frequency.
```

---

## POSSIBLE RTL BUGS

**Monitor wake sources missing from the clock-gating activity term (all three `axi5_*_mon_cg` wrappers).**
The inner `axi5_*_mon` is clocked by `gated_aclk`, but `user_valid`/`axi_valid` are built only from AXI valids plus the core's `busy`. The monitor's own state — reporter-FIFO backlog, a registered `monbus_valid`, an open perfmon window (`window_active`) — contributes nothing, and the monitor's `.busy()` output is unconnected in the wrappers. Consequences: (1) a packet queued in the reporter FIFO on an idle bus is not emitted until unrelated AXI traffic wakes the block (unbounded delay, though not loss); (2) an open measurement window freezes mid-window; (3) `cfg_window_force_close`/`cfg_end_trigger`/`cfg_start_trigger`, sampled on the gated clock, are silently ignored while gated. The docs explicitly claim the opposite ("monitor stays awake", "continues to track when gated"), so either the activity term should include monitor wake sources (e.g. reporter non-empty, `window_active`, `monbus_valid & ~monbus_ready`) or the documented behaviour should be downgraded. Note `axi_monitor_base.busy` itself is only `active_count > 0`, so even wiring monitor-busy in would not cover reporter backlog — a base-level fix would need to OR in FIFO/output state.

Not a bug but worth recording: the wrappers hardwire `cfg_freq_sel = 4'b0001`, so the frequency-invariant timer ticks every 19 clocks regardless of the actual clock frequency — the "frequency invariant" property is lost in every wrapper. Timeouts remain correct in tick units; this is a documentation/expectation gap more than a logic defect.

---

## Overall accuracy

The structural bulk of this part is in good shape: every parameter name and default (including the `ENABLE_*_LOGIC` cone set, `ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS/2` present on the base monitors and correctly absent from the `_cg` wrappers, and AGENT_ID 10/11/12/13), the full perfmon port lists, the 128-bit packet bit layout, the `block_ready`/saturation-recovery contract prose, the addr-range checker encoding (event code 0x0D, `{range_idx[3:0], addr[59:0]}`, `error_mask[13]` masking, per-range coalescing), the `cfg_timeout_cycles` saturation encoding, and the W-channel `data_id = AWID / data_resp = 2'b00` design note all match the RTL exactly. The defects cluster in five places: the master-read filtering section (inverted polarity, swapped/dead bit indices, a phantom Level-2 routing feature); the slave pages' event tables (wrong type numbers, fabricated payload layouts, and PERF events the hardware never emits); a family of detection claims (poison, tag mismatch, missing WLAST, ATOP/BTAGMATCH monitoring, alignment/strobe/handshake checks) with no implementing logic — the monitor only sees handshake-level taps; the clock-gating pages, whose "monitor keeps running / stays awake" claims are flatly contradicted by the gated-clock wiring and whose idle-count comments are off by 2x; and the `ENABLE_PERF_LOGIC` description, which misattributes the perfmon window/counters to a cone that actually only covers the legacy count-rollup packets. Add a handful of stale artefacts (64-bit monbus labels in four diagrams, "(placeholder)" status annotations, the wrap-vs-saturate counter claim) and the unsourced area/power percentages already flagged in the brief, and the part needs a focused repair pass on the filtering, event-table, and clock-gating sections before release — but the parameter/port reference material, which is what integrators will rely on most, is reliable.