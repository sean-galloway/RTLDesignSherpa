# Review: monitor_part_02 (8 pages, 8 modules)

I checked every parameter table, port list, mask encoding, status-output description, and the backpressure/perfmon/addr-range narratives in these eight pages against the RTL. The four base pages (`axi4_master_rd_mon`, `axi4_master_wr_mon`, `axi4_slave_rd_mon`, `axi4_slave_wr_mon`) are largely accurate — every parameter default, all nine filter masks, the `w_timeout_cnt` encoding, the `cfg_conflict_error` equation, the saturation-recovery arithmetic, the packet bit layout, and the strategy mask hex values (`16'hFFF6`, `16'hFFEE`, `16'hFFF4`) all verified clean. The clock-gated pages contain nearly all of the defects.

---

## Findings

```
[CONFIRMED] AXI4 *_mon_cg pages document clock-gating parameters that do not exist; the Quick Usage example will not elaborate
  File:     docs/markdown/RTLAmba/axi4/axi4_master_wr_mon_cg.md
            (identical boilerplate in axi4_slave_rd_mon_cg.md, axi4_slave_wr_mon_cg.md)
  Says:     "| `ENABLE_CLOCK_GATING` | 1 | Master enable (0=disable, identical to base) |
             | `CG_IDLE_CYCLES` | 8 | Cycles before clock gating activates |
             | `CG_GATE_*` | 1 | Domain-specific gating enables |"
            and in Quick Usage: ".ENABLE_CLOCK_GATING(1), .CG_IDLE_CYCLES(8)"
  Actually: axi4_master_wr_mon_cg.sv has no ENABLE_CLOCK_GATING, CG_IDLE_CYCLES, or CG_GATE_*
            parameters. The only CG parameter is `parameter int CG_IDLE_COUNT_WIDTH = 4`, and
            gating is controlled at runtime by the ports `cfg_cg_enable` and
            `cfg_cg_idle_count` (inputs to amba_clock_gate_ctrl). There is a single gating
            domain (one controller gates the whole inner monitor), so "domain-specific gating
            enables" has no counterpart. None of cfg_cg_enable, cfg_cg_idle_count, or
            CG_IDLE_COUNT_WIDTH is documented anywhere on these three pages, and the
            cg_gating/cg_idle status outputs are undocumented too.
  Impact:   Parameter overrides of nonexistent parameters are an elaboration error, so the
            Quick Usage example fails to compile as written; and a reader has no way to learn
            the real CG controls from the page (leaving cfg_cg_enable unconnected floats it).
            The "Zero Overhead When Disabled: ENABLE_CLOCK_GATING=0" bullet leans on the same
            nonexistent parameter (the real disable, cfg_cg_enable=0, is functional
            transparency, not zero area — the gate controller still synthesizes).
```

```
[CONFIRMED] "while a measurement window is open the monitor stays awake" is not implemented — window_active has no path into the wake logic
  File:     docs/markdown/RTLAmba/axi4/axi4_master_wr_mon_cg.md
            (same sentence in axi4_slave_rd_mon_cg.md, axi4_slave_wr_mon_cg.md;
             axi5_master_rd_mon_cg.md says "...regardless of the idle-count setting")
  Says:     "Clock gating never suppresses these paths: while a measurement window is open
             the monitor stays awake, so window cycle accounting remains exact regardless of
             `CG_IDLE_CYCLES`."
  Actually: The wake terms are fixed valids + core busy, e.g. axi4_master_wr_mon_cg.sv:
             assign user_valid = fub_axi_awvalid || fub_axi_wvalid || fub_axi_bvalid || int_busy;
             assign axi_valid  = m_axi_awvalid || m_axi_wvalid || m_axi_bvalid;
            int_busy comes only from the core's skid-buffer busy (the monitor's own busy pin
            is left unconnected inside the *_mon wrappers). window_active is not an input to
            i_amba_clock_gate_ctrl in any of the four CG modules. With an open window and an
            idle bus, the clock gates after cfg_cg_idle_count+1 cycles and window_cycles and
            all bucket counters (clocked by gated_aclk) freeze until the next wake.
  Impact:   A reader expecting an open perfmon window to pin the block awake, or window_cycles
            to measure wall-clock time across idle gaps, gets neither — window_cycles counts
            gated-clock cycles only and undercounts elapsed time whenever the bus idles.
```

```
[CONFIRMED] axi5 CG page labels error_count/transaction_count "(placeholder)" — they are functional reporter counters
  File:     docs/markdown/RTLAmba/axi5/axi5_master_rd_mon_cg.md
  Says:     "| error_count | 16 | Output | Cumulative error count (placeholder) |
             | transaction_count | 32 | Output | Total transaction count (placeholder) |"
  Actually: axi5_master_rd_mon.sv: assign error_count = w_perf_error_count;
             assign transaction_count = {16'h0, w_perf_completed_count};
            These are the lifetime reporter perf counters (error+timeout packets emitted /
            completion packets emitted; 0 only when ENABLE_PERF_LOGIC=0 or USE_MONITOR=0).
            The AXI4 monitor pages in this same part describe the identical outputs correctly
            as real counters.
  Impact:   A reader believes these status outputs are unimplemented stubs and ignores
            working counters. Looks like stale text from before the counters were wired up.
```

```
[CONFIRMED] wr/slave base pages claim cfg_active_trans_threshold is "fixed" at 8 inside the wrapper; it is driven by the top-level ACTIVE_TRANS_THRESHOLD parameter the same pages document
  File:     docs/markdown/RTLAmba/axi4/axi4_master_wr_mon.md
            (same note in axi4_slave_rd_mon.md, axi4_slave_wr_mon.md)
  Says:     "The inner monitor's `cfg_debug_level` (tied to 0), `cfg_debug_mask` (0) and
             `cfg_active_trans_threshold` (8) are fixed inside the wrapper and are **not**
             top-level ports on this module."
  Actually: axi4_master_wr_mon.sv: .cfg_active_trans_threshold(16'(ACTIVE_TRANS_THRESHOLD))
            with `parameter int ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2` — a top-level
            parameter that the same page's Monitor Parameters table lists as tunable.
            axi4_master_rd_mon.md states it correctly: "cfg_active_trans_threshold is driven
            from the ACTIVE_TRANS_THRESHOLD parameter (default MAX_TRANSACTIONS/2)".
  Impact:   Internal contradiction (parameter table says tunable, note says fixed 8). A user
            who wants a different threshold trip point is told it is hardwired when it is not.
```

```
[CONFIRMED] "In addition to all axi4_master_wr_mon parameters" is false — the CG wrappers do not expose ACTIVE_TRANS_THRESHOLD
  File:     docs/markdown/RTLAmba/axi4/axi4_master_wr_mon_cg.md
            (same claim in axi4_slave_rd_mon_cg.md, axi4_slave_wr_mon_cg.md)
  Says:     "In addition to all [axi4_master_wr_mon](./axi4_master_wr_mon.md) parameters
             (including `USE_MONITOR`):"
  Actually: The CG wrapper parameter lists contain no ACTIVE_TRANS_THRESHOLD, and the inner
            axi4_master_wr_mon instance is built without the override, so it silently takes
            the inner default MAX_TRANSACTIONS/2. Overriding .ACTIVE_TRANS_THRESHOLD(...) on
            the CG module is an elaboration error.
  Impact:   Minor but concrete: one documented base parameter is not reachable through the
            CG variant despite the blanket claim. (The axi5 CG page avoids this by listing
            parameters explicitly.)
```

```
[CONFIRMED] axi5 CG page code snippet puts fub_axi_rready in the activity term; the RTL uses fub_axi_rvalid and explicitly forbids peer READYs
  File:     docs/markdown/RTLAmba/axi5/axi5_master_rd_mon_cg.md
  Says:     "user_valid = fub_axi_arvalid || fub_axi_rready || int_busy;"
  Actually: axi5_master_rd_mon_cg.sv: assign user_valid = fub_axi_arvalid || fub_axi_rvalid || int_busy;
            and the RTL header comment states: "A peer's READY must never appear in the
            activity term: a consumer that parks its response-ready high while idle ...
            would pin this block permanently awake and defeat gating entirely."
  Impact:   Documents the wrong wake condition — precisely the anti-pattern the RTL comment
            warns against. A reader modeling wake behavior (or writing assertions) from the
            doc gets it backwards.
```

```
[CONFIRMED] "MonBus packets flushed before clock stops" is not guaranteed — monitor-bus occupancy is not part of the wake/gate logic
  File:     docs/markdown/RTLAmba/axi5/axi5_master_rd_mon_cg.md
  Says:     "Monitor packets generated before gating: Monitor processes all events before
             idle state; MonBus packets flushed before clock stops; No events lost during
             gating transition."
  Actually: monbus_valid / reporter FIFO occupancy has no connection to the wake terms
            (user_valid/axi_valid above) or to amba_clock_gate_ctrl. Nothing delays gating
            for monitor-bus drain. With monbus_ready low (stalled consumer) and an idle bus,
            the clock gates with packets undelivered in the reporter FIFO/output register.
            They are held, not lost, and drain on the next wake — so "No events lost" holds
            but "flushed before clock stops" does not.
  Impact:   Overclaim. With a stalled monbus consumer and no new AXI traffic, the final
            packets sit undelivered indefinitely; a power integrator reading this page would
            not expect that.
```

```
[CONFIRMED] axi5 CG usage example mislabels cfg_monitor_enable as "// Completions" and never connects cfg_compl_enable
  File:     docs/markdown/RTLAmba/axi5/axi5_master_rd_mon_cg.md
  Says:     ".cfg_monitor_enable (1'b1),        // Completions"
            (the "FUNCTIONAL DEBUG MODE" example then sets pkt_mask 16'hFFF4 to pass COMPL
             and compl_mask 16'h0000, but never drives cfg_compl_enable)
  Actually: cfg_monitor_enable is the master runtime gate (RTL: "Enable monitoring"; the
            clear input is `cam_clear | ~cfg_monitor_enable`). Completion packets are gated
            by cfg_compl_enable (axi_monitor_reporter_compl and the w_auto_retire logic),
            which the example leaves unconnected — a floating input, X in simulation.
  Impact:   The example's comments promise completion visibility that the code does not
            enable; copied into a testbench, completion behavior is indeterminate.
```

```
[SUSPECTED] Unsourced power-savings figures presented as fact on all four CG pages
  File:     docs/markdown/RTLAmba/axi4/axi4_master_wr_mon_cg.md,
            axi4_slave_rd_mon_cg.md, axi4_slave_wr_mon_cg.md,
            axi5_master_rd_mon_cg.md
  Says:     "Power Savings: 25-70% depending on traffic utilization" (AXI4 CG pages);
            "Clock gating saves ~80-90% when idle ... Net savings: 70-80% during idle
             periods", "Monitor adds ~10% dynamic power when active", "monitor + CG adds
             ~10% area" (axi5 page).
  Actually: No synthesis, simulation, or power data anywhere in the provided material
            supports these numbers; the RTL has no power instrumentation. SUSPECTED rather
            than CONFIRMED only because I cannot prove the numbers false — but they are
            unverifiable claims stated as measured fact.
  Impact:   Readers may quote invented-feeling figures in design reviews; the author should
            either source them or label them as targets/estimates.
```

```
[CONFIRMED] Minor: addr-range section writes the protocol field as 3'b000; the field is 4 bits
  File:     docs/markdown/RTLAmba/axi4/axi4_master_rd_mon.md,
            axi4_master_wr_mon.md, axi4_slave_rd_mon.md, axi4_slave_wr_mon.md
  Says:     "protocol    = AXI (3'b000)" (Address-Range Checker section)
  Actually: The same pages' Monitor Packet Format block says "Bits [108:105] - Protocol
             (4 bits): 0x0=AXI", and the RTL uses a 4-bit PROTOCOL_AXI field.
  Impact:   Trivial (value 0 either way), but a page-internal contradiction that could
            momentarily confuse someone writing a packet decoder.
```

---

## POSSIBLE RTL BUGS

**CG wrappers can strand undelivered monitor packets until unrelated traffic wakes the block.** In all four CG modules here (`axi4_master_wr_mon_cg`, `axi4_slave_rd_mon_cg`, `axi4_slave_wr_mon_cg`, `axi5_master_rd_mon_cg`), the wake terms are only AXI valids plus the core skid-buffer busy; neither `monbus_valid` nor reporter FIFO occupancy nor the monitor's own `busy`/`active_count` participates in gating. Two consequences: (a) with a stalled monbus consumer the clock gates with packets pending, and they can only be delivered after unrelated AXI activity — unbounded latency, no loss; (b) an open perfmon window (and the timeout detector) freezes while gated. Both are pause-not-lose behaviors, so they are design gaps rather than functional bugs, but they directly contradict what these doc pages claim ("monitor stays awake", "packets flushed before clock stops") — either the RTL should OR monitor-side activity into `user_valid`, or the docs should stop claiming it does. The doc-side findings above cover the documentation half; flagging the RTL half here as requested.

---

## Overall accuracy

The four base AXI4 monitor pages are in good shape: I re-verified every parameter default (including `AGENT_ID` 16'h000A/000B/0014/0015, `ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS/2`, the six `ENABLE_*_LOGIC` defaults), the `w_timeout_cnt` encoding (0→15, 1–15 literal, >15 saturates), the `block_ready` gating equation and the saturation-recovery arithmetic (cap = MAX − reserve, reopen at MAX − (reserve−1), strictly above the cap — matches `BLOCK_MARGIN = CMD_ENTRY_RESERVE − 1`), the perfmon window/bucket/byte-count semantics against `axi_monitor_base`, the addr-range event encoding (`8'h0D`, `error_mask[13]` via `ec_idx = event_code[3:0]`), the 128-bit packet layout against `create_monitor_packet` usage, the "1 packet per 2 cycles" bandwidth figure (reporter output register cannot reload on the accept cycle), and the strategy mask hex values bit by bit. Apart from the stale `cfg_active_trans_threshold (8)` note on three of them, they check out.

The clock-gated pages are the weak area of this part: they document three CG parameters that do not exist while omitting the two CG ports and one CG parameter that do, their usage example would not elaborate, the "stays awake during an open window" and "flushed before clock stops" claims are contradicted by the RTL's wake terms, and the axi5 CG page additionally carries a wrong activity-term snippet, two functional counters mislabeled "(placeholder)", and a mislabeled enable comment. Note also that the known-weak issue from previous rounds — `*_mon_cg` wrappers with no clock-gating logic — does **not** apply to the four CG modules reviewed here; all four contain a real `amba_clock_gate_ctrl` instance, masked readys, and a gated clock.