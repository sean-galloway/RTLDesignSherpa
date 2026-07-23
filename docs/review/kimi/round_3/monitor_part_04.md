# Review: monitor_part_04 (AXIL4 monitor wrappers, `*_mon_cg` wrappers, monitor core, reporter cones)

I verified every parameter table, port list, and behavioral claim below against the supplied RTL. The four `*_mon_cg` pages dominate the findings: they describe a placeholder module that does not exist in the source tree, inverting the "known-weak" expectation (for these AXIL4 modules the RTL *does* contain real clock gating — the docs say it doesn't).

---

```
[CONFIRMED] The four *_mon_cg pages describe a nonexistent placeholder design; the RTL implements full clock gating
  File:     docs/markdown/RTLAmba/monitor/axil4_master_rd_mon_cg.md (identical text in
            axil4_master_wr_mon_cg.md, axil4_slave_rd_mon_cg.md, axil4_slave_wr_mon_cg.md)
  Says:     "**This wrapper does not currently gate any clock.** The RTL contains no
            `amba_clock_gate_ctrl` instance, no ICG cell, and no gated clock net; the base
            `axil4_master_rd_mon` inside it runs on the ungated `aclk`."
            Also: "Gate the monitor functionally, by ANDing the gating enable into the
            monitor enable: `cfg_monitor_enable & cfg_cg_enable`" and "Count idle cycles
            into `cg_cycles_saved` ... The RTL labels this block 'Clock Gating Statistics
            (Placeholder)'."
  Actually: Every one of these claims is false. Each of the four wrappers instantiates
            `amba_clock_gate_ctrl #(.CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH))
            i_amba_clock_gate_ctrl (...)`, which instantiates `clock_gate_ctrl`, which
            instantiates a real `icg u_icg` cell. The inner monitor is clocked by the
            gated clock: `.aclk (gated_aclk)`. There is no AND of cfg_cg_enable into
            cfg_monitor_enable (`.cfg_monitor_enable(cfg_monitor_enable)` is passed
            straight through; `cfg_cg_enable` feeds only the gate controller). There is
            no `cg_cycles_saved` signal and no "Clock Gating Statistics (Placeholder)"
            label anywhere in the RTL. The doc's "Consequence for integrators: ... will
            not reduce dynamic power" is therefore also wrong — the wrapper gates the
            clock of the entire inner transport+monitor.
            Note: this inverts the known-weak-area entry ("wrappers contain no clock-
            gating logic"). For these four AXIL4 modules the RTL has the gating; the
            doc is stale.
  Impact:   A reader concludes the module is a power-management no-op and avoids it (or
            needlessly swaps in the transport-level _cg modules), when in fact it performs
            real ICG-based gating of the whole monitor+transport.
```

```
[CONFIRMED] *_mon_cg pages document parameters/ports that do not exist, and the usage examples would not compile
  File:     docs/markdown/RTLAmba/monitor/axil4_master_rd_mon_cg.md (same in the other three _cg pages)
  Says:     Parameters "`ENABLE_CLOCK_GATING` (bit, 1)" and "`CG_IDLE_CYCLES` (int, 4)";
            ports "`cfg_cg_idle_threshold` (Input, 8)" and "`cg_cycles_saved` (Output, 32)";
            example: ".cfg_cg_idle_threshold(8'd4), .cg_cycles_saved(idle_cycle_est)".
            Also: "`cfg_cg_enable` ... Gates the monitor functionally ... 0 = monitor
            disabled" and "Drive `cfg_cg_enable = 1` for any test that expects monitor
            packets — with it low the monitor is off and no packets are emitted."
  Actually: The RTL's only clock-gating parameter is `parameter int CG_IDLE_COUNT_WIDTH
            = 4`; the ports are `cfg_cg_enable`, `cfg_cg_idle_count[CG_IDLE_COUNT_WIDTH-1:0]`,
            and status outputs `cg_gating` / `cg_idle`. `ENABLE_CLOCK_GATING`,
            `CG_IDLE_CYCLES`, `cfg_cg_idle_threshold`, and `cg_cycles_saved` do not exist,
            so the named-port example fails at elaboration. Semantics are inverted too:
            in `clock_gate_ctrl`, `w_gate_enable = cfg_cg_enable && !wakeup &&
            (r_idle_counter == 'h0)` — so cfg_cg_enable=0 means the clock is NEVER gated
            and the monitor runs exactly like the base module, packets included.
            The real ports (cg_gating, cg_idle, cfg_cg_idle_count) are documented nowhere.
  Impact:   Example code won't compile; verification guidance tells engineers to drive
            cfg_cg_enable high for any packet test when low is the fully-functional
            ungated mode; integrators can't discover the actual idle-count knob or the
            gating status outputs.
```

```
[CONFIRMED] "ENABLE_PERF_LOGIC=0 drops the perfmon window + counters" is wrong — they are always instantiated
  File:     docs/markdown/RTLAmba/monitor/axil4_master_rd_mon.md ("`ENABLE_PERF_LOGIC = 0`
            drops the whole block at synthesis" — same sentence in axil4_master_wr_mon.md,
            axil4_slave_rd_mon.md, axil4_slave_wr_mon.md; parameter table "Drop the
            perfmon window + counters"), and docs/markdown/RTLAmba/monitor/axi_monitor_base.md
            ("Drop the perfmon measurement window + counters"; "Setting it also defaults
            `ENABLE_PERF_LOGIC` on, instantiating the measurement window + counters")
  Says:     "`ENABLE_PERF_LOGIC` | bit | 1 | Drop the perfmon window + counters"
  Actually: In axi_monitor_base the window state machine (`r_win_state`, `r_window_cycles`)
            and the Stage-B counters (`r_prod_cycles` … `r_byte_count`, `r_burst_count`)
            are plain always_ff blocks with no generate gating — they synthesize
            unconditionally. ENABLE_PERF_LOGIC reaches only axi_monitor_reporter, where
            `if (ENABLE_PERF_LOGIC) begin : g_perf` instantiates axi_monitor_reporter_perf
            (the legacy count-rollup cone and the lifetime completed/error counters);
            the else branch ties `perf_completed_count_w`/`perf_error_count_w` to 0.
            With ENABLE_PERF_LOGIC=0, window_active and all seven perf counters still
            operate; only the reporter perf cone disappears.
  Impact:   A user setting ENABLE_PERF_LOGIC=0 to save the ~250 flops of window/counter
            state gets none of that area back, and sees live perfmon outputs the docs say
            cannot exist. (Conversely the docs' claim that error_count/transaction_count
            read 0 when ENABLE_PERF_LOGIC=0 IS correct.)
```

```
[CONFIRMED] "The counters advance only while cfg_perf_enable = 1" — counters are not gated by cfg_perf_enable
  File:     docs/markdown/RTLAmba/monitor/axil4_master_rd_mon.md (same sentence in
            axil4_master_wr_mon.md, axil4_slave_rd_mon.md, axil4_slave_wr_mon.md)
  Says:     "The counters advance only while `cfg_perf_enable = 1`"
  Actually: In axi_monitor_base the bucket/beat/byte/burst counters increment whenever
            `r_win_state == WIN_ACTIVE_S`. cfg_perf_enable is referenced only by the
            edge detector for window events 3'b010/3'b011 and by the reporter perf cone.
            A window opened by cfg_start_trigger (sel 000/100), first command handshake
            (sel 001), or first data beat (sel 011) accumulates counters with
            cfg_perf_enable tied low.
  Impact:   A user who leaves cfg_perf_enable=0 and opens a window via trigger or
            handshake gets counting the docs say is impossible; conversely one may
            wrongly believe perf_enable is a master counter gate.
```

```
[CONFIRMED] Measurement-window end-event table transposes the 3'b010 and 3'b011 encodings
  File:     docs/markdown/RTLAmba/monitor/axi_monitor_base.md
  Says:     "| `3'b010` | `cfg_perf_enable` rising edge | `window_cycles` saturation |
            | `3'b011` | first data handshake ... | `cfg_perf_enable` falling edge |"
  Actually: The RTL end-event mux is:
              3'b010:  w_end_event = w_perf_enable_falling;  // perf-enable edge
              3'b011:  w_end_event = w_window_saturate;      // counter saturate
            The module header (declared authoritative by the ISSUE #41 fix comment, which
            corrected exactly this transposition in the RTL) agrees: "3'b010 cfg_perf_enable
            edge (rising/falling); 3'b011 first productive beat (start) / counter
            saturate (end)". The doc's Start column is right; its End column for these
            two codes is swapped.
  Impact:   Software programming cfg_end_event_sel per the doc gets saturation instead of
            the perf-enable falling edge and vice versa — windows that never close, or
            close immediately.
```

```
[CONFIRMED] cfg_window_force_close misdescribed as "asynchronous" and as dropping perf totals
  File:     docs/markdown/RTLAmba/monitor/axi_monitor_filtered.md
  Says:     "`cfg_window_force_close` | Input | 1 | Asynchronous emergency close (drops
            any in-flight perf totals)."
  Actually: It is a synchronous input to the window FSM in axi_monitor_base:
            `if (w_end_event || cfg_window_force_close) r_win_state <= WIN_CLOSING_S;`
            inside `always_ff @(posedge aclk ...)`. Nothing is dropped — the counters
            hold through WIN_CLOSING/WIN_IDLE exactly as for a normal close (the ISSUE
            #41 fix explicitly made r_window_cycles hold too). The base page's own
            description ("Software override: force the window closed immediately
            regardless of the end-event selector") is correct; only the filtered page
            is wrong.
  Impact:   A reader expects asynchronous behavior and lost totals; neither is true.
```

```
[CONFIRMED] ADDR_BITS_IN_PKT documented as controlling packet address width; it is a dead parameter
  File:     docs/markdown/RTLAmba/monitor/axi_monitor_base.md
  Says:     "| `ADDR_BITS_IN_PKT` | int | 38 | Number of address LSBs carried in an
            error/event packet (clamped to `ADDR_WIDTH`) |"
  Actually: Neither ADDR_BITS_IN_PKT nor the derived `ADDR_BITS` is referenced anywhere
            in the axi_monitor_base body. Error/completion/timeout packets are built by
            the reporter cones with `pad_address(input logic [31:0] addr)` — a 32-bit
            value zero-extended to 64 — and axi_monitor_trans_mgr stores
            `next.addr = 32'(cmd_addr)`. The trans_mgr header spells it out: "the packet
            format intends to carry 38 address bits, but this table can only supply 32".
            So every error/event packet carries exactly 32 address bits regardless of
            this parameter. (The addr_check packet is the exception: it carries up to 60
            bits from its own latch, also independent of ADDR_BITS_IN_PKT.)
  Impact:   A user with ADDR_WIDTH=64 expects 38 address bits in error packets and gets
            32; the parameter can be tweaked with no effect.
```

```
[CONFIRMED] ENABLE_DEBUG_MODULE / DEBUG_FIFO_DEPTH / cfg_debug_level / cfg_debug_mask documented as functional; none do anything
  File:     docs/markdown/RTLAmba/monitor/axi_monitor_base.md ("`ENABLE_DEBUG_MODULE` ...
            Master switch for the debug-trace reporter sub-module"; "`DEBUG_FIFO_DEPTH` ...
            (used when the debug module is enabled)"; cfg_debug_level/cfg_debug_mask
            "(only used when `ENABLE_DEBUG_MODULE=1`)") and
            docs/markdown/RTLAmba/monitor/axi_monitor_filtered.md ("`ENABLE_DEBUG_MODULE`
            | bit | 0 | Instantiate the debug reporter sub-block.")
  Says:     "Master switch for the debug-trace reporter sub-module"
  Actually: In axi_monitor_base the only reference to ENABLE_DEBUG_MODULE is
            `if (!ENABLE_DEBUG_MODULE) begin : gen_no_debug ... assign w_debug_monbus_valid
            = 1'b0; ... end` — there is no debug sub-module and no else branch.
            DEBUG_FIFO_DEPTH, cfg_debug_level, and cfg_debug_mask are never referenced in
            the module body. The actual debug emitter (axi_monitor_reporter_debug) lives
            in axi_monitor_reporter and is gated by ENABLE_DEBUG_LOGIC, not
            ENABLE_DEBUG_MODULE; it has no FIFO and no level/mask inputs.
  Impact:   A user sets ENABLE_DEBUG_MODULE=1 expecting a debug stream (and wires up
            cfg_debug_level/mask); nothing happens — and see RTL bug A below.
```

```
[CONFIRMED] axil4_master_wr_mon page says "Filtering masks (7 masks)"; the module has nine
  File:     docs/markdown/RTLAmba/monitor/axil4_master_wr_mon.md
  Says:     "- Filtering masks (7 masks)"
 