# Review: monitor_part_01 (11 docs, 10 modules + dependencies)

I checked every enum table, parameter table, port list, packet-layout claim, and code example against `RTL.sv`. The four package-reference pages are nearly perfect; several module pages are not. Findings ranked by severity.

---

```
[CONFIRMED] Documented clock-gating parameters, gating domains, and status
signals of axi4_master_rd_mon_cg do not exist; all three usage examples
fail to compile
  File:     docs/markdown/RTLAmba/axi4/axi4_master_rd_mon_cg.md
  Says:     "| `ENABLE_CLOCK_GATING` | bit | 1 | Master enable for clock gating |
             `CG_IDLE_CYCLES` | int | 8 | ... | `CG_GATE_MONITOR` ... `CG_GATE_REPORTER`
             ... `CG_GATE_TIMERS`" and three examples instantiating e.g.
             ".ENABLE_CLOCK_GATING(1), .CG_IDLE_CYCLES(4), .CG_GATE_MONITOR(1)"
  Actually: rtl/amba/axi4/axi4_master_rd_mon_cg.sv has none of these five
            parameters. The only CG parameter is `parameter int
            CG_IDLE_COUNT_WIDTH = 4`. Gating is controlled at runtime by PORTS
            `cfg_cg_enable` and `cfg_cg_idle_count` (4 bits), which the page
            never documents. Named-parameter overrides of nonexistent
            parameters are elaboration errors, so every example on the page
            fails to compile. The claimed "independent gating domains"
            (Monitor/Reporter/Timer) also do not exist — a single
            amba_clock_gate_ctrl gates the whole inner module's clock
            (gated_aclk feeds all of axi4_master_rd_mon). The "Power
            Monitoring Signals" `cg_monitor_gated` / `cg_reporter_gated` /
            `cg_timers_gated` do not exist; the actual outputs are
            `cg_gating` and `cg_idle`. Finally, the latency table lists
            `CG_IDLE_CYCLES=16`, which cannot fit the 4-bit cfg_cg_idle_count.
  Impact:   Copy-paste instantiations are dead on arrival; the real runtime
            controls (cfg_cg_enable / cfg_cg_idle_count) are undiscoverable
            from this page.
```

```
[CONFIRMED] arbiter_monbus_common described as monitor-stream arbitration
infrastructure; the RTL monitors ONE arbiter
  File:     docs/markdown/RTLAmba/monitor/arbiter_monbus_common.md
  Says:     "provides Base infrastructure for monitor bus arbitration";
            Key Features: "Shared arbitration logic for multiple monitor
            sources", "Packet multiplexing with source identification";
            Module Purpose: "Source Multiplexing: Combines multiple monitor
            streams"; mermaid shows mon_valid[0..N]/mon_data[0..N] feeding
            "Arbiter Logic" -> "agg_valid/data"
  Actually: rtl/amba/monitor/arbiter_monbus_common.sv has no monitor-stream
            inputs at all. Its inputs are a single arbiter's snoop signals
            (cfg_max_thresh, request, grant_valid, grant, grant_id, grant_ack,
            block_arb) plus cfg_mon_* config; it emits one monbus stream of
            PROTOCOL_ARB event packets (starvation, ACK timeout, fairness,
            efficiency, completion, grant-perf). There is no N-input mux,
            no round-robin over monitor sources, no source-ID tagging.
  Impact:   A reader looking for the component that arbitrates multiple
            monitor streams (that is monbus_arbiter, a different module) is
            sent to the wrong module with a wrong mental model of the
            architecture.
```

```
[CONFIRMED] Wrong hex value for APB_ERR_ADDR_RANGE in the payload table
  File:     docs/markdown/RTLAmba/includes/monitor_package_spec.md
  Says:     "| `apb_monitor_addr_check` | Error | `APB_ERR_ADDR_RANGE` (8'h0D)
             | `[63:60]` = range_index (4b), `[59]` = is_read, `[58:0]` = address |"
  Actually: rtl/amba/includes/monitor_amba4_pkg.sv: `APB_ERR_ADDR_RANGE = 8'h8`
            (8'hD is APB_ERR_RESERVED_D). rtl/amba/monitor/apb_monitor_addr_check.sv
            confirms with `EVENT_CODE = APB_ERR_ADDR_RANGE; // 8'h08`, and both
            monitor_amba4_pkg.md and apb5_monitor.md correctly say 0x08.
            8'h0D is the AXI value (AXI_ERR_ADDR_RANGE), correctly given in the
            row above.
  Impact:   A consumer decoding APB range-violation packets by this table
            matches the wrong code and never fires.
```

```
[CONFIRMED] WRR arbitration algorithm misdescribed (and self-contradictory)
  File:     docs/markdown/RTLAmba/monitor/arbiter_wrr_pwm_monbus.md
  Says:     "Arbitration Algorithm: 1. Identify all active requests 2. Select
             highest weight among active requests 3. Round-robin among clients
             with that weight 4. Issue grant and update rotation pointer" —
             while also claiming "lower-weight clients still receive guaranteed
             service, preventing starvation"
  Actually: rtl/common/arbiter_round_robin_weighted.sv is credit-based: each
            client is loaded with `weight` credits (r_credit_counter), plain
            round-robin runs among clients with credits > 0
            (w_has_crd / w_requesting_eligible), a completed grant decrements
            the winner's credit, and a global replenish reloads all credits
            when no requester has any left (w_global_replenish). There is no
            "select highest weight" stage; under continuous all-client
            requests the doc's algorithm grants client 0 forever (strict
            priority), which directly contradicts the page's own starvation
            guarantee.
  Impact:   A reader predicts grant patterns (and starvation behavior) that
            the hardware does not produce.
```

```
[CONFIRMED] Claim that clock gating never disturbs perf-window accounting is
not supported by the activity logic
  File:     docs/markdown/RTLAmba/axi4/axi4_master_rd_mon_cg.md
  Says:     "Clock gating never suppresses these paths: while a measurement
             window is open the monitor stays awake, so window cycle accounting
             remains exact regardless of CG_IDLE_CYCLES."
  Actually: In axi4_master_rd_mon_cg.sv the activity terms are
            `user_valid = fub_axi_arvalid || fub_axi_rvalid || int_busy` and
            `axi_valid = m_axi_arvalid || m_axi_rvalid`; int_busy (from
            axi4_master_rd) is skid counts plus those same valids.
            window_active is not an activity term. An open measurement window
            over an idle bus lets the clock gate after cfg_cg_idle_count, and
            window_cycles / perf_*_cycles (counted inside axi_monitor_base on
            the gated clock) freeze until traffic resumes.
  Impact:   Windowed utilization measurements with gating enabled silently
            measure awake-time, not wall-time — the opposite of the documented
            guarantee.
```

```
[CONFIRMED] apb_monitor.md documents throughput events and config inputs that
the RTL never uses
  File:     docs/markdown/RTLAmba/apb/apb_monitor.md
  Says:     "Performance Events (when cfg_perf_enable = 1): Latency threshold
             violations, Throughput degradation, Transaction statistics";
             ports "cfg_throughput_enable — Enable throughput tracking",
             "cfg_throughput_threshold — Throughput threshold for alerts";
             also "cfg_debug_level — Debug verbosity level (0-15)"
  Actually: In rtl/amba/apb/apb_monitor.sv, cfg_throughput_enable,
            cfg_throughput_threshold and cfg_debug_level appear only in the
            port list. r_throughput_counter / r_throughput_timer are
            maintained but never read by any event path; the only perf event
            is the latency-threshold one (cfg_perf_enable && cfg_latency_enable
            && latency > cfg_latency_threshold). No throughput packet can ever
            be emitted. (Contrast with apb5_monitor.md, which honestly marks
            its unimplemented user-signal feature "Not Implemented".)
  Impact:   Enabling "throughput tracking" per the doc produces zero packets;
            dead configuration inputs presented as functional.
```

```
[CONFIRMED] apb_monitor.md module declaration and parameter/port tables are
stale: N_ADDR_RANGES and the entire address-checker port group are missing
  File:     docs/markdown/RTLAmba/apb/apb_monitor.md
  Says:     The "Module Declaration" block lists neither `USE_MONITOR` nor
            `N_ADDR_RANGES`, and no cfg_addr_check_enable / cfg_addr_range_enable
            / cfg_addr_range_low / cfg_addr_range_high ports; the Parameters
            table includes USE_MONITOR but not N_ADDR_RANGES; the block also
            shows `import monitor_pkg::*;`
  Actually: rtl/amba/apb/apb_monitor.sv has `parameter bit USE_MONITOR =
            1'b1, parameter int N_ADDR_RANGES = 0` and the four addr-checker
            config ports, instantiates apb_monitor_addr_check when
            N_ADDR_RANGES > 0, and imports monitor_common_pkg +
            monitor_amba4_pkg (with an explicit note that monitor_pkg is
            intentionally not imported). The sibling apb5_monitor.md documents
            all of this correctly.
  Impact:   The address-range checker is undiscoverable from this page, and
            the quoted declaration does not match the module.
```

```
[CONFIRMED] apb_monitor.md usage example: 64-bit FIFO for a 128-bit packet,
timestamp and i_mon_time never connected
  File:     docs/markdown/RTLAmba/apb/apb_monitor.md
  Says:     "gaxi_fifo_sync #(.DATA_WIDTH(64), .DEPTH(128)) u_mon_fifo (...
             .wr_data(mon_packet) ...)" and the apb_monitor instantiation
             connects neither i_mon_time nor monbus_timestamp (nor
             cfg_latency_enable / cfg_throughput_enable / cfg_trans_debug_enable
             / cfg_debug_level / cfg_latency_threshold / cfg_throughput_threshold).
  Actually: mon_packet is the 128-bit monitor_packet_t; gaxi_fifo_sync's
            wr_data is [DATA_WIDTH-1:0], so the example silently truncates the
            upper 64 bits — packet_type, protocol, event_code, channel_id,
            agent_id and unit_id are all discarded, keeping only event_data.
            Leaving input i_mon_time unconnected also makes monbus_timestamp X
            in simulation (FIFO events sample it at emission:
            `w_monbus_pkt_ts = i_mon_time`).
  Impact:   A copy-pasted integration stores header-less 64-bit fragments and
            gets X timestamps; exactly the class of defect the reader cannot
            debug from the docs.
```

```
[CONFIRMED] i_mon_time input and monbus_timestamp output missing from both
PWM-arbiter pages (tables and examples)
  File:     docs/markdown/RTLAmba/monitor/arbiter_rr_pwm_monbus.md and
            docs/markdown/RTLAmba/monitor/arbiter_wrr_pwm_monbus.md
  Says:     "Monitor Bus Output" tables list only monbus_valid / monbus_ready /
            monbus_packet; both usage examples instantiate exactly those three.
  Actually: rtl/amba/monitor/arbiter_rr_pwm_monbus.sv and
            arbiter_wrr_pwm_monbus.sv both have
            `input monitor_common_pkg::monbus_timestamp_t i_mon_time` and
            `output monitor_common_pkg::monbus_timestamp_t monbus_timestamp`
            (passed through to arbiter_monbus_common, which drives
            `monbus_timestamp = i_mon_time`).
  Impact:   Example-based instantiations leave i_mon_time floating → emitted
            timestamps are X; the side-band timestamp the whole subsystem is
            built around is invisible on these pages.
```

```
[CONFIRMED] "Every enum"/"one per enum" claims for the AMBA4 union and helpers
are too broad; perfhist enum is 4 bits, not 8
  File:     docs/markdown/RTLAmba/includes/monitor_amba4_pkg.md
  Says:     "a `unified_event_code_t` packed union that overlays every enum in
             this document ... Helper functions `create_axi_*_event` ... (one
             per enum)"; intro: "Each enum is 8 bits wide."
  Actually: The page names axi_perfwin_code_t and axi_perfhist_select_t as
            AXI categories, but rtl/amba/includes/monitor_amba4_pkg.sv puts
            neither in unified_event_code_t (19 members + raw) and exports no
            create_axi_perfwin_event / create_axi_perfhist_event. Also
            `axi_perfhist_select_t` is `typedef enum logic [3:0]` — a 4-bit
            select nibble, contradicting "each enum is 8 bits wide".
  Impact:   Minor. Users of the windowed categories find no helper and no
            union member; the width blanket statement is wrong for one enum.
```

```
[SUSPECTED] Fairness deviation described as measured "over the 256-cycle
window"; RTL accumulates grant counts for the lifetime of the monitor
  File:     docs/markdown/RTLAmba/monitor/arbiter_rr_pwm_monbus.md (and the
            WRR page's fairness example)
  Says:     "Actual distribution measured over 256-cycle window."
  Actually: In arbiter_monbus_common.sv, r_fairness_timer paces re-evaluation
            every FAIRNESS_REPORT_CYCLES, but the percentages are computed from
            r_grant_counters[] / r_total_grants, which are never reset except
            at rst_n. The 256-cycle figure is a reporting cadence, not a
            measurement window. I could not find a windowed counter anywhere
            in the module.
  Impact:   Minor; deviation converges to a lifetime average rather than
            reacting per window, which matters for how readers set
            cfg_mon_fairness(_thresh).
```

```
[SUSPECTED] Stale 3-bit protocol notation
  File:     docs/markdown/RTLAmba/monitor/arbiter_rr_pwm_monbus.md
  Says:     "Uses PROTOCOL_ARB (3'b011) event encoding"
  Actually: The protocol field is 4 bits (PROTOCOL_ARB = 4'h3 per
            monitor_package_spec.md and the 128-bit packing in
            arbiter_monbus_common.sv itself). Numerically harmless but stale.
```

Small items I noted but did not elevate: "Fixed 16-entry FIFO prevents event loss" (arbiter_rr_pwm_monbus.md) — a full FIFO drops events (`w_fifo_wr_valid` asserts regardless of `w_fifo_wr_ready`); the power-savings percentage table in the cg page is unsourced (same class as the already-known unsourced timing tables); `MAX_LEVELS` of arbiter_monbus_common is a real overridable parameter (the WRR wrapper sets it) although the page calls the weight widths "derived localparams"; the reporter "full 64-bit address" in monitor_package_spec.md is really a zero-extended 32-bit address (`pad_address(trans_table[w_sel].addr)`).

---

## POSSIBLE RTL BUGS

1. **`apb_monitor`: `r_error_count` has no reset.** In the transaction-lifecycle `ALWAYS_FF_RST`, the reset branch clears `r_active_count`, `r_transaction_count`, `r_cmd_start_time` but not `r_error_count`. `apb5_monitor.sv` contains the fix with the telltale comment `r_error_count <= '0; // was omitted: r_error_count had no reset` — the base module never received it. `error_count` is X after reset in simulation.

2. **`apb_monitor`: no edge qualification on level-sensitive events.** `w_cmd_timeout`, `w_rsp_timeout`, `w_protocol_violation`, and `w_latency_threshold_exceeded` are levels fed straight into `w_fifo_wr_valid`, so a held condition writes a packet every cycle until the FIFO fills — precisely the failure apb5_monitor fixed and documented ("one stuck command emitted an identical timeout packet on every cycle … 29 packets over a 40-cycle stall"). The base APB monitor still has the flooding behavior.

3. **`apb_monitor`: FIFO-full drops pulsed events and leaks the transaction slot.** Completion and SLVERR events are single-cycle pulses gated only by `w_fifo_wr_ready` for marking (`event_reported` sets only when the write is accepted). If the FIFO is full on that cycle, the packet is lost forever *and* the entry is never marked `event_reported`, so `w_completed_trans` never fires and the slot (plus `active_count`) leaks. This contradicts apb_monitor.md's "FIFO full condition prevents packet loss". The AXI reporter family added auto-retire logic for exactly this failure mode; the APB monitor has none.

4. **`arbiter_monbus_common`: protocol-violation reporting is dead logic.** `r_protocol_violation_count` is declared and drives `debug_protocol_violations` but is never assigned or reset anywhere → that output is permanently X/0. Further, `r_protocol_violation_event` is registered but never enters `w_event_valid` or the packet priority encoder, so ARB protocol violations (multiple grants, spurious ACK, grant-without-request) are detected and then dropped — `ARB_ERR_PROTOCOL_VIOLATION`, `ARB_ERR_CONCURRENT_GRANTS`, `ARB_ERR_ORPHAN_ACK` are unreachable from this module.

5. Minor: `apb_monitor` uses `r_trans_table[...].addr <= {{(64-AW){1'b0}}, cmd_paddr};` (64-bit literal into the 32-bit field; negative replication count for AW > 64). apb5_monitor fixed this with `32'(cmd_paddr)`; the base module keeps the fragile form. Also, the header comment block of `arbiter_monbus_common.sv` still describes the retired 64-bit packet layout ("Protocol field INCREASED to 3 bits [59:57]…"), which will mislead anyone reading the RTL — worth refreshing alongside the doc fixes.

---

## Overall accuracy

The reference half of this part is in good shape: every enum value in `monitor_amba4_pkg.md`, `monitor_amba5_pkg.md`, and `monitor_arbiter_pkg.md` matches the RTL exactly, including the honest note that CORE constructors are not exported; `monitor_package_spec.md`'s 128-bit field map, helper signatures, and payload conventions all verified against the packing in `arbiter_monbus_common.sv` and the addr_check modules, with the single exception of the `8'h0D`/`8'h08` slip for `APB_ERR_ADDR_RANGE`. Among module pages, `apb5_monitor.md` and `apb_monitor_addr_check.md` are exemplary — the "Not Implemented" user-signal disclosure, the edge-detection narrative, the priority order, and the packet layouts all match the RTL line for line. The problems cluster elsewhere: `axi4_master_rd_mon_cg.md` fabricates its entire clock-gating parameter set and gating domains (the actual single-domain, port-controlled gate is real but undocumented), `arbiter_monbus_common.md` describes a different module than the one that exists, `apb_monitor.md` is a pre-addr-checker revision with dead throughput claims and a broken FIFO example, and both PWM-arbiter pages omit the timestamp pair. The RTL bugs surfaced (unreset `r_error_count`, un-edge-qualified and unthrottled APB events, the dead protocol-violation path in `arbiter_monbus_common`) are worth tracking independently of the documentation fixes.