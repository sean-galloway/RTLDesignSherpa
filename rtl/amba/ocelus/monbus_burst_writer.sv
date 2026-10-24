// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: monbus_burst_writer
// Purpose: Continuous, FSM-free AXI4-shaped burst writer over a beat FIFO.
//
//   Drains a 64-bit beat-granular FIFO into an address window
//   [cfg_base_addr, cfg_limit_addr] as AXI4 INCR bursts: watermark /
//   timeout flush triggers, whole-record epochs (beats_per_unit = 3 for
//   raw records, 1 for compressed slots), 4 KB boundary and window-wrap
//   geometry, up to WR_OS_CAP outstanding sub-bursts with in-order B
//   credit return.
//
//   This is the writer section of monbus_group_core (amba BUG-039
//   redesign) lifted out verbatim so monbus_group_core_1wr can run one
//   writer per source behind a single write port. monbus_group_core keeps
//   its own inline copy (timing-closed, formally proven); the two are
//   meant to stay textually identical below the port list.
//
//   The FIFO read side is a plain valid/ready pop plus the live beat count
//   (the writer registers the count itself: triggers and the AW cap read
//   the one-flop-lagged copy, see the section header below).
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_burst_writer #(
    parameter int ADDR_WIDTH            = 32,
    parameter int AXI_ID_WIDTH_M        = 1,       // master-write id (1 in AXIL builds)
    parameter int MAX_BURST_BEATS       = 1,       // max beats per AW (AXIL: 1, AXI4: up to 256)
    parameter int FLUSH_TIMEOUT_CYCLES  = 1024     // cycles since last W to force a flush
) (
    input  logic                          axi_aclk,
    input  logic                          axi_aresetn,

    // ------------------------------------------------------------------
    // Beat FIFO read side (one entry = one 64-bit beat)
    // ------------------------------------------------------------------
    input  logic                          fifo_rd_valid,
    output logic                          fifo_rd_ready,
    input  logic [63:0]                   fifo_rd_data,
    input  logic [15:0]                   fifo_beat_count,  // live occupancy, beats

    // Record geometry: 3 (raw {ts, pkt_hi, pkt_lo} records) or 1
    // (self-tagged compressed slots). Hold stable while beats are queued.
    input  logic [15:0]                   beats_per_unit,

    // ------------------------------------------------------------------
    // Address window + flush thresholds
    // ------------------------------------------------------------------
    input  logic [ADDR_WIDTH-1:0]         cfg_base_addr,
    input  logic [ADDR_WIDTH-1:0]         cfg_limit_addr,
    input  logic [15:0]                   cfg_flush_watermark, // beats

    // ------------------------------------------------------------------
    // AXI4-shaped master-write FUB
    // ------------------------------------------------------------------
    output logic [AXI_ID_WIDTH_M-1:0]     fub_m_awid,
    output logic [ADDR_WIDTH-1:0]         fub_m_awaddr,
    output logic [7:0]                    fub_m_awlen,
    output logic [2:0]                    fub_m_awsize,
    output logic [1:0]                    fub_m_awburst,
    output logic                          fub_m_awvalid,
    input  logic                          fub_m_awready,

    output logic [63:0]                   fub_m_wdata,
    output logic [7:0]                    fub_m_wstrb,
    output logic                          fub_m_wlast,
    output logic                          fub_m_wvalid,
    input  logic                          fub_m_wready,

    input  logic [AXI_ID_WIDTH_M-1:0]     fub_m_bid,    // ignored
    input  logic [1:0]                    fub_m_bresp,  // ignored
    input  logic                          fub_m_bvalid,
    output logic                          fub_m_bready
`ifdef FORMAL
    ,
    // Formal-only probes of the continuous writer.
    output logic [ADDR_WIDTH-1:0]         f_r_wr_addr,
    output logic [15:0]                   f_r_win_beats,
    output logic [16:0]                   f_r_w_unsent_beats,
    output logic [16:0]                   f_r_aw_cov_beats,
    output logic [15:0]                   f_r_epoch_total,
    output logic [8:0]                    f_r_aw_subs,
    output logic [8:0]                    f_r_b_subs,
    output logic [2:0]                    f_r_os_count,
    output logic [2:0]                    f_r_ws_count,
    output logic [9:0]                    f_r_w_rem_in_sub,
    output logic [15:0]                   f_w_aw_beats,
    output logic                          f_w_aw_issue
`endif
);

    localparam int BYTES_PER_BEAT = 8;                   // 64-bit beats

    // Compressed slots are 1-beat units: no whole-record rounding on any cap.
    logic w_unit_one;
    assign w_unit_one = (beats_per_unit == 16'd1);

    logic w_fifo_empty;
    assign w_fifo_empty = !fifo_rd_valid;

    // ==================================================================
    // Master-write burst writer -- continuous, FSM-free (amba BUG-039,
    // 2026-10-09 redesign; replaces the WR_IDLE/WR_RUN drain-cycle FSM,
    // which quiesced the whole pipeline at every flush boundary).
    //
    // There is no drain cycle and no writer state machine.  An AW
    // handshake fires whenever all of these hold:
    //     (a) a flush trigger: r_fifo_beats >= cfg_flush_watermark OR
    //         FLUSH_TIMEOUT_CYCLES since the last W handshake, and the
    //         FIFO holds at least one whole record;
    //     (b) at least one whole record is in the FIFO that no previous
    //         AW owns (AW cap = record-rounded FIFO beats minus the
    //         committed-not-W-sent prefix counter);
    //     (c) an outstanding slot is free (r_os_count < WR_OS_CAP) and the
    //         window geometry allows a whole record
    //         (min(window budget, beats-to-4KB, FIFO avail, MAX_BURST)).
    // Batches form naturally and run back-to-back: when a trigger is
    // active the AWs keep issuing until nothing uncommitted remains, and
    // when it deasserts mid-stream the W/B streams simply drain in flight
    // -- there is nothing to re-arm and no geometry re-settle bubble.
    //
    // Window geometry is a saturating down-counter, not a pipeline: the
    // window is a contiguous [base, limit] range written strictly
    // sequentially, so "beats left from the running pointer" decrements
    // by each AW's beat count and reloads full on config adoption,
    // rewind, or base-stub step-over.  The 33-bit (limit + 1 - base)
    // subtract that was the 100 MHz critical path (amba ISSUE-001) now
    // feeds a flop once per config change and never sits on the per-AW
    // path; the only per-AW geometry left is the 13-bit beats-to-4KB
    // from r_wr_addr[11:0].  The watermark/timeout knobs keep their
    // batching-floor semantics exactly -- they only gate issue.
    //
    // Sub-burst lengths (awlen / wlast) ride in two small circular queues
    // pushed at every AW handshake; AXI's per-ID in-order B guarantee
    // makes the credit accounting exact.
    // ==================================================================

    // Max outstanding writes the issue logic allows.  The leaf skids are
    // 2 deep, but the B-return pipeline (leaf B skid + the slave's B
    // register) adds ~2 more cycles of transit; 4 covers it without letting
    // AW run far enough ahead to stress slaves that only tolerate a couple
    // of outstanding single-beat writes.
    localparam int WR_OS_CAP = 4;

    logic [ADDR_WIDTH-1:0]       r_wr_addr;           // running write pointer
    logic [15:0]                 r_win_beats;         // beats remaining in the window from r_wr_addr
    logic [16:0]                 r_w_unsent_beats;    // AW-committed beats not yet W-sent (FIFO prefix)
    logic [16:0]                 r_aw_cov_beats;      // beats covered by AWs in the current epoch
    logic [15:0]                 r_epoch_total;       // frozen epoch budget (loaded at epoch start)
    logic                        r_cfg_pend_load;     // sticky: config adoption waiting for an epoch boundary
    logic [8:0]                  r_aw_subs;           // AW (sub-burst) handshakes issued (stats)
    logic [8:0]                  r_b_subs;            // B handshakes returned (credit)
    logic [9:0]                  r_w_rem_in_sub;      // beats left in W-side current sub-burst (0 = none loaded)
    logic [8:0]                  r_os_len [WR_OS_CAP]; // B-side sub-burst lengths (beats-1), AW order
    logic [1:0]                  r_os_rd, r_os_wr;
    logic [2:0]                  r_os_count;
    logic [8:0]                  r_ws_len [WR_OS_CAP]; // W-side sub-burst lengths (beats-1), AW order
    logic [1:0]                  r_ws_rd, r_ws_wr;
    logic [2:0]                  r_ws_count;
    logic [31:0]                 r_timeout_cnt;
    logic [15:0]                 r_fifo_beats;        // registered raw FIFO beat count

    // Locally-registered copies of the quasi-static window config.  They
    // feed the once-per-change budget load and the registered stub/rewind
    // compares; registering them here sources those loads from adjacent
    // flops instead of the far-placed config CSRs (amba ISSUE-001), and
    // the max_fanout cap forces driver replication.  Config is static
    // during operation; a change reloads the budget, so no AW is planned
    // against a half-adopted window.
    (* max_fanout = 24 *) logic [ADDR_WIDTH-1:0] r_cfg_base_addr;
    (* max_fanout = 24 *) logic [ADDR_WIDTH-1:0] r_cfg_limit_addr;
    // limit + 1, 33 bits, registered with the config: the budget divide
    // is (limit + 1 - base) >> 3 for every limit - base, including
    // 0xFFFF_FFFF (which is why the +1 is taken on the quasi-static side,
    // in 33 bits).
    logic [ADDR_WIDTH:0]                          r_cfg_limit_p1;
    // Delayed copy of the registered config.  The difference detects an
    // adopted change exactly once and loads the window budget from the
    // settled registered values; the raw cfg vs r_cfg compare is the
    // 1-cycle-earlier "change in flight" detect and holds AW issue.
    logic [ADDR_WIDTH-1:0]                        r_cfg_base_d1;
    logic [ADDR_WIDTH-1:0]                        r_cfg_limit_d1;

    // Window-budget and AW-cap math (all inputs registered or shallow).
    logic [15:0]                 beats_in_fifo;
    logic [ADDR_WIDTH:0]         w_full_budget_raw;
    logic [15:0]                 w_full_budget;
    logic                        w_cfg_raw_chg;
    logic                        w_cfg_adopted_chg;
    logic [15:0]                 w_4kb_beats;        // beats to the next 4KB boundary
    logic [15:0]                 w_win_units;        // record-rounded window room
    logic [15:0]                 w_4kb_units;        // record-rounded 4KB room
    logic [16:0]                 w_fifo_avail_beats; // uncommitted FIFO beats
    logic [16:0]                 w_fifo_epoch_beats; // avail + covered: coverable by this epoch
    logic [15:0]                 w_fifo_epoch_units; // record-rounded epoch budget (FIFO side)
    logic [15:0]                 w_epoch_live;       // min caps, valid at epoch start (covered == 0)
    logic                        w_epoch_inflight;   // covered != 0: epoch total is frozen
    logic [16:0]                 w_epoch_room;       // beats this epoch may still cover
    logic [15:0]                 w_aw_beats;         // beats the next AW covers
    logic [16:0]                 w_aw_beats_p1;
    logic                        w_epoch_load_en;    // freeze the epoch total this cycle
    logic                        w_epoch_roll;       // epoch complete: restart at the boundary
    logic                        w_geo_blocked;      // no whole record fits from r_wr_addr
    logic                        w_stub_at_base;     // ...but base sits in a too-short stub
    logic [1:0]                  w_win_rem3;   // math_mod_3_compress rem_out is 2 bits (0..2)
    logic [1:0]                  w_4kb_rem3;   // math_mod_3_compress rem_out is 2 bits (0..2)
    logic [1:0]                  w_epoch_rem3;   // math_mod_3_compress rem_out is 2 bits (0..2)
    // flush triggers
    logic                        flush_trigger_watermark;
    logic                        flush_trigger_timeout;
    logic                        have_one_unit;
    logic                        do_flush;

    assign beats_in_fifo = fifo_beat_count;

    // Full window budget off the REGISTERED config: (limit + 1 - base) >> 3,
    // saturated to 16 bits (the 33-bit subtract now loads a counter once
    // per config change / rewind and never sits on the per-AW path).
    assign w_full_budget_raw = (r_cfg_limit_p1 - {1'b0, r_cfg_base_addr}) >> 3;
    assign w_full_budget     = (|w_full_budget_raw[ADDR_WIDTH:16])
                             ? 16'hFFFF : w_full_budget_raw[15:0];

    assign w_cfg_raw_chg     = (cfg_base_addr  != r_cfg_base_addr)
                            || (cfg_limit_addr != r_cfg_limit_addr);
    assign w_cfg_adopted_chg = (r_cfg_base_addr  != r_cfg_base_d1)
                            || (r_cfg_limit_addr != r_cfg_limit_d1);

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_cfg_base_addr  <= '0;
            r_cfg_limit_addr <= '0;
            r_cfg_limit_p1   <= '0;
            r_cfg_base_d1    <= '0;
            r_cfg_limit_d1   <= '0;
        end else begin
            r_cfg_base_addr  <= cfg_base_addr;
            r_cfg_limit_addr <= cfg_limit_addr;
            r_cfg_limit_p1   <= {1'b0, cfg_limit_addr} + 1'b1;
            r_cfg_base_d1    <= r_cfg_base_addr;
            r_cfg_limit_d1   <= r_cfg_limit_addr;
        end
    )

    // Beats to the next 4KB boundary from the running pointer.  13-bit off
    // the registered r_wr_addr[11:0] -- the only per-AW geometry left.
    assign w_4kb_beats = (16'h1000 - {4'b0, r_wr_addr[11:0]}) >> 3;  // 16-bit throughout: 1 .. 0x1000 bytes

    // Strobes of the continuous writer (declared before the epoch logic
    // that references them).
    logic w_aw_issue;
    logic w_w_issue;
    logic w_b_issue;
    logic w_ws_pop;           // W-side queue pop this cycle

    // Record-rounded room on each cap.  floor-to-whole-record is monotonic,
    // so min(then-round) == round(each-then-min): each side rounds
    // independently and the min stays exact.
    assign w_win_units  = w_unit_one ? r_win_beats
                        : (r_win_beats - 16'(w_win_rem3));
    assign w_4kb_units  = w_unit_one ? w_4kb_beats
                        : (w_4kb_beats - 16'(w_4kb_rem3));
    // Beats the FIFO holds that no AW owns yet.  Unsent committed beats are
    // a prefix of the FIFO -- W pops in AW order, and a record is only
    // committable once its beats have all arrived -- so this never
    // underflows.  r_fifo_beats lags the live count by exactly one flop,
    // and the W that drains a committed beat decrements r_w_unsent_beats
    // the same cycle, so the cap stays exact.
    assign w_fifo_avail_beats = 17'(r_fifo_beats) - r_w_unsent_beats;

    // Epoch budget, FIFO side: beats this covering epoch may still commit.
    // avail + covered = beats arrived minus beats covered by previous
    // epochs, so rounding it down to a whole-record multiple never covers
    // an already-covered or not-yet-arrived beat.  The epoch TOTAL is
    // frozen at epoch start (r_epoch_total, loaded the cycle the first AW
    // of an epoch issues): freezing pins the 4KB cap to the page the
    // epoch started in, so a pointer that advances past a page boundary
    // mid-epoch cannot shrink the live cap below the covered count (the
    // unsigned room would underflow), and the epoch always completes at
    // exactly the frozen total -- the pointer lands on a record boundary.
    // Mid-epoch W handshakes leave avail + covered constant, so draining
    // the committed beats never starves the epoch that owns them; new
    // arrivals during the epoch are deferred to the next one (they
    // cannot join: covered > 0 freezes the total).
    assign w_fifo_epoch_beats  = w_fifo_avail_beats + r_aw_cov_beats;
    assign w_fifo_epoch_units  = w_unit_one ? 16'(w_fifo_epoch_beats[15:0])
                            : (16'(w_fifo_epoch_beats[15:0]) - 16'(w_epoch_rem3));

    // Live epoch cap: min of the three record-rounded caps, valid at
    // epoch start (covered == 0).  Individual sub-bursts (awlen) may
    // split records; the alignment invariant lives at the epoch total.
    // MAX_BURST_BEATS may be smaller than a record (AXIL leaves), which
    // only means more sub-bursts per epoch.  Only the low 8 bits go to
    // AWLEN (AXI4 awlen+1 <= 256 beats).
    assign w_epoch_live = (w_win_units < w_4kb_units)
                        ? ((w_win_units  < w_fifo_epoch_units) ? w_win_units  : w_fifo_epoch_units)
                        : ((w_4kb_units  < w_fifo_epoch_units) ? w_4kb_units  : w_fifo_epoch_units);
    assign w_epoch_inflight = (r_aw_cov_beats != 17'd0);
    assign w_epoch_room = w_epoch_inflight ? (17'(r_epoch_total) - r_aw_cov_beats)
                                           : 17'(w_epoch_live);
    assign w_epoch_load_en  = !w_epoch_inflight && w_aw_issue;
    assign w_epoch_roll     = w_epoch_inflight && (w_epoch_room == 17'd0)
                           && (r_w_unsent_beats == 17'd0) && (r_ws_count == 3'd0);
    assign w_aw_beats   = (w_epoch_room == 17'd0) ? 16'd0
                        : (w_epoch_room < 17'(MAX_BURST_BEATS))
                        ? 16'(w_epoch_room) : 16'(MAX_BURST_BEATS);
    assign w_aw_beats_p1 = 17'(w_aw_beats);

    // No whole record fits from the current position (window budget
    // exhausted, or a 4KB stub shorter than one record ahead): the
    // registered fixup in the counter block re-establishes the pointer
    // (rewind home, or step over a stub at base).  Evaluated only when no
    // epoch is in flight: the frozen total already caps the in-flight
    // pointer to the page/span the epoch started in, and re-establishing
    // the pointer mid-epoch would split a record across non-adjacent
    // addresses.
    assign w_geo_blocked = ((w_win_units < beats_per_unit)
                        ||  (w_4kb_units < beats_per_unit))
                        && !w_epoch_inflight;
    // Exception: the window itself still has room and base is the stub --
    // step over the stub instead of rewinding (a full 4KB region always
    // fits at least one record).
    assign w_stub_at_base = w_geo_blocked
                         && (r_wr_addr == r_cfg_base_addr)
                         && (w_win_units >= beats_per_unit);

    // Compressor-style mod-3 instances (combinational); fed by the
    // registered budget / FIFO counters and the shallow 4KB math.
    math_mod_3_compress u_mod3_win (
        .d_in    (r_win_beats),
        .rem_out (w_win_rem3)
    );
    math_mod_3_compress u_mod3_4kb (
        .d_in    (w_4kb_beats),
        .rem_out (w_4kb_rem3)
    );
    math_mod_3_compress u_mod3_fifo (
        .d_in    (16'(w_fifo_epoch_beats[15:0])),
        .rem_out (w_epoch_rem3)
    );

    // Triggers: watermark / timeout (short combinational paths).  Watermark
    // and the >=1-record guard read the SAME registered count (r_fifo_beats)
    // -- the guard is exact without record rounding, because
    // floor(x/u)*u >= u iff x >= u.
    assign have_one_unit            = (r_fifo_beats >= beats_per_unit);
    assign flush_trigger_watermark  = (r_fifo_beats >= cfg_flush_watermark);
    assign flush_trigger_timeout    = (r_timeout_cnt >= 32'(FLUSH_TIMEOUT_CYCLES));

    assign do_flush = (flush_trigger_watermark || flush_trigger_timeout) && have_one_unit;

    // AW fires whenever a flush trigger, a free outstanding slot, epoch
    // room, and the window geometry align; W streams the write FIFO in
    // the AW (sub-burst) order AXI4 demands; B is a pure credit return
    // consumed while any write is outstanding.  The epoch room -- not a
    // per-AW record count -- gates issue, so MAX_BURST_BEATS < record
    // size (AXIL leaves) just means more sub-bursts per epoch.  AW issue
    // holds while a config change is in flight and on the cycle a
    // (possibly deferred) adoption lands, so an address can never be
    // planned against a half-adopted window and an adopted change never
    // clobbers an in-flight AW's pointer advance.
    // Record-alignment gating (do_flush / have_one_unit) applies only to
    // EPOCH START: a fresh epoch must not plan beats that cannot form whole
    // records.  Once an epoch is in flight its beats are already committed
    // -- the frozen total was capped by the FIFO count at start, so the
    // data for every in-epoch sub-burst is provably present -- and gating
    // in-epoch AWs on the live FIFO count deadlocks the tail: the FIFO
    // drops below one record mid-epoch and the remaining covered beats
    // can never issue, leaving the epoch unable to roll (group_chain
    // drains-hang, 2026-10).  In-epoch issue needs only epoch room and a
    // free outstanding slot.
    assign fub_m_awvalid   = (w_epoch_inflight || do_flush)
                          && (w_aw_beats != 16'd0)
                          && (r_os_count < 3'(WR_OS_CAP))
                          && !(w_cfg_raw_chg && !w_epoch_inflight)
                          && !(w_cfg_adopted_chg && !w_epoch_inflight)
                          && !(r_cfg_pend_load && !w_epoch_inflight);
    assign fub_m_awid      = '0;
    assign fub_m_awsize    = 3'd3;          // 2^3 = 8 bytes
    assign fub_m_awburst   = 2'b01;         // INCR
    assign fub_m_awaddr    = r_wr_addr;
    assign fub_m_awlen     = 8'(w_aw_beats - 16'd1);
    assign w_aw_issue      = fub_m_awvalid && fub_m_awready;

    assign fub_m_wvalid    = (r_w_rem_in_sub != 10'd0) && fifo_rd_valid;
    assign fub_m_wdata     = fifo_rd_data;
    assign fub_m_wstrb     = 8'hFF;
    assign fub_m_wlast     = (r_w_rem_in_sub == 10'd1);
    assign fifo_rd_ready = fub_m_wvalid && fub_m_wready;
    assign w_w_issue       = fifo_rd_ready;

    assign fub_m_bready    = (r_os_count != 3'd0);
    assign w_b_issue       = fub_m_bvalid && fub_m_bready;

    // W-side queue pop: on the last beat of the loaded sub-burst (handover)
    // or on a load while no sub-burst is loaded.
    always_comb begin
        if (w_w_issue)
            w_ws_pop = (r_w_rem_in_sub == 10'd1) && (r_ws_count != 3'd0);
        else
            w_ws_pop = (r_w_rem_in_sub == 10'd0) && (r_ws_count != 3'd0);
    end

    // Counters -- the writer is FSM-free: every behavior above is a
    // function of the registered counters below plus the combinational
    // gates of the section header.  Running-pointer discipline, at most
    // one pointer event per cycle, priority:
    //
    //   adopted config : pointer <- base, budget <- full window -- at an
    //                    epoch boundary; an adoption that arrives mid-epoch
    //                    is sticky-deferred (r_cfg_pend_load) so an
    //                    in-flight epoch always completes on the window it
    //                    started in (re-windowing mid-epoch would split a
    //                    record across non-adjacent addresses)
    //   stub at base   : pointer <- next 4KB boundary, budget -= stub
    //                    beats (the stub bytes are inside the window and
    //                    are given up)
    //   AW handshake   : pointer += awlen+1 beats, budget -= awlen+1; the
    //                    epoch total freezes on the first AW of an epoch
    //   geo blocked    : pointer <- base, budget <- full window (window
    //                    end, or a mid-window stub: snap home and continue
    //                    from base, the old writer's ring behavior;
    //                    ping-pongs to a stall with the FIFO full when
    //                    the window cannot hold one record, the documented
    //                    misconfiguration)
    //
    // Fixups are evaluated every cycle (not just under do_flush): they
    // only move these registers, so an eager rewind between epochs costs
    // nothing and removes the old WR_IDLE settle bubble entirely.
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_wr_addr           <= '0;
            r_win_beats         <= 16'd0;
            r_w_unsent_beats    <= 17'd0;
            r_aw_cov_beats      <= 17'd0;
            r_epoch_total       <= 16'd0;
            r_cfg_pend_load     <= 1'b0;
            r_aw_subs           <= 9'd0;
            r_b_subs            <= 9'd0;
            r_w_rem_in_sub      <= 10'd0;
            r_os_len[0]         <= 9'd0;
            r_os_len[1]         <= 9'd0;
            r_os_len[2]         <= 9'd0;
            r_os_len[3]         <= 9'd0;
            r_os_rd             <= 2'd0;
            r_os_wr             <= 2'd0;
            r_os_count          <= 3'd0;
            r_ws_len[0]         <= 9'd0;
            r_ws_len[1]         <= 9'd0;
            r_ws_len[2]         <= 9'd0;
            r_ws_len[3]         <= 9'd0;
            r_ws_rd             <= 2'd0;
            r_ws_wr             <= 2'd0;
            r_ws_count          <= 3'd0;
            r_timeout_cnt       <= 32'd0;
            r_fifo_beats        <= 16'd0;
        end else begin
            // Registered raw FIFO beat count (the trigger and the AW cap
            // both read it; see the header note on the one-flop lag).
            r_fifo_beats <= beats_in_fifo;

            // Timeout counter: cycles since the last accepted W handshake
            // while the FIFO holds data (feeds flush_trigger_timeout).
            if (w_fifo_empty) begin
                r_timeout_cnt <= 32'd0;
            end else if (w_w_issue) begin
                r_timeout_cnt <= 32'd0;
            end else if (r_timeout_cnt < 32'(FLUSH_TIMEOUT_CYCLES)) begin
                r_timeout_cnt <= r_timeout_cnt + 32'd1;
            end

            // Running pointer / window budget / epoch state (one pointer
            // event per cycle; every pointer re-establishment restarts the
            // covering epoch at a record boundary).
            if ((r_cfg_pend_load || w_cfg_adopted_chg) && !w_epoch_inflight) begin
                // Config adoption lands: either a deferred one (sticky
                // flag, set when the change arrived mid-epoch) or the
                // 1-cycle adopted-change pulse, both only at an epoch
                // boundary.  r_cfg_* always hold the latest config, so a
                // deferred adoption picks up the newest window.
                r_wr_addr           <= r_cfg_base_addr;
                r_win_beats         <= w_full_budget;
                r_aw_cov_beats      <= 17'd0;
                r_epoch_total       <= 16'd0;
                r_cfg_pend_load     <= 1'b0;
            end else begin
                if (w_cfg_adopted_chg) r_cfg_pend_load <= 1'b1;   // defer to the epoch boundary
                if (w_stub_at_base) begin
                    r_wr_addr      <= {r_cfg_base_addr[ADDR_WIDTH-1:12] + 1'b1,
                                       12'd0};
                    r_win_beats    <= (r_win_beats > w_4kb_beats)
                                    ? (r_win_beats - w_4kb_beats) : 16'd0;
                    r_aw_cov_beats <= 17'd0;
                    r_epoch_total  <= 16'd0;
                end else if (w_aw_issue) begin
                    r_wr_addr      <= r_wr_addr
                                    + ADDR_WIDTH'(w_aw_beats_p1 * 17'(BYTES_PER_BEAT));
                    r_win_beats    <= r_win_beats - w_aw_beats;
                    r_aw_cov_beats <= r_aw_cov_beats + w_aw_beats_p1;
                end else if (w_geo_blocked) begin
                    r_wr_addr      <= r_cfg_base_addr;
                    r_win_beats    <= w_full_budget;
                    r_aw_cov_beats <= 17'd0;
                    r_epoch_total  <= 16'd0;
                end
            end

            // Freeze the epoch total on the first AW of an epoch
            // (w_epoch_load_en); it holds until the epoch completes.
            if (w_epoch_load_en) r_epoch_total <= w_epoch_live;

            // Epoch rollover: the frozen total is fully covered and every
            // committed beat has left the W stream (unsent == 0 and the
            // W-side length queue is drained), so the pointer sits on a
            // record boundary -- restart the epoch so the next live load
            // can issue.  B credits may still be in flight (os_count > 0);
            // AXI in-order B makes that safe and the next epoch's AWs may
            // issue while they return (os slot cap permitting), so the
            // roll costs no bubble: the room is already zero the cycle it
            // fires, and the next AW issues the cycle covered clears.
            if (w_epoch_roll) begin
                r_aw_cov_beats <= 17'd0;
                r_epoch_total  <= 16'd0;
            end

            // AW-committed-not-W-sent beats (a prefix of the FIFO).
            case ({w_aw_issue, w_w_issue})
                2'b10:   r_w_unsent_beats <= r_w_unsent_beats + w_aw_beats_p1;
                2'b01:   r_w_unsent_beats <= r_w_unsent_beats - 17'd1;
                // Both: a beat left the FIFO AND a new sub-burst committed.
                // Unlike the entry-count queues below (push+pop = net 0),
                // this is a BEAT counter, so the two events do not cancel:
                // net +aw_beats-1.  Recording nothing here under-counts the
                // committed prefix and lets an epoch over-plan the FIFO.
                2'b11:   r_w_unsent_beats <= r_w_unsent_beats + w_aw_beats_p1 - 17'd1;
                default: ;
            endcase

            // -- AW stream bookkeeping: push each sub-burst's length into
            //    both bookkeeping queues.
            if (w_aw_issue) begin
                r_aw_subs         <= r_aw_subs + 9'd1;
                r_os_len[r_os_wr] <= 9'(w_aw_beats - 16'd1);
                r_os_wr           <= r_os_wr + 2'd1;
                r_ws_len[r_ws_wr] <= 9'(w_aw_beats - 16'd1);
                r_ws_wr           <= r_ws_wr + 2'd1;
            end

            // -- B stream: credit return, in AW order (AXI per-ID
            //    in-order guarantee)
            if (w_b_issue) begin
                r_b_subs <= r_b_subs + 9'd1;
                r_os_rd  <= r_os_rd + 2'd1;
            end

            // -- W stream: pop the FIFO in sub-burst order.  Load the
            //    next sub-burst from the W-side queue either one beat
            //    ahead (seamless handover on the last beat of the
            //    current sub-burst) or whenever no sub-burst is loaded
            //    and a length is queued.
            if (w_w_issue) begin
                if (r_w_rem_in_sub == 10'd1) begin
                    r_w_rem_in_sub <= w_ws_pop
                                    ? (10'(r_ws_len[r_ws_rd]) + 10'd1)
                                    : 10'd0;
                end else begin
                    r_w_rem_in_sub <= r_w_rem_in_sub - 10'd1;
                end
            end else if (w_ws_pop) begin
                r_w_rem_in_sub <= 10'(r_ws_len[r_ws_rd]) + 10'd1;
            end
            if (w_ws_pop) begin
                r_ws_rd <= r_ws_rd + 2'd1;
            end

            // -- queue occupancy: one combined update per queue so
            //    simultaneous push/pop cannot clobber (NBA last-win).
            case ({w_aw_issue, w_b_issue})
                2'b10:   r_os_count <= r_os_count + 3'd1;
                2'b01:   r_os_count <= r_os_count - 3'd1;
                default: ;
            endcase
            case ({w_aw_issue, w_ws_pop})
                2'b10:   r_ws_count <= r_ws_count + 3'd1;
                2'b01:   r_ws_count <= r_ws_count - 3'd1;
                default: ;
            endcase
        end
    )

`ifdef FORMAL
    // Formal-only probes: expose the continuous writer state for harness-side
    // checks (hierarchical references are not supported by the sv2v/Yosys flow).
    assign f_r_wr_addr        = r_wr_addr;
    assign f_r_win_beats      = r_win_beats;
    assign f_r_w_unsent_beats = r_w_unsent_beats;
    assign f_r_aw_cov_beats   = r_aw_cov_beats;
    assign f_r_epoch_total    = r_epoch_total;
    assign f_r_aw_subs        = r_aw_subs;
    assign f_r_b_subs         = r_b_subs;
    assign f_r_os_count       = r_os_count;
    assign f_r_ws_count       = r_ws_count;
    assign f_r_w_rem_in_sub   = r_w_rem_in_sub;
    assign f_w_aw_beats       = w_aw_beats;
    assign f_w_aw_issue       = w_aw_issue;
`endif

    // Lint: bresp/bid not used internally
    /* verilator lint_off UNUSED */
    logic [AXI_ID_WIDTH_M-1:0] _unused_bid   = fub_m_bid;
    logic [1:0]                _unused_bresp = fub_m_bresp;
    /* verilator lint_on UNUSED */

endmodule : monbus_burst_writer
