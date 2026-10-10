// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal liveness wrapper for amber_control (yosys-compatible)
// Run with: sby amber_control_live.sby
//
// Task 13 proof (2): no deadlock/livelock under fair arbitration.
//
// Why a separate wrapper: the bounded-residence and whole-request bounds
// quantify over ALL tag-array behaviors, so the tag store is a free
// environment here (top-level inputs are anyseq) -- the strongest
// abstraction, and it removes the behavioral tag model whose SMT store
// chains made deep BMC of the safety wrapper multi-hour. Every FSM path
// (hit, miss, upgrade, snoop detours) remains fully exercised because the
// free tag data makes every hit/miss outcome available at every lookup.
//
// Assumption inventory: identical to the safety wrapper's environment
// table (see formal_amber_control.sv / the Task 13 report): house reset,
// fill done after start / one pulse / within 12 cycles / after all 8
// in-order beats, drain done after start / one pulse / within 6 cycles,
// cdready stall <= 1, snoop grant spacing >= 6, at most 2 snoop grants
// per accepted CPU request, req_valid only at IDLE, one outstanding
// request. The 12-cycle fill window is the structural minimum + margin
// (8 in-order beats => earliest done start+9); a smaller window makes the
// assumption set unsatisfiable and vacates the proof (caught by cover).

module formal_amber_control_live (
    input  logic        clk,
    input  logic        rst_n,

    // tag-array lookups (free: every hit/miss outcome is possible)
    input  logic [1:0][24:0] tag_a_tag_state,
    input  logic [1:0][24:0] tag_b_tag_state,

    // CPU frontend (free environment)
    input  logic        req_valid,
    input  logic [31:0] req_addr,
    input  logic        req_we,
    input  logic [7:0]  req_be,

    // snoop responder (free environment)
    input  logic        snoop_req,
    input  logic [2:0]  snoop_type,
    input  logic [31:0] snoop_addr,
    input  logic        cdready,

    // replacement engine (free)
    input  logic        repl_way,

    // fill / drain partners (free with fair constraints)
    input  logic        fill_done,
    input  logic        fill_beat_valid,
    input  logic [2:0]  fill_beat_idx,
    input  logic        drain_done,

    // data-array read data (free; liveness never depends on data values)
    input  logic [63:0] data_a_rdata,
    input  logic [63:0] data_b_rdata
);

    // DUT outputs used by the properties
    logic        ctrl_req_ready;
    logic        ctrl_rsp_valid;
    logic        ctrl_fill_start;
    logic        ctrl_drain_start;
    logic        ctrl_snoop_ready;
    logic        ctrl_cdvalid;
    logic [3:0]  ctrl_state;

    amber_control dut (
        .clk                     (clk),
        .rst_n                   (rst_n),
        .req_valid               (req_valid),
        .req_addr                (req_addr),
        .req_we                  (req_we),
        .req_be                  (req_be),
        .req_wdata               (64'd0),
        .ctrl_req_ready          (ctrl_req_ready),
        .ctrl_rsp_valid          (ctrl_rsp_valid),
        .ctrl_rsp_data           (),
        .ctrl_tag_a_set          (),
        .ctrl_tag_a_tag_state    (tag_a_tag_state),
        .ctrl_tag_a_wr_en        (),
        .ctrl_tag_a_wr_way_onehot(),
        .ctrl_tag_a_wr_set       (),
        .ctrl_tag_a_wr_tag_state (),
        .ctrl_data_a_addr        (),
        .ctrl_data_a_way         (),
        .ctrl_data_a_rdata       (data_a_rdata),
        .ctrl_data_a_wr_en       (),
        .ctrl_data_a_wr_way_onehot(),
        .ctrl_data_a_wr_addr     (),
        .ctrl_data_a_wr_wdata    (),
        .ctrl_data_a_wr_be       (),
        .ctrl_tag_b_req          (),
        .ctrl_tag_b_set          (),
        .ctrl_tag_b_tag_state    (tag_b_tag_state),
        .ctrl_data_b_addr        (),
        .ctrl_data_b_way         (),
        .ctrl_data_b_rdata       (data_b_rdata),
        .ctrl_repl_req           (),
        .ctrl_repl_set           (),
        .ctrl_repl_way           (repl_way),
        .ctrl_repl_hit           (),
        .ctrl_repl_update        (),
        .ctrl_repl_hit_way       (),
        .ctrl_victim_load        (),
        .ctrl_victim_addr_in     (),
        .ctrl_victim_data_in     (),
        .ctrl_fill_start         (ctrl_fill_start),
        .ctrl_fill_addr          (),
        .ctrl_req_class          (),
        .ctrl_fill_done          (fill_done),
        .ctrl_fill_beat_valid    (fill_beat_valid),
        .ctrl_fill_beat_idx      (fill_beat_idx),
        .ctrl_drain_start        (ctrl_drain_start),
        .ctrl_drain_done         (drain_done),
        .ctrl_snoop_req          (snoop_req),
        .ctrl_snoop_ready        (ctrl_snoop_ready),
        .ctrl_snoop_type         (snoop_type),
        .ctrl_snoop_addr         (snoop_addr),
        .ctrl_crresp             (),
        .ctrl_cddata             (),
        .ctrl_cdlast             (),
        .ctrl_cdvalid            (ctrl_cdvalid),
        .ctrl_cdready            (cdready),
        .ctrl_init_busy          (),
        .ctrl_init_set           (),
        .ctrl_state              (ctrl_state)
    );

    // ------------------------------------------------------------------
    // House reset protocol
    // ------------------------------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // ------------------------------------------------------------------
    // Fair environment (identical table to the safety wrapper)
    // ------------------------------------------------------------------
    localparam [3:0] CS_IDLE        = 4'd0;
    localparam [3:0] CS_MISS_VICTIM = 4'd5;
    localparam [3:0] CS_MISS_DRAIN  = 4'd6;
    localparam [3:0] CS_MISS_FILL   = 4'd7;
    localparam [3:0] CS_SNOOP       = 4'd10;

    // fill partner
    reg f_fill_start_seen, f_fill_done_seen;
    reg [3:0] f_fill_wait;
    reg [3:0] f_beat_count;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_fill_start_seen <= 1'b0; f_fill_done_seen <= 1'b0;
            f_fill_wait <= 4'd0; f_beat_count <= 4'd0;
        end else begin
            if (ctrl_fill_start) begin
                f_fill_start_seen <= 1'b1;
                f_fill_wait <= 4'd0;
                f_beat_count <= 4'd0;
            end else if (!f_fill_done_seen && (f_fill_wait != 4'hF)) begin
                f_fill_wait <= f_fill_wait + 4'd1;
            end
            if (fill_done) f_fill_done_seen <= 1'b1;
            if (fill_beat_valid && (f_beat_count != 4'hF))
                f_beat_count <= f_beat_count + 4'd1;
            if (ctrl_state == 4'd8) begin   // FILL_WRITE consumes the launch
                f_fill_start_seen <= 1'b0; f_fill_done_seen <= 1'b0;
                f_fill_wait <= 4'd0; f_beat_count <= 4'd0;
            end
        end
    end

    always @(posedge clk) begin
        if (rst_n) begin
            as_fill_done_after_start: assume (!fill_done || f_fill_start_seen);
            as_fill_done_once: assume (!fill_done || !f_fill_done_seen);
            as_fill_done_fair: assume (!(f_fill_start_seen && !f_fill_done_seen)
                                       || (f_fill_wait < 12) || fill_done);
            as_fill_done_is_rlast: assume (!fill_done
                                           || (f_beat_count == 4'd8));
            as_beat_order: assume (!fill_beat_valid
                || (f_fill_start_seen && !f_fill_done_seen
                    && (fill_beat_idx == f_beat_count[2:0])));
        end
    end

    // drain partner
    reg f_drain_start_seen, f_drain_done_seen;
    reg [3:0] f_drain_wait;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_drain_start_seen <= 1'b0; f_drain_done_seen <= 1'b0;
            f_drain_wait <= 4'd0;
        end else begin
            if (ctrl_drain_start) begin
                f_drain_start_seen <= 1'b1;
                f_drain_wait <= 4'd0;
            end else if (!f_drain_done_seen && (f_drain_wait != 4'hF)) begin
                f_drain_wait <= f_drain_wait + 4'd1;
            end
            if (drain_done) f_drain_done_seen <= 1'b1;
            if (ctrl_state == 4'd8) begin
                f_drain_start_seen <= 1'b0; f_drain_done_seen <= 1'b0;
                f_drain_wait <= 4'd0;
            end
        end
    end

    always @(posedge clk) begin
        if (rst_n) begin
            as_drain_done_after_start: assume (!drain_done || f_drain_start_seen);
            as_drain_done_once: assume (!drain_done || !f_drain_done_seen);
            as_drain_done_fair: assume (!(f_drain_start_seen && !f_drain_done_seen)
                                        || (f_drain_wait < 6) || drain_done);
        end
    end

    // CD channel
    reg [1:0] f_cd_wait;
    always @(posedge clk) begin
        if (!rst_n) f_cd_wait <= 0;
        else if (ctrl_cdvalid && !cdready) begin
            if (f_cd_wait != 2'h3) f_cd_wait <= f_cd_wait + 1;
        end else f_cd_wait <= 0;
    end

    always @(posedge clk) begin
        if (rst_n)
            as_cdready_fair: assume (!(ctrl_cdvalid && !cdready)
                                     || (f_cd_wait < 1) || cdready);
    end

    // CPU / snoop fair arbitration
    reg        f_req_pending;
    wire       f_req_accept = req_valid && ctrl_req_ready;
    always @(posedge clk) begin
        if (!rst_n) f_req_pending <= 1'b0;
        else if (f_req_accept) f_req_pending <= 1'b1;
        else if (ctrl_rsp_valid) f_req_pending <= 1'b0;
    end

    reg [3:0] f_sn_gap;
    reg [1:0] f_sn_per_txn;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_sn_gap <= 4'hF;
            f_sn_per_txn <= 2'd0;
        end else begin
            if (ctrl_snoop_ready) begin
                f_sn_gap <= 4'd0;
                if (f_req_pending && (f_sn_per_txn != 2'h3))
                    f_sn_per_txn <= f_sn_per_txn + 1;
            end else if (f_sn_gap != 4'hF) begin
                f_sn_gap <= f_sn_gap + 4'd1;
            end
            if (f_req_accept) f_sn_per_txn <= 2'd0;
        end
    end

    // The fill committed the line (proven on the tag-model wrapper:
    // ap_fill_install, plus the landed array write): the replayed lookup
    // must see it. The free-tag model otherwise lets the replay miss
    // forever, making the request bound unprovable by construction -- this
    // assumption imports the real array's read-after-write consequence.
    // (Found as ap_txn_bounded failing at timer=104 with an infinitely
    // re-missing replay; the safety BMC's install claims justify it.)
    reg f_replay_q, f_replay_lookup;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_replay_q <= 1'b0;
            f_replay_lookup <= 1'b0;
        end else begin
            if (ctrl_state == 4'd9) f_replay_q <= 1'b1;   // REPLAY arms it
            else if (ctrl_state == 4'd2) f_replay_q <= 1'b0; // LOOKUP consumes
            f_replay_lookup <= f_replay_q && (ctrl_state == 4'd2);
        end
    end

    always @(posedge clk) begin
        if (rst_n)
            as_replay_hits: assume (!f_replay_lookup
                || (ctrl_state == 4'd3) || (ctrl_state == 4'd4));
    end

    always @(posedge clk) begin
        if (rst_n) begin
            as_sn_spacing: assume (!snoop_req || (f_sn_gap >= 6));
            as_sn_per_txn: assume (!ctrl_snoop_ready || (f_sn_per_txn < 2));
            as_req_at_idle: assume (!req_valid || (ctrl_state == CS_IDLE));
            as_single_outstanding: assume (!req_valid || !f_req_pending);
        end
    end

    // ------------------------------------------------------------------
    // Bounded liveness (the no-deadlock/livelock claims)
    // ------------------------------------------------------------------
    reg [4:0] f_fill_res, f_drain_res, f_victim_res, f_snoop_res;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_fill_res <= 0; f_drain_res <= 0;
            f_victim_res <= 0; f_snoop_res <= 0;
        end else begin
            if (ctrl_state == CS_MISS_FILL && f_fill_start_seen && !f_fill_done_seen)
                f_fill_res <= f_fill_res + 1;
            else f_fill_res <= 0;
            if (ctrl_state == CS_MISS_DRAIN && f_drain_start_seen && !f_drain_done_seen)
                f_drain_res <= f_drain_res + 1;
            else f_drain_res <= 0;
            if (ctrl_state == CS_MISS_VICTIM) f_victim_res <= f_victim_res + 1;
            else f_victim_res <= 0;
            if (ctrl_state == CS_SNOOP) f_snoop_res <= f_snoop_res + 1;
            else f_snoop_res <= 0;
        end
    end

    always @(posedge clk) begin
        if (rst_n) begin
            ap_fill_bounded: assert (f_fill_res < 16);
            ap_drain_bounded: assert (f_drain_res < 8);
            ap_victim_bounded: assert (f_victim_res < 12);
            ap_snoop_bounded: assert (f_snoop_res < 40);
        end
    end

    // whole-request bound: accept -> response never exceeds the budget
    // (lookup + victim gather + fair drain + fair fill (12-cycle window) +
    // 2 bounded snoop detours; honest worst ~95, ~9% margin). Bounds are
    // generous on purpose -- a FAIL means the RTL can actually be starved.
    reg [7:0] f_txn_timer;
    always @(posedge clk) begin
        if (!rst_n) f_txn_timer <= 0;
        else if (f_req_accept) f_txn_timer <= 8'd1;
        else if (f_req_pending) begin
            if (f_txn_timer != 8'hFF) f_txn_timer <= f_txn_timer + 8'd1;
        end else f_txn_timer <= 0;
    end

    always @(posedge clk) begin
        if (rst_n)
            ap_txn_bounded: assert (!f_req_pending || (f_txn_timer < 104));
    end

    // ------------------------------------------------------------------
    // Cover: the bound is not vacuous -- a deep request really completes
    // ------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n)
            cp_deep_txn: cover (ctrl_rsp_valid && (f_txn_timer > 30));
    end

endmodule
