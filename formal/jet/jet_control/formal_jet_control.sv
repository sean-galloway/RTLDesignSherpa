// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for jet_control (yosys-compatible) -- SAFETY + COVER.
// Run with: sby jet_control.sby
//
// Task 11 (jet MAS ch05/01) at the tiny geometry SETS=16 / WAYS=2 /
// LINE_BYTES=64 / BUS_WIDTH=64 / MSHR_COUNT=2 / VICTIM_DEPTH=2.  The tiny
// geometry is not a limitation for these properties: MSHR-full (2
// entries), WB-full (2 slots) and set oversubscription (2 claims in a
// 2-way set) are reachable exactly there.
//
// Composition: the DUT plus the REAL jet_mshr / jet_wb_buffer /
// jet_rsp_seq leaf blocks (the control layer drives them over handshake
// pins; proving against the real files keeps the alloc/CAM/claim/snarf
// answers honest).  The tag arrays stay outside: the wrapper carries an
// abstract tag store (a 16x2 store, reset Invalid, applying every port-A
// write -- an exact model of l1_tag_array at this geometry).  The data
// arrays are free inputs: no property claims data values.  l1_fill /
// l1_drain are rig-top integrations (jet_top), so the harness drives
// their handshake pins as free inputs under the documented engine
// contract (the assumption table below mirrors jet_top's fill-launch
// adapter and the l1_fill/l1_drain handshake rules).
//
// The snoop peer is modeled as a want line plus a presenting shim: the
// transport (l1_snoop_resp) accepts an AC only while sn_safe_o, so the
// shim presents exactly then -- the DUT's sn_req |-> sn_safe contract is
// structural here.  The peer holds want/addr/type until the grant (the
// ACVALID rule).
//
// Internal observability: the DUT flat is parameter-specialized (see the
// Makefile) and jet_control.sby exposes 20 internal signals as DUT output
// ports (yosys has no hierarchical references and its bind statement
// never fires on any target -- the amber Task 13 toolchain finding), so
// expose + plain wiring is the mechanism.  Everything else the properties
// need comes from the real leaf outputs or the wrapper's own shadow
// models (driven by the leaf's own alloc/retire event taps, so the shadow
// is exactly the leaf's occupancy).
//
// Assumption inventory (environment obligations; each recorded):
//   - house reset protocol;
//   - A-fill-accept: the launch adapter accepts a presented launch
//     combinationally when (and only when) the engine is idle, no victim
//     capture streams, and the cycle is not a dirty-victim alloc -- the
//     exact jet_top rule;
//   - A-fill-flight: beats only for the in-flight entry, in order 0..7,
//     only after the fill's AR is accepted; a data fill's done comes after
//     all 8 beats, a CU's with none; AR accepted within 4 cycles of the
//     launch accept, done within 15 (a fair, single-outstanding engine);
//   - A-fill-pd: PassDirty at done only on an RNSD flight;
//   - A-drain: done only while a drain is outstanding, forced within 10
//     cycles of the start (a fair l1_drain);
//   - A-cdready: stalled at most 1 cycle (fair manager);
//   - A-snoop-transport: the peer holds want/addr/type until the grant
//     and presents only legal snoop types (0..5).
//
// The CPU frontend needs NO assumptions: the lookup stage is a
// combinational classify of the currently-presented request, so each
// presenting cycle is an independent request (stalled requests retry --
// the J6 story -- and nothing is latched before the accept).

module formal_jet_control (
    input  logic        clk,
    input  logic        rst_n,

    // CPU frontend (free environment)
    input  logic        lkup_valid,
    input  logic [31:0] lkup_addr,
    input  logic        lkup_we,
    input  logic [7:0]  lkup_be,

    // replacement engine (free: any victim way is legal -- the
    // claim-aware victim check (S4) is exactly what makes that safe)
    input  logic        repl_victim_way,

    // snoop peer (free want; the shim presents when the DUT is safe)
    input  logic        sn_want,
    input  logic [31:0] sn_addr,
    input  logic [2:0]  sn_type,
    input  logic        sn_cdready,

    // response frontend (free; the ring backpressures via tag_gnt)
    input  logic        rsp_ready,

    // fill engine (free with the launch-adapter contract, see header)
    input  logic        fill_accept,
    input  logic        fill_pass_dirty,
    input  logic        fill_beat_valid,
    input  logic        fill_beat_idx,
    input  logic [2:0]  fill_beat_num,
    input  logic        fill_done,
    input  logic        fill_ar_done,

    // drain engine (free, fair)
    input  logic        drain_done,

    // data-array read data (free; no property claims data values)
    input  logic [63:0] dat_a_rdata,
    input  logic [63:0] dat_b_rdata
);

    // ------------------------------------------------------------------
    // Geometry (the specialized flat is parameterless; these mirror it)
    // ------------------------------------------------------------------
    localparam SETS       = 16;
    localparam WAYS       = 2;
    localparam SET_W      = 4;
    localparam TAG_W      = 22;
    localparam TSW        = 25;
    localparam LINE_W     = 26;
    localparam FILL_BEATS = 8;

    // MESI (l1_pkg) and jet class encodings (jet_pkg)
    localparam [2:0] ST_I = 3'b000;
    localparam [2:0] ST_S = 3'b001;
    localparam [2:0] ST_E = 3'b010;
    localparam [2:0] ST_M = 3'b011;
    localparam [1:0] CLS_RNSD = 2'b00;
    localparam [1:0] CLS_RU   = 2'b01;
    localparam [1:0] CLS_CU   = 2'b10;
    // commit / snoop FSM encodings (jet_control localparams)
    localparam [3:0] C_IDLE       = 4'd0;
    localparam [3:0] C_CU_INSTALL = 4'd7;
    localparam [1:0] SN_IDLE = 2'd0;
    localparam [1:0] SN_DATA = 2'd1;
    localparam [1:0] SRC_MSHR = 2'd2;
    // stall sub-reasons (jet_control localparams)
    localparam [2:0] STALL_MSHR_FULL   = 3'd1;
    localparam [2:0] STALL_WB          = 3'd2;
    localparam [2:0] STALL_SET_OVERSUB = 3'd3;
    localparam [2:0] STALL_XCLASS      = 3'd4;
    localparam [2:0] STALL_TAG_FULL    = 3'd5;
    localparam [2:0] STALL_COMMIT      = 3'd6;
    // PF_GUARD mask: keeps {WasUnique, IsShared}, clears PassDirty/DT
    localparam [4:0] CRRESP_NO_DT = 5'b11000;

    // ------------------------------------------------------------------
    // DUT outputs
    // ------------------------------------------------------------------
    logic        dut_init_busy;
    logic        dut_lkup_ready;
    logic        dut_lkup_hit;
    logic        dut_lkup_merge;
    logic        dut_lkup_miss_alloc;
    logic        dut_lkup_upgrade;
    logic        dut_lkup_stall;
    logic [2:0]  dut_stall_reason;
    logic        dut_wr_yield;
    logic        dut_cap_busy;
    logic        dut_tag_req;
    logic        dut_cpl_valid;
    logic [1:0]  dut_cpl_tag;
    logic [63:0] dut_cpl_data;
    logic [3:0]  dut_tag_a_set;
    logic        dut_tag_a_wr_en;
    logic [1:0]  dut_tag_a_wr_way;
    logic [3:0]  dut_tag_a_wr_set;
    logic [24:0] dut_tag_a_wr_ts;
    logic        dut_tag_b_req;
    logic [3:0]  dut_tag_b_set;
    logic        dut_mshr_alloc;
    logic [25:0] dut_alloc_line;
    logic [3:0]  dut_alloc_set;
    logic [1:0]  dut_alloc_cls;
    logic        dut_alloc_install;
    logic        dut_alloc_vway;
    logic        dut_alloc_wb_slot;
    logic        dut_alloc_wb_valid;
    logic [1:0]  dut_alloc_seq;
    logic [25:0] dut_lkup_line;
    logic        dut_cpl_idx;
    logic        dut_mshr_merge;
    logic        dut_mshr_merge_idx;
    logic [1:0]  dut_mshr_merge_seq;
    logic        dut_mshr_beat;
    logic        dut_mshr_beat_idx;
    logic [2:0]  dut_mshr_beat_num;
    logic        dut_mshr_retire;
    logic        dut_mshr_retire_idx;
    logic        dut_wb_cap;
    logic [25:0] dut_wb_cap_line;
    logic        dut_wb_cap_beat;
    logic [63:0] dut_wb_cap_beat_data;
    logic [25:0] dut_wb_sn_line;
    logic [1:0]  dut_wb_sn_eff;
    logic        dut_drain_start;
    logic [25:0] dut_mshr_sn_line;
    logic        dut_mshr_sn_eff;
    logic        dut_mshr_sn_eff_idx;
    logic [1:0]  dut_mshr_sn_eff_value;
    logic        dut_sn_ready;
    logic        dut_sn_safe;
    logic [4:0]  dut_sn_crresp;
    logic [63:0] dut_sn_cddata;
    logic        dut_sn_cdlast;
    logic        dut_sn_cdvalid;
    logic        dut_fill_start;
    logic [31:0] dut_fill_addr;
    logic [1:0]  dut_fill_cls;
    logic        dut_cmt_busy;
    logic        dut_ctrl_error;

    // exposed internals (jet_control.sby `expose`; see the header note)
    logic [3:0]  obs_cmt_state;
    logic [1:0]  obs_sn_state;
    logic [1:0]  obs_sn_src;
    logic        obs_sn_allb;
    logic        obs_upgr_valid;
    logic [25:0] obs_upgr_line;
    logic [3:0]  obs_upgr_set;
    logic        obs_upgr_way;
    logic        obs_upgr_killed;
    logic        obs_fill_pend;
    logic        obs_fill_idx;
    logic        obs_ar_done;
    logic [1:0]  obs_claim_vld;
    logic [2:0]  obs_fq_undone;
    logic        obs_src_wb;
    logic        obs_src_mshr;
    logic        obs_src_array;
    logic [2:0]  obs_sn_ref;
    logic        obs_sn_deliver;
    logic        obs_mshr_pre_ar;

    // ------------------------------------------------------------------
    // Leaf wiring
    // ------------------------------------------------------------------
    logic        mshr_alloc_gnt;
    logic        mshr_alloc_idx;
    logic        mshr_full;
    logic        mshr_set_full;
    logic        mshr_lkup_reg_match;
    logic        mshr_lkup_reg_match_idx;
    logic [1:0]  mshr_lkup_reg_match_cls;
    logic        mshr_sn_match;
    logic        mshr_sn_match_idx;
    logic [7:0]  mshr_sn_beats;
    logic        mshr_sn_install;
    logic [25:0] mshr_cpl_line;
    logic [1:0]  mshr_cpl_pend_eff;
    logic [3:0]  mshr_cpl_merge_seqs;
    logic [1:0]  mshr_cpl_merge_count;
    logic        mshr_ev_alloc;    // leaf event taps: the TRUE alloc/retire
    logic        mshr_ev_retire;
    logic        mshr_ev_retire_idx;

    logic        wb_cap_gnt;
    logic        wb_cap_slot;
    logic        wb_full;
    logic        wb_drain_valid;
    logic        wb_sn_hit;
    logic [511:0] wb_sn_data;
    logic        wb_sn_bresp_cycle;

    logic        seq_tag_gnt;
    logic [1:0]  seq_tag;

    // ------------------------------------------------------------------
    // Abstract tag-array model (exact at 16x2): reset to Invalid (the D-3
    // init walk writes {0, I} everywhere, a no-op on the model), every
    // port-A write applied, both ports read combinationally.
    // ------------------------------------------------------------------
    reg [24:0] tag_model [0:31];
    integer mi;
    always @(posedge clk) begin
        if (!rst_n) begin
            for (mi = 0; mi < 32; mi = mi + 1)
                tag_model[mi] <= 25'd0;   // {tag 0, STATE_I}
        end else if (dut_tag_a_wr_en) begin
            if (dut_tag_a_wr_way[0])
                tag_model[dut_tag_a_wr_set] <= dut_tag_a_wr_ts;
            if (dut_tag_a_wr_way[1])
                tag_model[16 + dut_tag_a_wr_set] <= dut_tag_a_wr_ts;
        end
    end

    wire [1:0][24:0] w_tag_a_ts;
    wire [1:0][24:0] w_tag_b_ts;
    assign w_tag_a_ts[0] = tag_model[dut_tag_a_set];
    assign w_tag_a_ts[1] = tag_model[16 + dut_tag_a_set];
    assign w_tag_b_ts[0] = tag_model[dut_tag_b_set];
    assign w_tag_b_ts[1] = tag_model[16 + dut_tag_b_set];

    // ------------------------------------------------------------------
    // Snoop transport shim: present exactly while the DUT is safe (the
    // l1_snoop_resp accept-only-while-safe contract, structural here).
    // ------------------------------------------------------------------
    wire w_sn_req = sn_want & dut_sn_safe;
    wire w_sn_gnt = w_sn_req & dut_sn_ready;

    // ------------------------------------------------------------------
    // DUT
    // ------------------------------------------------------------------
    jet_control dut (
        .clk                     (clk),
        .rst_n                   (rst_n),
        .init_busy_o             (dut_init_busy),
        .lkup_valid_i            (lkup_valid),
        .lkup_addr_i             (lkup_addr),
        .lkup_we_i               (lkup_we),
        .lkup_be_i               (lkup_be),
        .lkup_wdata_i            (64'd0), // tied: no property claims data values
        .lkup_ready_o            (dut_lkup_ready),
        .lkup_hit_o              (dut_lkup_hit),
        .lkup_merge_o            (dut_lkup_merge),
        .lkup_miss_alloc_o       (dut_lkup_miss_alloc),
        .lkup_upgrade_o          (dut_lkup_upgrade),
        .lkup_stall_o            (dut_lkup_stall),
        .lkup_stall_reason_o     (dut_stall_reason),
        .lkup_wr_yield_o         (dut_wr_yield),
        .cap_busy_o              (dut_cap_busy),
        .tag_req_o               (dut_tag_req),
        .tag_gnt_i               (seq_tag_gnt),
        .tag_i                   (seq_tag),
        .cpl_valid_o             (dut_cpl_valid),
        .cpl_tag_o               (dut_cpl_tag),
        .cpl_data_o              (dut_cpl_data),
        .tag_a_set_o             (dut_tag_a_set),
        .tag_a_tag_state_i       (w_tag_a_ts),
        .tag_a_wr_en_o           (dut_tag_a_wr_en),
        .tag_a_wr_way_onehot_o   (dut_tag_a_wr_way),
        .tag_a_wr_set_o          (dut_tag_a_wr_set),
        .tag_a_wr_tag_state_o    (dut_tag_a_wr_ts),
        .dat_a_addr_o            (),
        .dat_a_way_o             (),
        .dat_a_rdata_i           (dat_a_rdata),
        .dat_a_wr_en_o           (),
        .dat_a_wr_way_onehot_o   (),
        .dat_a_wr_addr_o         (),
        .dat_a_wr_wdata_o        (),
        .dat_a_wr_be_o           (),
        .dat_b_addr_o            (),
        .dat_b_way_o             (),
        .dat_b_rdata_i           (dat_b_rdata),
        .repl_req_o              (),
        .repl_set_o              (),
        .repl_victim_way_i       (repl_victim_way),
        .repl_hit_o              (),
        .repl_update_o           (),
        .repl_hit_way_o          (),
        .mshr_alloc_o            (dut_mshr_alloc),
        .mshr_alloc_line_o       (dut_alloc_line),
        .mshr_alloc_set_o        (dut_alloc_set),
        .mshr_alloc_cls_o        (dut_alloc_cls),
        .mshr_alloc_install_o    (dut_alloc_install),
        .mshr_alloc_victim_way_o (dut_alloc_vway),
        .mshr_alloc_wb_slot_o    (dut_alloc_wb_slot),
        .mshr_alloc_wb_valid_o   (dut_alloc_wb_valid),
        .mshr_alloc_seq_o        (dut_alloc_seq),
        .mshr_alloc_gnt_i        (mshr_alloc_gnt),
        .mshr_alloc_idx_i        (mshr_alloc_idx),
        .mshr_full_i             (mshr_full),
        .mshr_set_full_i         (mshr_set_full),
        .mshr_lkup_line_o        (dut_lkup_line),
        .mshr_lkup_reg_match_i   (mshr_lkup_reg_match),
        .mshr_lkup_reg_match_idx_i(mshr_lkup_reg_match_idx),
        .mshr_lkup_reg_match_cls_i(mshr_lkup_reg_match_cls),
        .mshr_cpl_idx_o          (dut_cpl_idx),
        .mshr_cpl_merge_count_i  (mshr_cpl_merge_count),
        .mshr_cpl_line_i         (mshr_cpl_line),
        .mshr_cpl_pend_eff_i     (mshr_cpl_pend_eff),
        .mshr_cpl_merge_seqs_i   (mshr_cpl_merge_seqs),
        .mshr_merge_o            (dut_mshr_merge),
        .mshr_merge_idx_o        (dut_mshr_merge_idx),
        .mshr_merge_seq_o        (dut_mshr_merge_seq),
        .mshr_beat_o             (dut_mshr_beat),
        .mshr_beat_idx_o         (dut_mshr_beat_idx),
        .mshr_beat_num_o         (dut_mshr_beat_num),
        .mshr_retire_o           (dut_mshr_retire),
        .mshr_retire_idx_o       (dut_mshr_retire_idx),
        .wb_cap_o                (dut_wb_cap),
        .wb_cap_line_o           (dut_wb_cap_line),
        .wb_cap_beat_o           (dut_wb_cap_beat),
        .wb_cap_beat_data_o      (dut_wb_cap_beat_data),
        .wb_cap_gnt_i            (wb_cap_gnt),
        .wb_cap_slot_i           (wb_cap_slot),
        .wb_full_i               (wb_full),
        .wb_sn_line_o            (dut_wb_sn_line),
        .wb_sn_hit_i             (wb_sn_hit),
        .wb_sn_eff_o             (dut_wb_sn_eff),
        .wb_sn_data_i            (wb_sn_data),
        .wb_sn_bresp_cycle_i     (wb_sn_bresp_cycle),
        .wb_drain_valid_i        (wb_drain_valid),
        .drain_start_o           (dut_drain_start),
        .drain_done_i            (drain_done),
        .tag_b_req_o             (dut_tag_b_req),
        .tag_b_set_o             (dut_tag_b_set),
        .tag_b_tag_state_i       (w_tag_b_ts),
        .mshr_sn_line_o          (dut_mshr_sn_line),
        .mshr_sn_match_i         (mshr_sn_match),
        .mshr_sn_match_idx_i     (mshr_sn_match_idx),
        .mshr_sn_beats_rcvd_i    (mshr_sn_beats),
        .mshr_sn_install_i       (mshr_sn_install),
        .mshr_sn_eff_o           (dut_mshr_sn_eff),
        .mshr_sn_eff_idx_o       (dut_mshr_sn_eff_idx),
        .mshr_sn_eff_value_o     (dut_mshr_sn_eff_value),
        .sn_req_i                (w_sn_req),
        .sn_want_i               (sn_want),
        .sn_addr_i               (sn_addr),
        .sn_type_i               (sn_type),
        .sn_ready_o              (dut_sn_ready),
        .sn_safe_o               (dut_sn_safe),
        .sn_crresp_o             (dut_sn_crresp),
        .sn_cddata_o             (dut_sn_cddata),
        .sn_cdlast_o             (dut_sn_cdlast),
        .sn_cdvalid_o            (dut_sn_cdvalid),
        .sn_cdready_i            (sn_cdready),
        .fill_start_o            (dut_fill_start),
        .fill_addr_o             (dut_fill_addr),
        .fill_cls_o              (dut_fill_cls),
        .fill_accept_i           (fill_accept),
        .fill_pass_dirty_i       (fill_pass_dirty),
        .fill_beat_valid_i       (fill_beat_valid),
        .fill_beat_idx_i         (fill_beat_idx),
        .fill_beat_num_i         (fill_beat_num),
        .fill_done_i             (fill_done),
        .fill_ar_done_i          (fill_ar_done),
        .cmt_busy_o              (dut_cmt_busy),
        .ctrl_error_o            (dut_ctrl_error),
        .r_cmt_state             (obs_cmt_state),
        .r_sn_state              (obs_sn_state),
        .r_sn_src                (obs_sn_src),
        .r_sn_allb               (obs_sn_allb),
        .r_upgr_valid            (obs_upgr_valid),
        .r_upgr_line             (obs_upgr_line),
        .r_upgr_set              (obs_upgr_set),
        .r_upgr_way              (obs_upgr_way),
        .r_upgr_killed           (obs_upgr_killed),
        .r_fill_pend             (obs_fill_pend),
        .r_fill_idx              (obs_fill_idx),
        .r_ar_done               (obs_ar_done),
        .r_claim_vld             (obs_claim_vld),
        .r_fq_undone             (obs_fq_undone),
        .w_src_wb                (obs_src_wb),
        .w_src_mshr              (obs_src_mshr),
        .w_src_array             (obs_src_array),
        .w_sn_ref                (obs_sn_ref),
        .w_sn_deliver            (obs_sn_deliver),
        .w_mshr_pre_ar           (obs_mshr_pre_ar)
    );

    // ------------------------------------------------------------------
    // Real leaf blocks (the control layer's handshake partners)
    // ------------------------------------------------------------------
    jet_mshr #(
        .MSHR_COUNT   (2),
        .SETS         (SETS),
        .WAYS         (WAYS),
        .LINE_W       (LINE_W),
        .SEQ_W        (2),
        .VICTIM_DEPTH (2)
    ) mshr (
        .clk                 (clk),
        .rst_n               (rst_n),
        .alloc_i             (dut_mshr_alloc),
        .alloc_line_i        (dut_alloc_line),
        .alloc_set_i         (dut_alloc_set),
        .alloc_cls_i         (dut_alloc_cls),
        .alloc_install_i     (dut_alloc_install),
        .alloc_victim_way_i  (dut_alloc_vway),
        .alloc_wb_slot_i     (dut_alloc_wb_slot),
        .alloc_wb_valid_i    (dut_alloc_wb_valid),
        .alloc_seq_i         (dut_alloc_seq),
        .alloc_gnt_o         (mshr_alloc_gnt),
        .alloc_idx_o         (mshr_alloc_idx),
        .full_o              (mshr_full),
        .set_full_o          (mshr_set_full),
        .lkup_line_i         (dut_lkup_line),
        .lkup_match_o        (),
        .lkup_reg_match_o    (mshr_lkup_reg_match),
        .lkup_reg_match_idx_o(mshr_lkup_reg_match_idx),
        .lkup_reg_match_cls_o(mshr_lkup_reg_match_cls),
        .lkup_match_idx_o    (),
        .lkup_match_cls_o    (),
        .sn_line_i           (dut_mshr_sn_line),
        .sn_match_o          (mshr_sn_match),
        .sn_match_idx_o      (mshr_sn_match_idx),
        .sn_beats_rcvd_o     (mshr_sn_beats),
        .sn_install_o        (mshr_sn_install),
        .merge_i             (dut_mshr_merge),
        .merge_idx_i         (dut_mshr_merge_idx),
        .merge_seq_i         (dut_mshr_merge_seq),
        .beat_i              (dut_mshr_beat),
        .beat_idx_i          (dut_mshr_beat_idx),
        .beat_num_i          (dut_mshr_beat_num),
        .sn_eff_i            (dut_mshr_sn_eff),
        .sn_eff_idx_i        (dut_mshr_sn_eff_idx),
        .sn_eff_value_i      (dut_mshr_sn_eff_value),
        .retire_i            (dut_mshr_retire),
        .retire_idx_i        (dut_mshr_retire_idx),
        .cpl_idx_i           (dut_cpl_idx),
        .cpl_line_o          (mshr_cpl_line),
        .cpl_install_o       (),
        .cpl_pend_eff_o      (mshr_cpl_pend_eff),
        .cpl_merge_seqs_o    (mshr_cpl_merge_seqs),
        .cpl_merge_count_o   (mshr_cpl_merge_count),
        .cpl_wb_slot_o       (),
        .cpl_wb_valid_o      (),
        .occupancy_o         (),
        .alloc_o             (mshr_ev_alloc),
        .alloc_set_o         (),
        .alloc_cls_o         (),
        .merge_o             (),
        .merge_idx_o         (),
        .merge_depth_o       (),
        .retire_o            (mshr_ev_retire),
        .retire_idx_o        (mshr_ev_retire_idx)
    );

    jet_wb_buffer #(
        .VICTIM_DEPTH (2),
        .LINE_W       (LINE_W),
        .ADDR_WIDTH   (32),
        .LINE_BYTES   (64),
        .BUS_WIDTH    (64)
    ) wb (
        .clk             (clk),
        .rst_n           (rst_n),
        .cap_i           (dut_wb_cap),
        .cap_line_i      (dut_wb_cap_line),
        .cap_beat_i      (dut_wb_cap_beat),
        .cap_beat_data_i (dut_wb_cap_beat_data),
        .cap_gnt_o       (wb_cap_gnt),
        .cap_slot_o      (wb_cap_slot),
        .wb_full_o       (wb_full),
        .drain_valid_o   (wb_drain_valid),
        .drain_addr_o    (),
        .drain_data_o    (),
        .drain_done_i    (drain_done),
        .sn_line_i       (dut_wb_sn_line),
        .sn_hit_o        (wb_sn_hit),
        .sn_data_o       (wb_sn_data),
        .sn_bresp_cycle_o(wb_sn_bresp_cycle),
        .sn_eff_i        (dut_wb_sn_eff),
        .wb_occupancy_o  ()
    );

    jet_rsp_seq #(
        .RSP_DEPTH (4),
        .BUS_WIDTH (64),
        .SEQ_W     (2)
    ) rsp (
        .clk        (clk),
        .rst_n      (rst_n),
        .tag_req_i  (dut_tag_req),
        .tag_gnt_o  (seq_tag_gnt),
        .tag_o      (seq_tag),
        .cpl_i      (dut_cpl_valid),
        .cpl_tag_i  (dut_cpl_tag),
        .cpl_data_i (dut_cpl_data),
        .rsp_valid_o(),
        .rsp_data_o (),
        .rsp_ready_i(rsp_ready)
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
    // Fill-engine model (the jet_top launch-adapter contract + a fair
    // single-outstanding engine; A-fill-* in the header table)
    // ------------------------------------------------------------------
    reg        r_eng_busy;
    reg        r_flight_idx;
    reg [1:0]  r_flight_cls;
    reg [3:0]  r_beat_cnt;
    reg [4:0]  r_since_accept;
    reg        r_ar_done_sh;

    wire w_eng_acceptable = dut_fill_start & ~r_eng_busy & ~dut_cap_busy
                            & ~(dut_mshr_alloc & dut_alloc_wb_valid);

    always @(posedge clk) begin
        if (!rst_n) begin
            r_eng_busy     <= 1'b0;
            r_flight_idx   <= 1'b0;
            r_flight_cls   <= CLS_RNSD;
            r_beat_cnt     <= 4'd0;
            r_since_accept <= 5'd0;
            r_ar_done_sh   <= 1'b0;
        end else if (fill_accept) begin
            r_eng_busy     <= 1'b1;
            r_flight_idx   <= obs_fill_pend ? obs_fill_idx : mshr_alloc_idx;
            r_flight_cls   <= dut_fill_cls;
            r_beat_cnt     <= 4'd0;
            r_since_accept <= 5'd0;
            r_ar_done_sh   <= 1'b0;
        end else if (r_eng_busy) begin
            if (r_since_accept != 5'h1F)
                r_since_accept <= r_since_accept + 5'd1;
            if (fill_beat_valid && (r_beat_cnt != 4'hF))
                r_beat_cnt <= r_beat_cnt + 4'd1;
            if (fill_ar_done) r_ar_done_sh <= 1'b1;
            if (fill_done)    r_eng_busy   <= 1'b0;
        end
    end

    always @(posedge clk) begin
        if (rst_n) begin
            // the launch adapter: accept combinationally iff the engine is
            // idle, no capture streams, and the cycle is not a dirty-victim
            // alloc (the exact jet_top rule)
            as_accept_exact: assume (fill_accept == w_eng_acceptable);
            // the flight: beats only in flight, only after the AR, only for
            // a data fill, in order, at most FILL_BEATS of them
            as_beat_busy: assume (!fill_beat_valid
                || (r_eng_busy && r_ar_done_sh && (r_flight_cls != CLS_CU)));
            as_beat_idx: assume (!fill_beat_valid
                || ((fill_beat_idx == r_flight_idx)
                    && (fill_beat_num == r_beat_cnt[2:0])));
            as_beat_room: assume (!fill_beat_valid || (r_beat_cnt < 4'd8));
            // done: only in flight, after the AR, with all beats (data
            // fill) or none (CU), forced within 15 cycles of the accept
            as_done_busy:  assume (!fill_done || r_eng_busy);
            as_done_rlast: assume (!fill_done
                || ((r_flight_cls == CLS_CU) ? (r_beat_cnt == 4'd0)
                                             : (r_beat_cnt == 4'd8)));
            as_done_ar:    assume (!fill_done || r_ar_done_sh);
            as_done_fair:  assume (!r_eng_busy || (r_since_accept < 5'd15)
                                   || fill_done);
            // the AR: once per flight, within 4 cycles of the accept
            as_ar_scope: assume (!fill_ar_done
                                 || (r_eng_busy && !r_ar_done_sh));
            as_ar_fair:  assume (!r_eng_busy || r_ar_done_sh
                                 || (r_since_accept < 5'd4) || fill_ar_done);
            // PassDirty is only meaningful for an RNSD flight
            as_pd_scope: assume (!(fill_done && fill_pass_dirty)
                                 || (r_flight_cls == CLS_RNSD));
        end
    end

    // ------------------------------------------------------------------
    // Drain-engine model (a fair l1_drain: done only while a drain is
    // outstanding, forced within 10 cycles of the start)
    // ------------------------------------------------------------------
    reg       r_drain_busy_sh;
    reg [3:0] f_drain_wait;
    always @(posedge clk) begin
        if (!rst_n) begin
            r_drain_busy_sh <= 1'b0;
            f_drain_wait    <= 4'd0;
        end else begin
            if (dut_drain_start) begin
                r_drain_busy_sh <= 1'b1;
                f_drain_wait    <= 4'd0;
            end else if (r_drain_busy_sh && (f_drain_wait != 4'hF)) begin
                f_drain_wait <= f_drain_wait + 4'd1;
            end
            if (drain_done) begin
                r_drain_busy_sh <= 1'b0;
                f_drain_wait    <= 4'd0;
            end
        end
    end

    always @(posedge clk) begin
        if (rst_n) begin
            as_drain_done_busy: assume (!drain_done || r_drain_busy_sh);
            as_drain_fair: assume (!r_drain_busy_sh || (f_drain_wait < 4'd10)
                                   || drain_done);
        end
    end

    // ------------------------------------------------------------------
    // CD channel (a fair manager: stall at most 1 cycle)
    // ------------------------------------------------------------------
    reg [1:0] f_cd_wait;
    always @(posedge clk) begin
        if (!rst_n) f_cd_wait <= 2'd0;
        else if (dut_sn_cdvalid && !sn_cdready) begin
            if (f_cd_wait != 2'h3) f_cd_wait <= f_cd_wait + 2'd1;
        end else f_cd_wait <= 2'd0;
    end

    always @(posedge clk) begin
        if (rst_n)
            as_cd_fair: assume (!(dut_sn_cdvalid && !sn_cdready)
                                || (f_cd_wait < 2'd1) || sn_cdready);
    end

    // ------------------------------------------------------------------
    // Snoop transport (A-snoop-transport: the peer holds want/addr/type
    // until the grant -- the ACVALID rule -- and presents only the legal
    // snoop encodings 0..5)
    // ------------------------------------------------------------------
    reg        r_sn_want_d, r_sn_gnt_d;
    reg [31:0] r_sn_addr_d;
    reg [2:0]  r_sn_type_d;
    always @(posedge clk) begin
        r_sn_want_d <= sn_want;
        r_sn_gnt_d  <= w_sn_gnt;
        r_sn_addr_d <= sn_addr;
        r_sn_type_d <= sn_type;
    end

    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 2)) begin
            as_sn_hold: assume (!(r_sn_want_d && !r_sn_gnt_d) || sn_want);
            as_sn_stable: assume (!(r_sn_want_d && !r_sn_gnt_d)
                || ((sn_addr == r_sn_addr_d) && (sn_type == r_sn_type_d)));
            as_sn_type: assume (!sn_want || (sn_type <= 3'd5));
        end
    end

    // ------------------------------------------------------------------
    // Shadow MSHR occupancy + claimed-way scoreboard, driven by the leaf's
    // own event taps (so the shadow is exactly the leaf's state).  An
    // entry's way claim lives precisely from its alloc to its retire.
    // ------------------------------------------------------------------
    reg [1:0]  sh_vld;
    reg [25:0] sh_line [0:1];
    reg [3:0]  sh_cset [0:1];
    reg        sh_cway [0:1];
    always @(posedge clk) begin
        if (!rst_n) begin
            sh_vld <= 2'b00;
        end else begin
            if (mshr_ev_alloc) begin
                sh_vld[mshr_alloc_idx]  <= 1'b1;
                sh_line[mshr_alloc_idx] <= dut_alloc_line;
                sh_cset[mshr_alloc_idx] <= dut_alloc_set;
                sh_cway[mshr_alloc_idx] <= dut_alloc_vway;
            end
            if (mshr_ev_retire) begin
                sh_vld[mshr_ev_retire_idx] <= 1'b0;
            end
        end
    end

    // ------------------------------------------------------------------
    // Independent spec copy of the HAS Table 3.0 CRRESP decode (verified
    // cell for cell against l1_pkg.amber_snoop_crresp; the formal
    // cross-check: a wiring change to the pkg function fails ap_crresp).
    // ------------------------------------------------------------------
    function [4:0] exp_crresp;
        input [2:0] state;
        input [2:0] snoop;
        reg dt, pd, is, wu;
        begin
            dt = 1'b0; pd = 1'b0; is = 1'b0; wu = 1'b0;
            case (state)
                ST_M: begin
                    case (snoop)
                        3'b000, 3'b011, 3'b100: begin dt = 1'b1; pd = 1'b1; is = 1'b1; end
                        3'b001, 3'b010:         begin dt = 1'b1; pd = 1'b1; end
                        default: ;
                    endcase
                end
                ST_E: begin
                    case (snoop)
                        3'b000, 3'b001: begin dt = 1'b1; is = 1'b1; wu = 1'b1; end
                        3'b010:         begin dt = 1'b1; wu = 1'b1; end
                        3'b011:         begin is = 1'b1; wu = 1'b1; end
                        default: ;
                    endcase
                end
                ST_S: begin
                    case (snoop)
                        3'b000, 3'b001: is = 1'b1;
                        default: ;
                    endcase
                end
                default: ;
            endcase
            exp_crresp = {wu, is, pd, 1'b0, dt};
        end
    endfunction

    // ------------------------------------------------------------------
    // Independent grant-cycle answer-source resolution (the fixed match
    // order WB > MSHR > array), against the tag MODEL's port-B read and
    // the wrapper's shadow claims -- the DUT's own w_src_* / w_sn_ref are
    // pinned against this independent computation.
    // ------------------------------------------------------------------
    wire [3:0]  f_sn_set = sn_addr[9:6];
    wire [21:0] f_sn_tag = sn_addr[31:10];
    wire [24:0] f_ts0    = tag_model[f_sn_set];
    wire [24:0] f_ts1    = tag_model[16 + f_sn_set];
    wire f_h0 = (f_ts0[24:3] == f_sn_tag)
                && ((f_ts0[2:0] == ST_S) || (f_ts0[2:0] == ST_E)
                    || (f_ts0[2:0] == ST_M));
    wire f_h1 = (f_ts1[24:3] == f_sn_tag)
                && ((f_ts1[2:0] == ST_S) || (f_ts1[2:0] == ST_E)
                    || (f_ts1[2:0] == ST_M));
    wire       f_thit   = f_h0 | f_h1;
    wire       f_tway   = f_h0 ? 1'b0 : 1'b1;   // way0 first, like the RTL loop
    wire [2:0] f_tstate = f_h0 ? f_ts0[2:0] : f_ts1[2:0];
    wire f_tclaimed =
        (sh_vld[0] && (sh_cset[0] == f_sn_set) && (sh_cway[0] == f_tway))
        || (sh_vld[1] && (sh_cset[1] == f_sn_set) && (sh_cway[1] == f_tway));

    wire f_xsrc_wb    = wb_sn_hit;
    wire f_xsrc_mshr  = ~wb_sn_hit & mshr_sn_match & ~obs_mshr_pre_ar;
    wire f_xsrc_array = ~wb_sn_hit & ~f_xsrc_mshr & f_thit & ~f_tclaimed;
    wire [2:0] f_xref = f_xsrc_wb    ? ST_M
                        : f_xsrc_mshr  ? (mshr_sn_install ? ST_M : ST_S)
                        : f_xsrc_array ? f_tstate
                        :                ST_I;

    // ------------------------------------------------------------------
    // Shadow of the pend_eff records (BUG-004): the MSHR effect record is
    // written only by dut_mshr_sn_eff pulses (already I-sticks-gated in
    // the DUT) and cleared at the alloc that reuses the entry, so this
    // shadow is exact.  The last-grant shadow tracks the service in
    // flight (grants land only at SN_IDLE -- one service at a time).
    // ------------------------------------------------------------------
    localparam [1:0] PEND_NONE  = 2'b00;
    localparam [1:0] PEND_DN_S  = 2'b01;
    localparam [1:0] PEND_INV_I = 2'b10;
    // shared-domain (non-invalidating) snoop encodings (l1_pkg)
    localparam [2:0] SN_RS = 3'b000;
    localparam [2:0] SN_RO = 3'b001;
    localparam [2:0] SN_CS = 3'b011;

    reg [1:0] sh_pend [0:1];
    reg [2:0] sh_gnt_type;
    reg       sh_gnt_idx;
    reg       sh_gnt_mshr;
    always @(posedge clk) begin
        if (!rst_n) begin
            sh_pend[0] <= PEND_NONE;
            sh_pend[1] <= PEND_NONE;
        end else begin
            // mirror the DUT's same-cycle ordering: the alloc clear wins
            if (dut_mshr_sn_eff)
                sh_pend[dut_mshr_sn_eff_idx] <= dut_mshr_sn_eff_value;
            if (mshr_ev_alloc)
                sh_pend[mshr_alloc_idx] <= PEND_NONE;
        end
    end
    always @(posedge clk) begin
        if (w_sn_gnt) begin
            sh_gnt_type <= sn_type;
            sh_gnt_idx  <= mshr_sn_match_idx;
            sh_gnt_mshr <= f_xsrc_mshr;
        end
    end

    // =========================================================================
    // Safety properties (MAS ch05/01)
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            // S5 (BUG-004): an armed downgrade-S survives a shared-domain
            // repeat snoop on the pending fill -- RS/RO/CS are fixed
            // points of the ARMED S, so the effect record for such a
            // service is never INVALIDATE_I.  (The repeat snoop chains
            // against the armed state; resolving it against the original
            // post-fill M armed I and the commit silently dropped the
            // merged store -- the Task-12 grid find.)
            ap_pend_chain: assert (!(dut_mshr_sn_eff
                                     && (dut_mshr_sn_eff_value == PEND_INV_I)
                                     && sh_gnt_mshr
                                     && (sh_gnt_idx == dut_mshr_sn_eff_idx)
                                     && (sh_pend[dut_mshr_sn_eff_idx]
                                         == PEND_DN_S)
                                     && ((sh_gnt_type == SN_RS)
                                         || (sh_gnt_type == SN_RO)
                                         || (sh_gnt_type == SN_CS))));
            // S1: the grant-cycle answer-source pins -- the fixed match
            // order WB > MSHR > array with the pre-AR suppression and the
            // claimed-way (stale-victim) suppression, all against the
            // independent resolution above
            ap_src_wb:    assert (!w_sn_gnt || (obs_src_wb == f_xsrc_wb));
            ap_src_mshr:  assert (!w_sn_gnt || (obs_src_mshr == f_xsrc_mshr));
            ap_src_array: assert (!w_sn_gnt || (obs_src_array == f_xsrc_array));
            ap_ref:       assert (!w_sn_gnt || (obs_sn_ref == f_xref));
            ap_deliver:   assert (!w_sn_gnt
                || (obs_sn_deliver == (f_xsrc_wb | f_xsrc_array
                                       | (f_xsrc_mshr & (&mshr_sn_beats)))));
            // S1: CRRESP at the grant equals the Table 3.0 decode at the
            // resolved reference state, PF_GUARD-masked when the fill has
            // not landed every beat
            ap_crresp: assert (!w_sn_gnt
                || (dut_sn_crresp
                    == (obs_sn_deliver ? exp_crresp(obs_sn_ref, sn_type)
                        : (exp_crresp(obs_sn_ref, sn_type) & CRRESP_NO_DT))));
            // BypassNeverAnswersInvalid, per entry: a pending-fill answer
            // is never at the Invalid row
            ap_bypass_never_i: assert (!(w_sn_gnt && f_xsrc_mshr)
                                       || (obs_sn_ref != ST_I));
            // PF_GUARD: without every fill beat landed, the answer carries
            // neither DataTransfer nor PassDirty
            ap_pf_guard: assert (!(w_sn_gnt && f_xsrc_mshr
                                   && !(&mshr_sn_beats))
                || ((dut_sn_crresp[0] == 1'b0) && (dut_sn_crresp[2] == 1'b0)));
            // PF_GUARD beat gating: no CD beat is presented from a pending
            // fill unless every fill beat had landed at the grant
            ap_pf_guard_svc: assert (!((obs_sn_state == SN_DATA)
                                       && (obs_sn_src == SRC_MSHR))
                                     || obs_sn_allb);
            // S3: no two valid MSHR entries share a line (merge, never
            // duplicate fetch)
            ap_no_dup_line: assert (!(sh_vld[0] && sh_vld[1]
                                      && (sh_line[0] == sh_line[1])));
            // S4: no two in-flight misses in a set claim the same way --
            // and the in-flight upgrade's way is never claimed either
            ap_no_dup_claim: assert (!(sh_vld[0] && sh_vld[1]
                                       && (sh_cset[0] == sh_cset[1])
                                       && (sh_cway[0] == sh_cway[1])));
            ap_claim_vs_upgr: assert (!(obs_upgr_valid
                && ((sh_vld[0] && (sh_cset[0] == obs_upgr_set)
                     && (sh_cway[0] == obs_upgr_way))
                    || (sh_vld[1] && (sh_cset[1] == obs_upgr_set)
                        && (sh_cway[1] == obs_upgr_way)))));
            // the DUT's claim scoreboard tracks the real occupancy
            ap_claim_shadow_eq: assert (obs_claim_vld == sh_vld);
            // integration pins (the RTL's own contract checks, re-proven
            // against the real leaves)
            ap_alloc_gnt: assert (!dut_mshr_alloc || mshr_alloc_gnt);
            ap_dirty_alloc_wb_gnt: assert (!(dut_mshr_alloc
                                             && dut_alloc_wb_valid)
                                           || wb_cap_gnt);
            ap_beat_has_claim: assert (!fill_beat_valid
                                       || obs_claim_vld[fill_beat_idx]);
            ap_retire_has_claim: assert (!dut_mshr_retire
                                         || obs_claim_vld[dut_mshr_retire_idx]);
            ap_done_has_flight: assert (!fill_done || (obs_fq_undone != 3'd0));
            // structural sanity
            ap_sn_cmt_excl: assert (!((obs_sn_state != SN_IDLE))
                                    || (obs_cmt_state == C_IDLE));
            ap_cmt_legal:   assert (obs_cmt_state <= 4'd8);
            ap_sn_legal:    assert (obs_sn_state != 2'd3);
            ap_no_error:    assert (!dut_ctrl_error);
        end
    end

    // =========================================================================
    // Cover properties -- the Step-2 reachability evidence: every stall
    // class and the composed corner must be REACHABLE at the tiny geometry
    // (a liveness proof over unreachable states is vacuous).
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            // the six J6 stall classes
            cp_stall_mshr_full: cover (dut_lkup_stall
                                       && (dut_stall_reason == STALL_MSHR_FULL));
            cp_stall_wb: cover (dut_lkup_stall
                                && (dut_stall_reason == STALL_WB));
            cp_stall_wb_race: cover (dut_lkup_stall
                                     && (dut_stall_reason == STALL_WB)
                                     && wb_sn_hit);   // the drain-race flavor
            cp_stall_set_oversub: cover (dut_lkup_stall
                                         && (dut_stall_reason == STALL_SET_OVERSUB));
            cp_stall_xclass: cover (dut_lkup_stall
                                    && (dut_stall_reason == STALL_XCLASS));
            cp_stall_tag_full: cover (dut_lkup_stall
                                      && (dut_stall_reason == STALL_TAG_FULL));
            cp_stall_commit: cover (dut_lkup_stall
                                    && (dut_stall_reason == STALL_COMMIT));
            // the composed corner itself: MSHR-full && WB-full && a snoop
            // waiting
            cp_corner: cover (mshr_full && wb_full && sn_want);
            // the three answer sources at the grant, plus the pre-AR
            // suppression and both PF_GUARD flavors
            cp_src_wb:     cover (w_sn_gnt && obs_src_wb);
            cp_src_mshr:   cover (w_sn_gnt && obs_src_mshr);
            cp_src_array:  cover (w_sn_gnt && obs_src_array);
            cp_pre_ar:     cover (w_sn_gnt && mshr_sn_match
                                  && obs_mshr_pre_ar && !wb_sn_hit);
            cp_pf_guard:   cover (w_sn_gnt && obs_src_mshr && !obs_sn_deliver);
            cp_pf_deliver: cover (w_sn_gnt && obs_src_mshr && obs_sn_deliver);
            // CD beats served from a pending fill (the bypass stream)
            cp_cd_mshr: cover ((obs_sn_state == SN_DATA)
                               && (obs_sn_src == SRC_MSHR) && dut_sn_cdvalid);
            // the upgrade path: a CU commit, and the killed-upgrade corner
            // (a pre-grant snoop invalidated the upgrade's line)
            cp_cu_commit: cover (obs_cmt_state == C_CU_INSTALL);
            cp_killed:    cover ((obs_cmt_state == C_CU_INSTALL)
                                 && obs_upgr_killed);
            // merge and write-hit yield
            cp_merge:    cover (dut_lkup_merge);
            cp_wr_yield: cover (dut_wr_yield);
            // a WB snarf answered in the entry's BRESP cycle (the
            // ships-in-the-night corner)
            cp_wb_bresp: cover (w_sn_gnt && obs_src_wb && wb_sn_bresp_cycle);
            // a retire straight out of a full MSHR file (the J6 release)
            cp_retire_full: cover (mshr_ev_retire && mshr_full);
            // BUG-004 reachability: the armed-downgrade + repeat-snoop
            // corner itself (grant on a pending fill whose shadow effect
            // is DOWNGRADE_S, with a shared-domain snoop), and the armed
            // downgrade surviving to the commit (the fill commits S)
            cp_pend_armed_s_ro: cover (w_sn_gnt && f_xsrc_mshr
                && (sh_pend[mshr_sn_match_idx] == PEND_DN_S)
                && (sn_type == SN_RO));
            cp_pend_armed_s_rs: cover (w_sn_gnt && f_xsrc_mshr
                && (sh_pend[mshr_sn_match_idx] == PEND_DN_S)
                && (sn_type == SN_RS));
        end
    end

endmodule
