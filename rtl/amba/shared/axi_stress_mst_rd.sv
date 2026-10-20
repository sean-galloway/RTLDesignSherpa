// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_stress_mst_rd
// Purpose: Read half of a bus-stress master: random legal AR bursts out, every
//          R beat checked against the burst its ID says it belongs to.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// Drives the fub side of axi4_master_rd (or a protocol shell that looks like
// it). Bursts come from axi_stress_txn_gen; each one issued takes a slot in an
// axi_stress_ord_table keyed by ARID, so a returning RID finds the OLDEST
// burst of that ID -- the only one AXI lets it complete. Bursts of different
// IDs may answer in any order and interleave beat by beat; each beat is
// checked against its own burst's next beat address, so neither reordering
// nor interleaving can upset the check, and an RID that names the wrong burst
// shows up as a data error, a wrong RLAST or a stray.
//
// R pipeline (RREADY never waits on the checker):
//   A  the handshake, registered
//   B  RID lookup; RLAST and RRESP against the burst; the burst's beat
//      address steps (f_next_addr) and the slot retires on its last beat
//   C  every active byte lane against f_word(beat address, tag, RD); beats
//      of a non-OKAY window are not data-checked
//
// AXI5 sideband (SB_MASK / RSB_MASK / POISON, all off for AXI3/AXI4): ARSB is
// f_sb(ARADDR) & SB_MASK, which the shell unpacks into the request fields;
// each R beat's response sideband must echo the request's (f_rsb(ARSB) &
// RSB_MASK: RTRACE = ARTRACE) when the window says responses echo (its sb),
// else 0, and RPOISON must be f_poison(beat address, the window's rate). A miss
// is ERR_M_SB.
//
// Checks: ERR_RD_STRAY, ERR_RD_LAST, ERR_RD_RESP, ERR_RD_DATA, ERR_HANG,
// ERR_M_SB.
// The first error is captured (kind, ID, address, expected, actual) and held
// until the next GO.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_stress_mst_rd
    import axi_stress_pkg::*;
#(
    parameter int DEPTH   = 16,          // bursts in flight, 2..64
    parameter int NWIN    = 8,
    parameter int IW      = 8,
    parameter int DW      = 64,          // >= 32
    parameter int UW      = 1,
    parameter logic [7:0] LEN_MASK = 8'hFF,   // AxLEN limit (AXI3: 8'h0F)
    parameter logic [31:0] SB_MASK  = '0,  // AXI5 request sideband bits carried (SB_* layout)
    parameter logic [7:0]  RSB_MASK = '0,  // AXI5 response sideband bits carried (RSB_* layout)
    parameter bit POISON  = 1'b0,        // AXI5 RPOISON checked
    parameter int XW      = $clog2(DEPTH),
    parameter int NB      = DW / 8,
    parameter int BUS_LG2 = $clog2(NB),
    parameter int NL      = DW / 32      // 32-bit lanes
) (
    input  logic                aclk,
    input  logic                aresetn,

    input  logic                go,
    input  logic                stop,
    input  stress_mdir_cfg_t    cfg,
    input  stress_win_t         cfg_win [NWIN],
    input  logic [31:0]         cfg_hash_seed,
    output stress_mdir_sts_t    sts,

    // fub AR / R
    output logic [IW-1:0]       fub_axi_arid,
    output logic [31:0]         fub_axi_araddr,
    output logic [7:0]          fub_axi_arlen,
    output logic [2:0]          fub_axi_arsize,
    output logic [1:0]          fub_axi_arburst,
    output logic                fub_axi_arlock,
    output logic [3:0]          fub_axi_arcache,
    output logic [2:0]          fub_axi_arprot,
    output logic [3:0]          fub_axi_arqos,
    output logic [3:0]          fub_axi_arregion,
    output logic [UW-1:0]       fub_axi_aruser,
    output logic [31:0]      fub_axi_arsb,
    output logic                fub_axi_arvalid,
    input  logic                fub_axi_arready,

    input  logic [IW-1:0]       fub_axi_rid,
    input  logic [DW-1:0]       fub_axi_rdata,
    input  logic [1:0]          fub_axi_rresp,
    input  logic                fub_axi_rlast,
    input  logic [UW-1:0]       fub_axi_ruser,
    input  logic [7:0]     fub_axi_rsb,
    input  logic                fub_axi_rpoison,
    input  logic                fub_axi_rvalid,
    output logic                fub_axi_rready
);

    // =========================================================================
    // Run control
    // =========================================================================
    logic        r_run, r_started;
    logic [31:0] r_issued, r_completed, r_beats;
    logic [NWIN-1:0] w_win_en;
    always_comb for (int i = 0; i < NWIN; i++) w_win_en[i] = cfg_win[i].rd_en;

    logic w_budget_left;
    assign w_budget_left = (cfg.txn_count == '0) || (r_issued < cfg.txn_count);

    // GO is taken only while idle: restarting under traffic would drop a
    // pending ARVALID and turn the responses still in flight into strays.
    logic w_done_now, w_go;
    assign w_go = go && (!r_started || w_done_now);

    logic [XW:0] w_max_out;
    assign w_max_out = ((cfg.max_out == '0) || (32'(cfg.max_out) > 32'(DEPTH)))
                     ? (XW+1)'(DEPTH) : (XW+1)'(cfg.max_out);

    // =========================================================================
    // Generator
    // =========================================================================
    logic          t_valid, t_ready, t_strb_rand, t_sb;
    logic [3:0]    t_plg2;
    logic [31:0]   t_addr;
    logic [7:0]    t_len, t_gap, t_tag;
    logic [2:0]    t_size;
    logic [1:0]    t_burst, t_resp;
    logic [IW-1:0] t_id;
    logic [3:0]    t_qos;

    axi_stress_txn_gen #(
        .NWIN(NWIN), .IW(IW), .BUS_LG2(BUS_LG2), .LEN_MASK(LEN_MASK),
        .SALT(32'h0000_0000)
    ) u_gen (
        .aclk, .aresetn,
        .restart      (w_go),
        .run          (r_run),
        .cfg_seed     (cfg.seed),
        .cfg_id_base  (cfg.id_base),
        .cfg_id_mask  (cfg.id_mask),
        .cfg_gap_mask (cfg.gap_mask),
        .cfg_qos_rand (cfg.qos_rand),
        .cfg_win      (cfg_win),
        .cfg_win_en   (w_win_en),
        .txn_valid    (t_valid),
        .txn_ready    (t_ready),
        .txn_addr     (t_addr),
        .txn_len      (t_len),
        .txn_size     (t_size),
        .txn_burst    (t_burst),
        .txn_id       (t_id),
        .txn_qos      (t_qos),
        .txn_gap      (t_gap),
        .txn_tag      (t_tag),
        .txn_resp     (t_resp),
        .txn_strb_rand(t_strb_rand),
        .txn_sb       (t_sb),
        .txn_plg2     (t_plg2)
    );

    // =========================================================================
    // Outstanding table
    // =========================================================================
    logic          tb_full, tb_lk_hit, tb_retire;
    logic [XW-1:0] tb_alloc_idx, tb_lk_idx;
    logic [XW:0]   tb_count;
    logic          w_issue;

    logic          r_a_valid;
    logic [IW-1:0] r_a_id;

    axi_stress_ord_table #(.DEPTH(DEPTH), .KW(IW)) u_tbl (
        .aclk, .aresetn,
        .clear        (w_go),
        .alloc_valid  (w_issue),
        .alloc_key    (t_id),
        .alloc_idx    (tb_alloc_idx),
        .full         (tb_full),
        .lk_key       (r_a_id),
        .lk_hit       (tb_lk_hit),
        .lk_idx       (tb_lk_idx),
        .retire_valid (tb_retire),
        .retire_idx   (tb_lk_idx),
        /* verilator lint_off PINCONNECTEMPTY */
        .valid_vec    (),
        /* verilator lint_on PINCONNECTEMPTY */
        /* verilator lint_off PINCONNECTEMPTY */
        .head_vec     (),
        /* verilator lint_on PINCONNECTEMPTY */
        .count        (tb_count)
    );

    // Per-slot payload
    logic [31:0] r_s_addr  [DEPTH];   // next beat's address
    logic [2:0]  r_s_size  [DEPTH];
    logic [7:0]  r_s_len   [DEPTH];
    logic [1:0]  r_s_burst [DEPTH];
    logic [7:0]  r_s_left  [DEPTH];   // beats after the next one
    logic [1:0]  r_s_resp  [DEPTH];
    logic [7:0]  r_s_tag   [DEPTH];
    logic [15:0] r_s_ts    [DEPTH];
    logic [7:0]  r_s_rsb   [DEPTH];   // AXI5: the response sideband expected
    logic [3:0]  r_s_plg2  [DEPTH];   // AXI5: poison rate

    // =========================================================================
    // AR issue
    // =========================================================================
    logic        r_ar_valid;
    logic [7:0]  r_gap_cnt;
    logic [15:0] r_now;

    assign w_issue = r_run && t_valid && w_budget_left && (r_gap_cnt == '0)
                  && !tb_full && (tb_count < w_max_out)
                  && (!r_ar_valid || fub_axi_arready);
    assign t_ready = w_issue;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_ar_valid <= 1'b0;
            r_gap_cnt  <= '0;
        end else if (w_go) begin
            r_gap_cnt  <= '0;
        end else begin
            if (w_issue)              r_ar_valid <= 1'b1;
            else if (fub_axi_arready) r_ar_valid <= 1'b0;
            if (w_issue)              r_gap_cnt  <= t_gap;
            else if (r_gap_cnt != '0) r_gap_cnt  <= r_gap_cnt - 8'd1;
        end
    )

    always_ff @(posedge aclk) begin
        if (w_issue) begin
            fub_axi_arid    <= t_id;
            fub_axi_araddr  <= t_addr;
            fub_axi_arlen   <= t_len;
            fub_axi_arsize  <= t_size;
            fub_axi_arburst <= t_burst;
            fub_axi_arqos   <= t_qos;
            fub_axi_arsb    <= (SB_MASK != '0) ? (f_sb(t_addr, cfg_hash_seed) & SB_MASK) : '0;
        end
    end

    assign fub_axi_arvalid  = r_ar_valid;
    assign fub_axi_arlock   = 1'b0;
    assign fub_axi_arcache  = 4'b0011;
    assign fub_axi_arprot   = 3'b000;
    assign fub_axi_arregion = 4'd0;
    assign fub_axi_aruser   = '0;

    // =========================================================================
    // R stage A: the handshake
    // =========================================================================
    logic [31:0] r_thr;          // free-running throttle PRNG
    logic        r_rready;
    logic [DW-1:0] r_a_data;
    logic [1:0]  r_a_resp;
    logic        r_a_last;
    logic [7:0] r_a_rsb;
    logic        r_a_poison;
    wire         w_r_hs = fub_axi_rvalid && r_rready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_thr     <= 32'h2545_F491;
            r_rready  <= 1'b0;
            r_a_valid <= 1'b0;
        end else begin
            r_thr     <= f_xs32(r_thr);
            r_rready  <= f_pass(r_thr[3:0], cfg.resp_throttle);
            r_a_valid <= w_r_hs;
        end
    )

    always_ff @(posedge aclk) begin
        if (w_r_hs) begin
            r_a_id   <= fub_axi_rid;
            r_a_data <= fub_axi_rdata;
            r_a_resp <= fub_axi_rresp;
            r_a_last <= fub_axi_rlast;
            r_a_rsb    <= fub_axi_rsb;
            r_a_poison <= fub_axi_rpoison;
        end
    end

    assign fub_axi_rready = r_rready;

    // =========================================================================
    // R stage B: which burst, and its control checks
    // =========================================================================
    logic          w_b_exp_last;
    logic          w_b_err;
    logic [3:0]    w_b_kind;
    logic [31:0]   w_b_exp, w_b_act;

    assign w_b_exp_last = (r_s_left[tb_lk_idx] == 8'd0);
    assign tb_retire    = r_a_valid && tb_lk_hit && w_b_exp_last;

    always_comb begin
        w_b_err  = 1'b0;
        w_b_kind = 4'(ERR_RD_STRAY);
        w_b_exp  = '0;
        w_b_act  = '0;
        if (r_a_valid) begin
            if (!tb_lk_hit) begin
                w_b_err  = 1'b1;
                w_b_kind = 4'(ERR_RD_STRAY);
                w_b_act  = r_a_data[31:0];
            end else if (r_a_last != w_b_exp_last) begin
                w_b_err  = 1'b1;
                w_b_kind = 4'(ERR_RD_LAST);
                w_b_exp  = {31'd0, w_b_exp_last};
                w_b_act  = {31'd0, r_a_last};
            end else if (r_a_resp != r_s_resp[tb_lk_idx]) begin
                w_b_err  = 1'b1;
                w_b_kind = 4'(ERR_RD_RESP);
                w_b_exp  = {30'd0, r_s_resp[tb_lk_idx]};
                w_b_act  = {30'd0, r_a_resp};
            end
        end
    end

    always_ff @(posedge aclk) begin
        if (w_issue) begin
            r_s_addr [tb_alloc_idx] <= t_addr;
            r_s_size [tb_alloc_idx] <= t_size;
            r_s_len  [tb_alloc_idx] <= t_len;
            r_s_burst[tb_alloc_idx] <= t_burst;
            r_s_left [tb_alloc_idx] <= t_len;
            r_s_resp [tb_alloc_idx] <= t_resp;
            r_s_tag  [tb_alloc_idx] <= t_tag;
            r_s_ts   [tb_alloc_idx] <= r_now;
            r_s_rsb  [tb_alloc_idx] <= t_sb ? (f_rsb(f_sb(t_addr, cfg_hash_seed) & SB_MASK)
                                               & RSB_MASK) : '0;
            r_s_plg2 [tb_alloc_idx] <= t_plg2;
        end
        if (r_a_valid && tb_lk_hit) begin
            r_s_addr[tb_lk_idx] <= f_next_addr(r_s_addr[tb_lk_idx], r_s_size[tb_lk_idx],
                                               r_s_len[tb_lk_idx], r_s_burst[tb_lk_idx]);
            r_s_left[tb_lk_idx] <= r_s_left[tb_lk_idx] - 8'd1;
        end
    end

    // =========================================================================
    // R stage C: the data
    // =========================================================================
    logic            r_c_valid;
    logic [31:0]     r_c_addr;
    logic [2:0]      r_c_size;
    logic [7:0]      r_c_tag;
    logic [IW-1:0]   r_c_id;
    logic [DW-1:0]   r_c_data;
    logic            r_c_sv;          // AXI5: check this beat's sideband
    logic            r_c_poison;
    logic [7:0]      r_c_rsb_exp;
    logic [3:0]      r_c_plg2;
    logic [7:0] r_c_rsb;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_c_valid <= 1'b0;
            r_c_sv    <= 1'b0;
        end else begin
            r_c_valid <= r_a_valid && tb_lk_hit && (r_s_resp[tb_lk_idx] == RESP_OKAY)
                      && (r_a_resp == RESP_OKAY);
            r_c_sv    <= r_a_valid && tb_lk_hit && ((RSB_MASK != '0) || POISON);
        end
    )

    always_ff @(posedge aclk) begin
        if (r_a_valid) begin
            r_c_addr <= r_s_addr[tb_lk_idx];
            r_c_size <= r_s_size[tb_lk_idx];
            r_c_tag  <= r_s_tag[tb_lk_idx];
            r_c_id   <= r_a_id;
            r_c_data <= r_a_data;
            r_c_rsb_exp <= r_s_rsb[tb_lk_idx];
            r_c_plg2   <= r_s_plg2[tb_lk_idx];
            r_c_rsb    <= r_a_rsb;
            r_c_poison <= r_a_poison;
        end
    end

    // AXI5 response sideband and poison of the beat
    logic [7:0] w_c_rsb_exp;
    logic            w_c_p_exp, w_c_sb_err;
    assign w_c_rsb_exp = r_c_rsb_exp;
    assign w_c_p_exp   = POISON && f_poison(r_c_addr, cfg_hash_seed, r_c_plg2);
    assign w_c_sb_err  = r_c_sv && (((RSB_MASK != '0) && ((r_c_rsb & RSB_MASK) != w_c_rsb_exp))
                                 || (POISON && (r_c_poison != w_c_p_exp)));

    logic [NB-1:0]  w_c_lanes;
    logic [DW-1:0]  w_c_exp;
    logic [NL-1:0]  w_c_bad;
    logic           w_c_err;
    logic [31:0]    w_c_exp_w, w_c_act_w, w_c_addr_w;

    always_comb begin
        logic [BUS_LG2:0] lo, hi;
        logic [31:0]      bytes;
        bytes = 32'd1 << r_c_size;
        lo    = (BUS_LG2+1)'(r_c_addr[BUS_LG2-1:0]);
        hi    = (BUS_LG2+1)'((r_c_addr & ~(bytes - 32'd1)) & 32'(NB - 1))
              + (BUS_LG2+1)'(bytes) - (BUS_LG2+1)'(1);
        for (int b = 0; b < NB; b++)
            w_c_lanes[b] = ((BUS_LG2+1)'(b) >= lo) && ((BUS_LG2+1)'(b) <= hi);
        for (int l = 0; l < NL; l++)
            w_c_exp[l*32 +: 32] = f_word({r_c_addr[31:BUS_LG2], BUS_LG2'(l * 4)},
                                         cfg_hash_seed, r_c_tag, 1'b1);
        for (int l = 0; l < NL; l++) begin
            w_c_bad[l] = 1'b0;
            for (int b = 0; b < 4; b++)
                if (w_c_lanes[l*4 + b] &&
                    (w_c_exp[l*32 + b*8 +: 8] != r_c_data[l*32 + b*8 +: 8]))
                    w_c_bad[l] = 1'b1;
        end
        w_c_err    = r_c_valid && (|w_c_bad);
        w_c_exp_w  = '0;
        w_c_act_w  = '0;
        w_c_addr_w = '0;
        for (int l = NL - 1; l >= 0; l--) begin
            if (w_c_bad[l]) begin
                w_c_exp_w  = w_c_exp[l*32 +: 32];
                w_c_act_w  = r_c_data[l*32 +: 32];
                w_c_addr_w = {r_c_addr[31:BUS_LG2], BUS_LG2'(l * 4)};
            end
        end
    end

    // =========================================================================
    // Hang detection
    // =========================================================================
    logic [31:0] r_idle;
    logic        w_hang;

    // Issue-to-retire latency, modulo 2^16. A 16-bit wire on purpose: inside
    // a 32'() cast the subtraction is context-sized, and Vivado extends both
    // stamps to 32 bits first -- a wrapped stamp then reads ~4 billion and
    // saturates LAT_SUM on the board, while Verilator computed it at 16 bits.
    logic [15:0] w_lat;
    assign w_lat = r_now - r_s_ts[tb_lk_idx];
    assign w_hang = (cfg.timeout_lg2 != '0) && r_idle[cfg.timeout_lg2]
                 && !sts.err_mask[ERR_HANG];

    // =========================================================================
    // Status
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_run        <= 1'b0;
            r_started    <= 1'b0;
            r_issued     <= '0;
            r_completed  <= '0;
            r_beats      <= '0;
            r_now        <= '0;
            r_idle       <= '0;
            sts          <= '0;
        end else begin
            r_now <= r_now + 16'd1;
            if (w_go) begin
                r_run       <= cfg.enable && (|w_win_en);
                r_started   <= 1'b1;
                r_issued    <= '0;
                r_completed <= '0;
                r_beats     <= '0;
                r_idle      <= '0;
                sts         <= '0;
                sts.runs    <= sts.runs + 8'd1;
            end else begin
                if (stop || (w_issue && (cfg.txn_count != '0)
                             && (r_issued + 32'd1 >= cfg.txn_count)))
                    r_run <= 1'b0;
                if (w_issue)   r_issued    <= r_issued + 32'd1;
                if (tb_retire) r_completed <= r_completed + 32'd1;
                if (w_r_hs)    r_beats     <= r_beats + 32'd1;

                if (w_r_hs || tb_count == '0) r_idle <= '0;
                else if (!r_idle[31])         r_idle <= r_idle + 32'd1;

                // errors: the older beat (stage C) is captured first
                if (w_c_err)    sts.err_mask[ERR_RD_DATA] <= 1'b1;
                if (w_c_sb_err) sts.err_mask[ERR_M_SB]    <= 1'b1;
                if (w_b_err)    sts.err_mask[w_b_kind]    <= 1'b1;
                if (w_hang)     sts.err_mask[ERR_HANG]    <= 1'b1;
                if (w_c_err || w_c_sb_err || w_b_err || w_hang) begin
                    sts.err_cnt <= (sts.err_cnt > 16'hFFFB) ? 16'hFFFF
                                 : sts.err_cnt + 16'(w_c_err) + 16'(w_c_sb_err)
                                   + 16'(w_b_err) + 16'(w_hang);
                end
                if (!sts.fe_valid) begin
                    if (w_c_err) begin
                        sts.fe_valid <= 1'b1;
                        sts.fe_kind  <= 4'(ERR_RD_DATA);
                        sts.fe_id    <= 16'(r_c_id);
                        sts.fe_addr  <= w_c_addr_w;
                        sts.fe_exp   <= w_c_exp_w;
                        sts.fe_act   <= w_c_act_w;
                    end else if (w_c_sb_err) begin
                        sts.fe_valid <= 1'b1;
                        sts.fe_kind  <= 4'(ERR_M_SB);
                        sts.fe_id    <= 16'(r_c_id);
                        sts.fe_addr  <= r_c_addr;
                        sts.fe_exp   <= {w_c_p_exp,  31'(w_c_rsb_exp)};
                        sts.fe_act   <= {r_c_poison, 31'(r_c_rsb)};
                    end else if (w_b_err) begin
                        sts.fe_valid <= 1'b1;
                        sts.fe_kind  <= w_b_kind;
                        sts.fe_id    <= 16'(r_a_id);
                        sts.fe_addr  <= tb_lk_hit ? r_s_addr[tb_lk_idx] : 32'd0;
                        sts.fe_exp   <= w_b_exp;
                        sts.fe_act   <= w_b_act;
                    end else if (w_hang) begin
                        sts.fe_valid <= 1'b1;
                        sts.fe_kind  <= 4'(ERR_HANG);
                        sts.fe_id    <= '0;
                        sts.fe_addr  <= '0;
                        sts.fe_exp   <= '0;
                        sts.fe_act   <= 32'(tb_count);
                    end
                end

                if (tb_retire) begin
                    if (w_lat > sts.lat_max) sts.lat_max <= w_lat;
                    sts.lat_sum <= (sts.lat_sum > 32'hFFFE_FFFF) ? 32'hFFFF_FFFF
                                 : sts.lat_sum + 32'(w_lat);
                end
                if (8'(tb_count) > sts.out_max) sts.out_max <= 8'(tb_count);
            end
            sts.issued    <= w_go ? 32'd0 : r_issued;
            sts.completed <= w_go ? 32'd0 : r_completed;
            sts.beats     <= w_go ? 32'd0 : r_beats;
            sts.out_now   <= 8'(tb_count);
            sts.busy      <= r_started && !w_done_now;
            sts.done      <= r_started && w_done_now;
        end
    )

    assign w_done_now = !r_run && (tb_count == '0) && !r_ar_valid
                     && !r_a_valid && !r_c_valid && !r_c_sv;

    wire unused = ^{fub_axi_ruser, t_strb_rand};

endmodule : axi_stress_mst_rd
