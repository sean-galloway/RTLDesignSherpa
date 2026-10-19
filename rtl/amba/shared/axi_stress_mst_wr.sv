// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_stress_mst_wr
// Purpose: Write half of a bus-stress master: random legal AW bursts, their W
//          data generated from the address, every B checked against the burst
//          its ID says it belongs to.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// Drives the fub side of axi4_master_wr. A burst issued takes a slot in an
// axi_stress_ord_table keyed by AWID and an entry in the W queue; AW and W
// then run independently, so W data may reach the fabric before its AW.
//
// W: beats in AW order (no write interleaving). fub_axi_wid carries the AWID
// of the burst each beat belongs to, for an AXI3 shell; the AXI4 shell leaves
// it open. Each active byte lane carries
// f_word(beat address, tag, WR); inactive lanes carry the complement with
// their strobes low. A window with strb_rand also clears random strobes of
// active lanes, so a converter that merges or moves strobes is seen at the
// slave. Beats go out with a random bubble (data_throttle) between them.
//
// B: the handshake is registered, then BID finds the oldest burst of that ID.
// Checks: ERR_WR_STRAY, ERR_WR_EARLY (a B for a burst whose last W has not
// left this block), ERR_WR_RESP, ERR_HANG. Data is checked at the slave.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_stress_mst_wr
    import axi_stress_pkg::*;
#(
    parameter int DEPTH   = 16,
    parameter int NWIN    = 8,
    parameter int IW      = 8,
    parameter int DW      = 64,
    parameter int UW      = 1,
    parameter logic [7:0] LEN_MASK = 8'hFF,   // AxLEN limit (AXI3: 8'h0F)
    parameter int XW      = $clog2(DEPTH),
    parameter int NB      = DW / 8,
    parameter int BUS_LG2 = $clog2(NB),
    parameter int NL      = DW / 32
) (
    input  logic                aclk,
    input  logic                aresetn,

    input  logic                go,
    input  logic                stop,
    input  stress_mdir_cfg_t    cfg,
    input  stress_win_t         cfg_win [NWIN],
    input  logic [31:0]         cfg_hash_seed,
    output stress_mdir_sts_t    sts,

    // fub AW / W / B
    output logic [IW-1:0]       fub_axi_awid,
    output logic [31:0]         fub_axi_awaddr,
    output logic [7:0]          fub_axi_awlen,
    output logic [2:0]          fub_axi_awsize,
    output logic [1:0]          fub_axi_awburst,
    output logic                fub_axi_awlock,
    output logic [3:0]          fub_axi_awcache,
    output logic [2:0]          fub_axi_awprot,
    output logic [3:0]          fub_axi_awqos,
    output logic [3:0]          fub_axi_awregion,
    output logic [UW-1:0]       fub_axi_awuser,
    output logic                fub_axi_awvalid,
    input  logic                fub_axi_awready,

    output logic [DW-1:0]       fub_axi_wdata,
    output logic [NB-1:0]       fub_axi_wstrb,
    output logic [IW-1:0]       fub_axi_wid,
    output logic                fub_axi_wlast,
    output logic [UW-1:0]       fub_axi_wuser,
    output logic                fub_axi_wvalid,
    input  logic                fub_axi_wready,

    input  logic [IW-1:0]       fub_axi_bid,
    input  logic [1:0]          fub_axi_bresp,
    input  logic [UW-1:0]       fub_axi_buser,
    input  logic                fub_axi_bvalid,
    output logic                fub_axi_bready
);

    // =========================================================================
    // Run control
    // =========================================================================
    logic        r_run, r_started;
    logic [31:0] r_issued, r_completed, r_beats;
    logic [NWIN-1:0] w_win_en;
    always_comb for (int i = 0; i < NWIN; i++) w_win_en[i] = cfg_win[i].wr_en;

    logic w_done_now, w_go;
    assign w_go = go && (!r_started || w_done_now);

    logic w_budget_left;
    assign w_budget_left = (cfg.txn_count == '0) || (r_issued < cfg.txn_count);

    logic [XW:0] w_max_out;
    assign w_max_out = ((cfg.max_out == '0) || (32'(cfg.max_out) > 32'(DEPTH)))
                     ? (XW+1)'(DEPTH) : (XW+1)'(cfg.max_out);

    // =========================================================================
    // Generator
    // =========================================================================
    logic          t_valid, t_ready, t_strb_rand;
    logic [31:0]   t_addr;
    logic [7:0]    t_len, t_gap, t_tag;
    logic [2:0]    t_size;
    logic [1:0]    t_burst, t_resp;
    logic [IW-1:0] t_id;
    logic [3:0]    t_qos;

    axi_stress_txn_gen #(
        .NWIN(NWIN), .IW(IW), .BUS_LG2(BUS_LG2), .LEN_MASK(LEN_MASK),
        .SALT(32'h6A09_E667)
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
        .txn_strb_rand(t_strb_rand)
    );

    // =========================================================================
    // Outstanding table
    // =========================================================================
    logic          tb_full, tb_lk_hit, tb_retire;
    logic [XW-1:0] tb_alloc_idx, tb_lk_idx;
    logic [XW:0]   tb_count;
    logic          w_issue;

    logic          r_b_valid;
    logic [IW-1:0] r_b_id;
    logic [1:0]    r_b_resp;

    axi_stress_ord_table #(.DEPTH(DEPTH), .KW(IW)) u_tbl (
        .aclk, .aresetn,
        .clear        (w_go),
        .alloc_valid  (w_issue),
        .alloc_key    (t_id),
        .alloc_idx    (tb_alloc_idx),
        .full         (tb_full),
        .lk_key       (r_b_id),
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

    logic [1:0]       r_s_resp  [DEPTH];
    logic [15:0]      r_s_ts    [DEPTH];
    logic [DEPTH-1:0] r_s_wdone;           // the burst's last W has left

    // =========================================================================
    // W queue: one entry per issued burst, in AW order
    // =========================================================================
    localparam int WQW = XW + IW + 32 + 8 + 3 + 2 + 8 + 1;

    logic           wq_wr_ready, wq_rd_valid, wq_rd_ready;
    logic [WQW-1:0] wq_rd_data;

    gaxi_fifo_sync #(
        .REGISTERED(0), .DATA_WIDTH(WQW), .DEPTH(DEPTH)
    ) u_wq (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_issue),
        .wr_ready    (wq_wr_ready),
        .wr_data     ({tb_alloc_idx, t_id, t_addr, t_len, t_size, t_burst, t_tag, t_strb_rand}),
        .rd_ready    (wq_rd_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (wq_rd_valid),
        .rd_data     (wq_rd_data)
    );

    logic [XW-1:0] q_idx;
    logic [IW-1:0] q_id;
    logic [31:0]   q_addr;
    logic [7:0]    q_len, q_tag;
    logic [2:0]    q_size;
    logic [1:0]    q_burst;
    logic          q_srand;
    assign {q_idx, q_id, q_addr, q_len, q_size, q_burst, q_tag, q_srand} = wq_rd_data;

    // =========================================================================
    // AW issue
    // =========================================================================
    logic        r_aw_valid;
    logic [7:0]  r_gap_cnt;
    logic [15:0] r_now;

    assign w_issue = r_run && t_valid && w_budget_left && (r_gap_cnt == '0)
                  && !tb_full && (tb_count < w_max_out) && wq_wr_ready
                  && (!r_aw_valid || fub_axi_awready);
    assign t_ready = w_issue;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_aw_valid <= 1'b0;
            r_gap_cnt  <= '0;
        end else if (w_go) begin
            r_gap_cnt  <= '0;
        end else begin
            if (w_issue)              r_aw_valid <= 1'b1;
            else if (fub_axi_awready) r_aw_valid <= 1'b0;
            if (w_issue)              r_gap_cnt  <= t_gap;
            else if (r_gap_cnt != '0) r_gap_cnt  <= r_gap_cnt - 8'd1;
        end
    )

    always_ff @(posedge aclk) begin
        if (w_issue) begin
            fub_axi_awid    <= t_id;
            fub_axi_awaddr  <= t_addr;
            fub_axi_awlen   <= t_len;
            fub_axi_awsize  <= t_size;
            fub_axi_awburst <= t_burst;
            fub_axi_awqos   <= t_qos;
            r_s_resp[tb_alloc_idx] <= t_resp;
            r_s_ts  [tb_alloc_idx] <= r_now;
        end
    end

    assign fub_axi_awvalid  = r_aw_valid;
    assign fub_axi_awlock   = 1'b0;
    assign fub_axi_awcache  = 4'b0011;
    assign fub_axi_awprot   = 3'b000;
    assign fub_axi_awregion = 4'd0;
    assign fub_axi_awuser   = '0;

    // =========================================================================
    // W engine
    // =========================================================================
    logic          r_wa;                 // a burst is part-sent
    logic [XW-1:0] r_wa_idx;
    logic [IW-1:0] r_wa_id;
    logic [31:0]   r_wa_addr;
    logic [7:0]    r_wa_len, r_wa_left, r_wa_tag;
    logic [2:0]    r_wa_size;
    logic [1:0]    r_wa_burst;
    logic          r_wa_srand;

    // the beat to send: the part-sent burst, else the queue head
    logic          c_valid;
    logic [XW-1:0] c_idx;
    logic [IW-1:0] c_id;
    logic [31:0]   c_addr;
    logic [7:0]    c_len, c_left, c_tag;
    logic [2:0]    c_size;
    logic [1:0]    c_burst;
    logic          c_srand;
    always_comb begin
        c_valid = r_wa || wq_rd_valid;
        c_idx   = r_wa ? r_wa_idx   : q_idx;
        c_id    = r_wa ? r_wa_id    : q_id;
        c_addr  = r_wa ? r_wa_addr  : q_addr;
        c_len   = r_wa ? r_wa_len   : q_len;
        c_left  = r_wa ? r_wa_left  : q_len;
        c_size  = r_wa ? r_wa_size  : q_size;
        c_burst = r_wa ? r_wa_burst : q_burst;
        c_tag   = r_wa ? r_wa_tag   : q_tag;
        c_srand = r_wa ? r_wa_srand : q_srand;
    end

    logic          r_wv, r_wv_last;
    logic [XW-1:0] r_wv_idx;
    logic [31:0]   r_thr, r_sr;          // throttle (free-running), strobes (per beat)
    logic          r_wpass, r_bready;
    logic          w_wmake;
    wire           w_w_hs = r_wv && fub_axi_wready;

    assign w_wmake     = c_valid && r_wpass && (!r_wv || fub_axi_wready);
    assign wq_rd_ready = w_wmake && !r_wa;

    logic [NB-1:0] w_lanes;
    logic [DW-1:0] w_data;
    always_comb begin
        logic [BUS_LG2:0] lo, hi;
        logic [31:0]      bytes;
        logic [31:0]      word;
        bytes = 32'd1 << c_size;
        lo    = (BUS_LG2+1)'(c_addr[BUS_LG2-1:0]);
        hi    = (BUS_LG2+1)'((c_addr & ~(bytes - 32'd1)) & 32'(NB - 1))
              + (BUS_LG2+1)'(bytes) - (BUS_LG2+1)'(1);
        for (int b = 0; b < NB; b++)
            w_lanes[b] = ((BUS_LG2+1)'(b) >= lo) && ((BUS_LG2+1)'(b) <= hi);
        for (int l = 0; l < NL; l++) begin
            word = f_word({c_addr[31:BUS_LG2], BUS_LG2'(l * 4)}, cfg_hash_seed, c_tag, 1'b0);
            for (int b = 0; b < 4; b++)
                w_data[l*32 + b*8 +: 8] = w_lanes[l*4 + b] ? word[b*8 +: 8] : ~word[b*8 +: 8];
        end
    end

    // random strobe clears: a byte keeps its strobe unless two random bits
    // are both 1 (one in four), drawn from a per-beat stream
    logic [NB-1:0] w_sclr;
    always_comb begin
        logic [31:0] r;
        r = r_sr;
        for (int b = 0; b < NB; b++) begin
            if (b % 16 == 0 && b != 0) r = f_xs32(r);
            w_sclr[b] = r[(2*b) % 32] & r[(2*b + 1) % 32];
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wa      <= 1'b0;
            r_wv      <= 1'b0;
            r_thr     <= 32'h7F4A_7C15;
            r_sr      <= 32'h1;
            r_wpass   <= 1'b0;
            r_bready  <= 1'b0;
            r_s_wdone <= '0;
        end else begin
            r_thr    <= f_xs32(r_thr);
            r_wpass  <= f_pass(r_thr[3:0], cfg.data_throttle);
            r_bready <= f_pass(r_thr[7:4], cfg.resp_throttle);
            if (w_go) begin
                r_sr <= f_xs32(((cfg.seed == '0) ? 32'hC0FF_EE11 : cfg.seed) ^ 32'hBB67_AE85);
            end else if (w_wmake) begin
                r_sr <= f_xs32(r_sr);
            end
            if (w_wmake) begin
                r_wa <= (c_left != 8'd0);
                r_wv <= 1'b1;
            end else if (fub_axi_wready) begin
                r_wv <= 1'b0;
            end
            if (w_issue)                   r_s_wdone[tb_alloc_idx] <= 1'b0;
            if (w_w_hs && r_wv_last)       r_s_wdone[r_wv_idx]     <= 1'b1;
        end
    )

    always_ff @(posedge aclk) begin
        if (w_wmake) begin
            r_wa_idx      <= c_idx;
            r_wa_id       <= c_id;
            r_wa_addr     <= f_next_addr(c_addr, c_size, c_len, c_burst);
            r_wa_len      <= c_len;
            r_wa_left     <= c_left - 8'd1;
            r_wa_size     <= c_size;
            r_wa_burst    <= c_burst;
            r_wa_tag      <= c_tag;
            r_wa_srand    <= c_srand;
            r_wv_idx      <= c_idx;
            r_wv_last     <= (c_left == 8'd0);
            fub_axi_wdata <= w_data;
            fub_axi_wstrb <= w_lanes & ~(c_srand ? w_sclr : '0);
            fub_axi_wid   <= c_id;
            fub_axi_wlast <= (c_left == 8'd0);
        end
    end

    assign fub_axi_wvalid = r_wv;
    assign fub_axi_wuser  = '0;

    // =========================================================================
    // B: handshake (A), then lookup and checks (B)
    // =========================================================================
    wire w_b_hs = fub_axi_bvalid && r_bready;
    assign fub_axi_bready = r_bready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_b_valid <= 1'b0;
        else                        r_b_valid <= w_b_hs;
    )

    always_ff @(posedge aclk) begin
        if (w_b_hs) begin
            r_b_id   <= fub_axi_bid;
            r_b_resp <= fub_axi_bresp;
        end
    end

    assign tb_retire = r_b_valid && tb_lk_hit;

    logic        w_b_err;
    logic [3:0]  w_b_kind;
    logic [31:0] w_b_exp, w_b_act;
    always_comb begin
        w_b_err  = 1'b0;
        w_b_kind = 4'(ERR_WR_STRAY);
        w_b_exp  = '0;
        w_b_act  = '0;
        if (r_b_valid) begin
            if (!tb_lk_hit) begin
                w_b_err  = 1'b1;
                w_b_kind = 4'(ERR_WR_STRAY);
                w_b_act  = {30'd0, r_b_resp};
            end else if (!r_s_wdone[tb_lk_idx]) begin
                w_b_err  = 1'b1;
                w_b_kind = 4'(ERR_WR_EARLY);
            end else if (r_b_resp != r_s_resp[tb_lk_idx]) begin
                w_b_err  = 1'b1;
                w_b_kind = 4'(ERR_WR_RESP);
                w_b_exp  = {30'd0, r_s_resp[tb_lk_idx]};
                w_b_act  = {30'd0, r_b_resp};
            end
        end
    end

    // =========================================================================
    // Hang detection and status
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

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_run       <= 1'b0;
            r_started   <= 1'b0;
            r_issued    <= '0;
            r_completed <= '0;
            r_beats     <= '0;
            r_now       <= '0;
            r_idle      <= '0;
            sts         <= '0;
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
                if (w_w_hs)    r_beats     <= r_beats + 32'd1;

                if (w_b_hs || w_w_hs || tb_count == '0) r_idle <= '0;
                else if (!r_idle[31])                   r_idle <= r_idle + 32'd1;

                if (w_b_err) sts.err_mask[w_b_kind] <= 1'b1;
                if (w_hang)  sts.err_mask[ERR_HANG] <= 1'b1;
                if (w_b_err || w_hang)
                    sts.err_cnt <= (sts.err_cnt > 16'hFFFD) ? 16'hFFFF
                                 : sts.err_cnt + 16'(w_b_err) + 16'(w_hang);
                if (!sts.fe_valid) begin
                    if (w_b_err) begin
                        sts.fe_valid <= 1'b1;
                        sts.fe_kind  <= w_b_kind;
                        sts.fe_id    <= 16'(r_b_id);
                        sts.fe_addr  <= '0;
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

    assign w_done_now = !r_run && (tb_count == '0) && !r_aw_valid && !r_wv && !r_wa
                     && !wq_rd_valid && !r_b_valid;

    wire unused = ^{fub_axi_buser};

endmodule : axi_stress_mst_wr
