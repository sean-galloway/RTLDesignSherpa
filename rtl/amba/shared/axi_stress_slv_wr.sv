// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_stress_slv_wr
// Purpose: Write half of a bus-stress slave: accepts AW bursts, checks every
//          strobed byte of W against the data its address implies, and
//          answers B in whatever order its configuration allows.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// Sits on the fub side of axi4_slave_wr.
//
// AW: accepted into an in-order queue while the queue and the bursts awaiting
// B together stay under max_out (so a burst's B always has a slot);
// AWREADY also drops at random (req_throttle). The same registered checks as
// the read side: ERR_S_ADDR, ERR_S_PROTO.
//
// W: beats belong to the AW at the head of the queue (AXI4 W order is AW
// order). WREADY waits for that AW -- a slave may -- and drops at random
// (data_throttle). Each beat is registered and checked the cycle after:
//   ERR_S_WDATA  a strobed byte differs from f_word(beat address, tag, WR)
//   ERR_S_WSTRB  a strobe on a byte outside the beat's lanes
//   ERR_S_WLAST  WLAST on the wrong beat (the burst ends on its AWLEN count)
//   ERR_S_WID    (CHECK_WID, AXI3) WID is not the AWID of the burst the beat
//                belongs to -- write interleaving or a mis-stamped WID
//
// B: a finished burst waits lat_min + random & lat_mask cycles, then answers
// once it is the oldest of its ID (all IDs as one with cfg.inorder); among
// those the scheduler picks at random.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_stress_slv_wr
    import axi_stress_pkg::*;
#(
    parameter int DEPTH   = 16,
    parameter int IW      = 8,
    parameter int DW      = 64,
    parameter int UW      = 1,
    parameter bit CHECK_WID = 1'b0,   // AXI3 shell: check fub_axi_wid
    parameter int XW      = $clog2(DEPTH),
    parameter int NB      = DW / 8,
    parameter int BUS_LG2 = $clog2(NB),
    parameter int NL      = DW / 32
) (
    input  logic                aclk,
    input  logic                aresetn,

    input  logic                clear,
    input  stress_sdir_cfg_t    cfg,
    input  logic [31:0]         cfg_hash_seed,
    output stress_sdir_sts_t    sts,

    input  logic [IW-1:0]       fub_axi_awid,
    input  logic [31:0]         fub_axi_awaddr,
    input  logic [7:0]          fub_axi_awlen,
    input  logic [2:0]          fub_axi_awsize,
    input  logic [1:0]          fub_axi_awburst,
    input  logic                fub_axi_awlock,
    input  logic [3:0]          fub_axi_awcache,
    input  logic [2:0]          fub_axi_awprot,
    input  logic [3:0]          fub_axi_awqos,
    input  logic [3:0]          fub_axi_awregion,
    input  logic [UW-1:0]       fub_axi_awuser,
    input  logic                fub_axi_awvalid,
    output logic                fub_axi_awready,

    input  logic [DW-1:0]       fub_axi_wdata,
    input  logic [NB-1:0]       fub_axi_wstrb,
    input  logic [IW-1:0]       fub_axi_wid,
    input  logic                fub_axi_wlast,
    input  logic [UW-1:0]       fub_axi_wuser,
    input  logic                fub_axi_wvalid,
    output logic                fub_axi_wready,

    output logic [IW-1:0]       fub_axi_bid,
    output logic [1:0]          fub_axi_bresp,
    output logic [UW-1:0]       fub_axi_buser,
    output logic                fub_axi_bvalid,
    input  logic                fub_axi_bready
);

    logic [XW:0] w_max_out;
    assign w_max_out = ((cfg.max_out == '0) || (32'(cfg.max_out) > 32'(DEPTH)))
                     ? (XW+1)'(DEPTH) : (XW+1)'(cfg.max_out);

    logic [31:0] r_thr, r_rnd;
    logic        r_awready, r_wpass;

    // =========================================================================
    // AW queue
    // =========================================================================
    localparam int AQW = IW + 32 + 8 + 3 + 2 + 2;

    logic           aq_wr_ready, aq_rd_valid, aq_rd_ready, w_aw_hs;
    logic [AQW-1:0] aq_rd_data;
    logic [XW:0]    tb_count;
    // Bursts held, AW accepted to B sent. Registered: gaxi_fifo_sync's count
    // is combinational on this cycle's write, so gating AWREADY with it loops.
    logic [XW:0]    r_held;

    logic [31:0] w_faddr;
    assign w_faddr = cfg.offset_mode
                   ? ((cfg.size_lg2 < 6'd32)
                      ? ((cfg.base & ~((32'd1 << cfg.size_lg2) - 32'd1))
                         | (fub_axi_awaddr & ((32'd1 << cfg.size_lg2) - 32'd1)))
                      : fub_axi_awaddr)
                   : fub_axi_awaddr;

    logic [1:0] w_aw_resp;
    assign w_aw_resp = (cfg.err_en && ((w_faddr & cfg.err_mask) == cfg.err_base))
                     ? RESP_SLVERR : RESP_OKAY;

    assign fub_axi_awready = r_awready && aq_wr_ready && (r_held < w_max_out);
    assign w_aw_hs = fub_axi_awvalid && fub_axi_awready;

    gaxi_fifo_sync #(
        .REGISTERED(0), .DATA_WIDTH(AQW), .DEPTH(DEPTH)
    ) u_aq (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_aw_hs),
        .wr_ready    (aq_wr_ready),
        .wr_data     ({fub_axi_awid, w_faddr, fub_axi_awlen, fub_axi_awsize,
                       fub_axi_awburst, w_aw_resp}),
        .rd_ready    (aq_rd_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (aq_rd_valid),
        .rd_data     (aq_rd_data)
    );

    logic [IW-1:0] q_id;
    logic [31:0]   q_addr;
    logic [7:0]    q_len;
    logic [2:0]    q_size;
    logic [1:0]    q_burst, q_resp;
    assign {q_id, q_addr, q_len, q_size, q_burst, q_resp} = aq_rd_data;

    // registered request checks
    logic          r_q_valid, r_q_win;
    logic [IW-1:0] r_q_id;
    logic [31:0]   r_q_addr;
    logic [7:0]    r_q_len;
    logic [2:0]    r_q_size;
    logic [1:0]    r_q_burst;

    logic w_in_win;
    assign w_in_win = (cfg.size_lg2 >= 6'd32) ? 1'b1
                    : cfg.offset_mode
                      ? ((fub_axi_awaddr >> cfg.size_lg2) == '0)
                      : (((fub_axi_awaddr ^ cfg.base) >> cfg.size_lg2) == '0);

    always_ff @(posedge aclk) begin
        if (w_aw_hs) begin
            r_q_win   <= w_in_win;
            r_q_id    <= fub_axi_awid;
            r_q_addr  <= fub_axi_awaddr;
            r_q_len   <= fub_axi_awlen;
            r_q_size  <= fub_axi_awsize;
            r_q_burst <= fub_axi_awburst;
        end
    end

    logic w_q_addr_err, w_q_proto_err;
    assign w_q_addr_err  = r_q_valid && !r_q_win;
    assign w_q_proto_err = r_q_valid && f_burst_illegal(r_q_addr, r_q_len, r_q_size,
                                                        r_q_burst, 3'(BUS_LG2));

    // =========================================================================
    // W
    // =========================================================================
    logic          r_wa;                  // a burst is part-received
    logic [IW-1:0] r_wa_id;
    logic [31:0]   r_wa_addr;
    logic [7:0]    r_wa_len, r_wa_left;
    logic [2:0]    r_wa_size;
    logic [1:0]    r_wa_burst, r_wa_resp;

    logic          c_valid;
    logic [IW-1:0] c_id;
    logic [31:0]   c_addr;
    logic [7:0]    c_len, c_left;
    logic [2:0]    c_size;
    logic [1:0]    c_burst, c_resp;
    always_comb begin
        c_valid = r_wa || aq_rd_valid;
        c_id    = r_wa ? r_wa_id    : q_id;
        c_addr  = r_wa ? r_wa_addr  : q_addr;
        c_len   = r_wa ? r_wa_len   : q_len;
        c_left  = r_wa ? r_wa_left  : q_len;
        c_size  = r_wa ? r_wa_size  : q_size;
        c_burst = r_wa ? r_wa_burst : q_burst;
        c_resp  = r_wa ? r_wa_resp  : q_resp;
    end

    logic tb_full, w_b_push;
    assign fub_axi_wready = c_valid && r_wpass;
    wire   w_w_hs         = fub_axi_wvalid && fub_axi_wready;
    assign aq_rd_ready    = w_w_hs && !r_wa;
    assign w_b_push       = w_w_hs && (c_left == 8'd0);

    always_ff @(posedge aclk) begin
        if (w_w_hs) begin
            r_wa_id    <= c_id;
            r_wa_addr  <= f_next_addr(c_addr, c_size, c_len, c_burst);
            r_wa_len   <= c_len;
            r_wa_left  <= c_left - 8'd1;
            r_wa_size  <= c_size;
            r_wa_burst <= c_burst;
            r_wa_resp  <= c_resp;
        end
    end

    // check stage
    logic          r_c_valid, r_c_last, r_c_exp_last;
    logic [IW-1:0] r_c_id, r_c_wid;
    logic [31:0]   r_c_addr;
    logic [2:0]    r_c_size;
    logic [DW-1:0] r_c_data;
    logic [NB-1:0] r_c_strb;

    always_ff @(posedge aclk) begin
        if (w_w_hs) begin
            r_c_id       <= c_id;
            r_c_wid      <= fub_axi_wid;
            r_c_addr     <= c_addr;
            r_c_size     <= c_size;
            r_c_data     <= fub_axi_wdata;
            r_c_strb     <= fub_axi_wstrb;
            r_c_last     <= fub_axi_wlast;
            r_c_exp_last <= (c_left == 8'd0);
        end
    end

    logic [NB-1:0] w_c_lanes;
    logic [NL-1:0] w_c_bad;
    logic          w_c_data_err, w_c_strb_err, w_c_last_err, w_c_wid_err;
    logic [31:0]   w_c_exp_w, w_c_act_w, w_c_addr_w;

    always_comb begin
        logic [BUS_LG2:0] lo, hi;
        logic [31:0]      bytes, word;
        logic [DW-1:0]    exp;
        bytes = 32'd1 << r_c_size;
        lo    = (BUS_LG2+1)'(r_c_addr[BUS_LG2-1:0]);
        hi    = (BUS_LG2+1)'((r_c_addr & ~(bytes - 32'd1)) & 32'(NB - 1))
              + (BUS_LG2+1)'(bytes) - (BUS_LG2+1)'(1);
        for (int b = 0; b < NB; b++)
            w_c_lanes[b] = ((BUS_LG2+1)'(b) >= lo) && ((BUS_LG2+1)'(b) <= hi);
        for (int l = 0; l < NL; l++) begin
            word = f_word({r_c_addr[31:BUS_LG2], BUS_LG2'(l * 4)}, cfg_hash_seed, cfg.tag, 1'b0);
            exp[l*32 +: 32] = word;
            w_c_bad[l] = 1'b0;
            for (int b = 0; b < 4; b++)
                if (r_c_strb[l*4 + b] && w_c_lanes[l*4 + b] &&
                    (word[b*8 +: 8] != r_c_data[l*32 + b*8 +: 8]))
                    w_c_bad[l] = 1'b1;
        end
        w_c_data_err = r_c_valid && (|w_c_bad);
        w_c_strb_err = r_c_valid && (|(r_c_strb & ~w_c_lanes));
        w_c_last_err = r_c_valid && (r_c_last != r_c_exp_last);
        w_c_wid_err  = CHECK_WID && r_c_valid && (r_c_wid != r_c_id);
        w_c_exp_w  = '0;
        w_c_act_w  = '0;
        w_c_addr_w = r_c_addr;
        for (int l = NL - 1; l >= 0; l--) begin
            if (w_c_bad[l]) begin
                w_c_exp_w  = exp[l*32 +: 32];
                w_c_act_w  = r_c_data[l*32 +: 32];
                w_c_addr_w = {r_c_addr[31:BUS_LG2], BUS_LG2'(l * 4)};
            end
        end
        if (!(|w_c_bad)) begin
            w_c_exp_w = w_c_strb_err ? 32'(w_c_lanes)
                      : w_c_last_err ? {31'd0, r_c_exp_last} : 32'(r_c_id);
            w_c_act_w = w_c_strb_err ? 32'(r_c_strb)
                      : w_c_last_err ? {31'd0, r_c_last}     : 32'(r_c_wid);
        end
    end

    // =========================================================================
    // B
    // =========================================================================
    logic             tb_retire;
    logic [XW-1:0]    tb_alloc_idx, w_pick_idx;
    logic [DEPTH-1:0] tb_valid, tb_head;

    axi_stress_ord_table #(.DEPTH(DEPTH), .KW(IW)) u_tbl (
        .aclk, .aresetn,
        .clear        (1'b0),
        .alloc_valid  (w_b_push),
        .alloc_key    (cfg.inorder ? IW'(0) : c_id),
        .alloc_idx    (tb_alloc_idx),
        .full         (tb_full),
        .lk_key       ('0),
        /* verilator lint_off PINCONNECTEMPTY */
        .lk_hit       (),
        /* verilator lint_on PINCONNECTEMPTY */
        /* verilator lint_off PINCONNECTEMPTY */
        .lk_idx       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .retire_valid (tb_retire),
        .retire_idx   (w_pick_idx),
        .valid_vec    (tb_valid),
        .head_vec     (tb_head),
        .count        (tb_count)
    );

    logic [IW-1:0] r_s_id   [DEPTH];
    logic [1:0]    r_s_resp [DEPTH];
    logic [8:0]    r_s_dly  [DEPTH];

    logic [8:0] w_dly;
    assign w_dly = 9'(cfg.lat_min) + 9'(r_rnd[7:0] & cfg.lat_mask);

    always_ff @(posedge aclk) begin
        for (int i = 0; i < DEPTH; i++)
            if (r_s_dly[i] != '0 && !(w_b_push && tb_alloc_idx == XW'(i)))
                r_s_dly[i] <= r_s_dly[i] - 9'd1;
        if (w_b_push) begin
            r_s_id  [tb_alloc_idx] <= c_id;
            r_s_resp[tb_alloc_idx] <= c_resp;
            r_s_dly [tb_alloc_idx] <= w_dly;
        end
    end

    logic [DEPTH-1:0] w_elig;
    logic             w_have;
    always_comb begin
        for (int i = 0; i < DEPTH; i++)
            w_elig[i] = tb_valid[i] && tb_head[i] && (r_s_dly[i] == '0);
        w_pick_idx = '0;
        w_have     = 1'b0;
        for (int k = DEPTH - 1; k >= 0; k--) begin
            if (w_elig[XW'(int'(r_rnd[31:24]) + k)]) begin
                w_pick_idx = XW'(int'(r_rnd[31:24]) + k);
                w_have     = 1'b1;
            end
        end
    end

    logic r_bv;
    logic w_bmake;
    assign w_bmake   = w_have && (!r_bv || fub_axi_bready);
    assign tb_retire = w_bmake;

    always_ff @(posedge aclk) begin
        if (w_bmake) begin
            fub_axi_bid   <= r_s_id[w_pick_idx];
            fub_axi_bresp <= r_s_resp[w_pick_idx];
        end
    end

    assign fub_axi_bvalid = r_bv;
    assign fub_axi_buser  = '0;

    // =========================================================================
    // Sequential control and status
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_thr     <= 32'h510E_527F;
            r_rnd     <= 32'h1;
            r_awready <= 1'b0;
            r_wpass   <= 1'b0;
            r_wa      <= 1'b0;
            r_bv      <= 1'b0;
            r_q_valid <= 1'b0;
            r_c_valid <= 1'b0;
            r_held    <= '0;
        end else begin
            r_held    <= r_held + (XW+1)'(w_aw_hs) - (XW+1)'(tb_retire);
            r_thr     <= f_xs32(r_thr);
            r_rnd     <= clear ? f_xs32((cfg.seed == '0) ? 32'h9B05_688C : cfg.seed)
                               : f_xs32(r_rnd);
            r_awready <= f_pass(r_thr[3:0], cfg.req_throttle);
            r_wpass   <= f_pass(r_thr[7:4], cfg.data_throttle);
            r_q_valid <= w_aw_hs;
            r_c_valid <= w_w_hs;
            if (w_w_hs) r_wa <= (c_left != 8'd0);
            if (w_bmake)             r_bv <= 1'b1;
            else if (fub_axi_bready) r_bv <= 1'b0;
        end
    )

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            sts <= '0;
        end else if (clear) begin
            sts      <= '0;
            sts.runs <= sts.runs + 8'd1;
        end else begin
            if (w_aw_hs) sts.bursts <= sts.bursts + 32'd1;
            if (w_w_hs)  sts.beats  <= sts.beats + 32'd1;
            if (w_q_addr_err)  sts.err_mask[ERR_S_ADDR]  <= 1'b1;
            if (w_q_proto_err) sts.err_mask[ERR_S_PROTO] <= 1'b1;
            if (w_c_data_err)  sts.err_mask[ERR_S_WDATA] <= 1'b1;
            if (w_c_strb_err)  sts.err_mask[ERR_S_WSTRB] <= 1'b1;
            if (w_c_last_err)  sts.err_mask[ERR_S_WLAST] <= 1'b1;
            if (w_c_wid_err)   sts.err_mask[ERR_S_WID]   <= 1'b1;
            if (w_q_addr_err || w_q_proto_err || w_c_data_err || w_c_strb_err || w_c_last_err
                || w_c_wid_err)
                sts.err_cnt <= (sts.err_cnt > 16'hFFF9) ? 16'hFFFF
                             : sts.err_cnt + 16'(w_q_addr_err) + 16'(w_q_proto_err)
                               + 16'(w_c_data_err) + 16'(w_c_strb_err) + 16'(w_c_last_err)
                               + 16'(w_c_wid_err);
            if (!sts.fe_valid) begin
                if (w_c_data_err || w_c_strb_err || w_c_last_err || w_c_wid_err) begin
                    sts.fe_valid <= 1'b1;
                    sts.fe_kind  <= w_c_data_err ? 4'(ERR_S_WDATA)
                                  : w_c_strb_err ? 4'(ERR_S_WSTRB)
                                  : w_c_last_err ? 4'(ERR_S_WLAST) : 4'(ERR_S_WID);
                    sts.fe_id    <= 16'(r_c_id);
                    sts.fe_addr  <= w_c_addr_w;
                    sts.fe_exp   <= w_c_exp_w;
                    sts.fe_act   <= w_c_act_w;
                end else if (w_q_addr_err || w_q_proto_err) begin
                    sts.fe_valid <= 1'b1;
                    sts.fe_kind  <= w_q_addr_err ? 4'(ERR_S_ADDR) : 4'(ERR_S_PROTO);
                    sts.fe_id    <= 16'(r_q_id);
                    sts.fe_addr  <= r_q_addr;
                    sts.fe_exp   <= 32'({r_q_size, r_q_len});
                    sts.fe_act   <= {30'd0, r_q_burst};
                end
            end
            sts.out_now <= 8'(r_held);
            if (8'(r_held) > sts.out_max) sts.out_max <= 8'(r_held);
        end
    )

    wire unused = ^{fub_axi_awlock, fub_axi_awcache, fub_axi_awprot, fub_axi_awqos,
                    fub_axi_awregion, fub_axi_awuser, fub_axi_wuser, fub_axi_wid, tb_full};

endmodule : axi_stress_slv_wr
