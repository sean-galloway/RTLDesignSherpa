// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_stress_slv_rd
// Purpose: Read half of a bus-stress slave: accepts AR bursts, checks them,
//          and answers with address-derived data in whatever order and
//          interleaving its configuration allows.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// Sits on the fub side of axi4_slave_rd. Stateless as a memory: an R beat is
// f_word(beat address, cfg.tag, RD) on every 32-bit lane, so no write has to
// come first and any number of masters can read any address.
//
// AR: accepted while fewer than max_out bursts are held (ARREADY also drops
// at random, req_throttle). Each one is checked, registered, a cycle later:
//   ERR_S_ADDR   outside the window (base / size_lg2; with offset_mode the
//                port carries an offset into the window, as an APB slave port
//                does, and the fabric address is rebuilt as base | offset)
//   ERR_S_PROTO  f_burst_illegal
// and gets a response code (SLVERR inside the error range, else OKAY) and a
// latency: lat_min + random & lat_mask cycles before it may answer.
//
// R: the held bursts are kept per ID in arrival order (axi_stress_ord_table;
// key = ARID, or 0 with cfg.inorder, which makes every burst wait for the one
// before it). A burst may answer once its latency has run out and it is the
// oldest of its ID. Among those, the scheduler picks at random; with
// cfg.interleave it picks again for every beat, so beats of different IDs
// interleave, otherwise it stays on one burst to RLAST. data_throttle puts
// random bubbles between beats.
//
// AXI5 sideband (SB_MASK / RSB_MASK / POISON, all off for AXI3/AXI4): ARSB must be
// f_sb(fabric address) & SB_MASK when the request came from a master in
// cfg.sb_src -- the master index is the fabric's ID prefix, ID[SRC_LSB +:
// SRC_W] -- and 0 from any other (ERR_S_SB). Each R beat echoes the
// burst's request sideband (f_rsb(ARSB) & RSB_MASK: RTRACE = ARTRACE) and
// carries RPOISON = f_poison(beat address, cfg.poison_lg2).
//
// AXI5 IDUNQ (UNIQUE): an ARIDUNQ request whose ID already has a burst held,
// or any request on an ID whose held burst is unique, is ERR_S_SB; RIDUNQ
// echoes the burst's ARIDUNQ.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_stress_slv_rd
    import axi_stress_pkg::*;
#(
    parameter int DEPTH   = 16,
    parameter int IW      = 8,
    parameter int DW      = 64,
    parameter int UW      = 1,
    parameter logic [31:0] SB_MASK  = '0,  // AXI5 request sideband bits carried (SB_* layout)
    parameter logic [7:0]  RSB_MASK = '0,  // AXI5 response sideband bits carried (RSB_* layout)
    parameter bit POISON  = 1'b0,        // AXI5 RPOISON driven
    parameter bit UNIQUE  = 1'b0,        // AXI5 ARIDUNQ checked, RIDUNQ echoed
    parameter int SRC_LSB = 0,           // master-index field of the ID
    parameter int SRC_W   = 0,           //   (0: one master, index 0)
    parameter int XW      = $clog2(DEPTH),
    parameter int NB      = DW / 8,
    parameter int BUS_LG2 = $clog2(NB),
    parameter int NL      = DW / 32
) (
    input  logic                aclk,
    input  logic                aresetn,

    input  logic                clear,          // zero the status (GO)
    input  stress_sdir_cfg_t    cfg,
    input  logic [31:0]         cfg_hash_seed,
    output stress_sdir_sts_t    sts,

    input  logic [IW-1:0]       fub_axi_arid,
    input  logic [31:0]         fub_axi_araddr,
    input  logic [7:0]          fub_axi_arlen,
    input  logic [2:0]          fub_axi_arsize,
    input  logic [1:0]          fub_axi_arburst,
    input  logic                fub_axi_arlock,
    input  logic [3:0]          fub_axi_arcache,
    input  logic [2:0]          fub_axi_arprot,
    input  logic [3:0]          fub_axi_arqos,
    input  logic [3:0]          fub_axi_arregion,
    input  logic [UW-1:0]       fub_axi_aruser,
    input  logic [31:0]      fub_axi_arsb,
    input  logic                fub_axi_aridunq,
    input  logic                fub_axi_arvalid,
    output logic                fub_axi_arready,

    output logic [IW-1:0]       fub_axi_rid,
    output logic [DW-1:0]       fub_axi_rdata,
    output logic [1:0]          fub_axi_rresp,
    output logic                fub_axi_rlast,
    output logic [UW-1:0]       fub_axi_ruser,
    output logic [7:0]     fub_axi_rsb,
    output logic                fub_axi_rpoison,
    output logic                fub_axi_ridunq,
    output logic                fub_axi_rvalid,
    input  logic                fub_axi_rready
);

    logic [XW:0] w_max_out;
    assign w_max_out = ((cfg.max_out == '0) || (32'(cfg.max_out) > 32'(DEPTH)))
                     ? (XW+1)'(DEPTH) : (XW+1)'(cfg.max_out);

    // =========================================================================
    // Held bursts
    // =========================================================================
    logic             tb_full, tb_retire, w_ar_hs;
    logic [XW-1:0]    tb_alloc_idx, w_pick_idx;
    logic [XW:0]      tb_count;
    logic [DEPTH-1:0] tb_valid, tb_head;
    logic             r_rv, w_rmake;      // R output register; a beat is made

    axi_stress_ord_table #(.DEPTH(DEPTH), .KW(IW)) u_tbl (
        .aclk, .aresetn,
        .clear        (1'b0),
        .alloc_valid  (w_ar_hs),
        .alloc_key    (cfg.inorder ? IW'(0) : fub_axi_arid),
        .alloc_idx    (tb_alloc_idx),
        /* verilator lint_off PINCONNECTEMPTY */
        .alloc_tail_vec (),
        /* verilator lint_on PINCONNECTEMPTY */
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

    logic [IW-1:0] r_s_id    [DEPTH];
    logic [31:0]   r_s_addr  [DEPTH];      // next beat, fabric address
    logic [2:0]    r_s_size  [DEPTH];
    logic [7:0]    r_s_len   [DEPTH];
    logic [1:0]    r_s_burst [DEPTH];
    logic [7:0]    r_s_left  [DEPTH];
    logic [1:0]    r_s_resp  [DEPTH];
    logic [8:0]    r_s_dly   [DEPTH];      // cycles until it may answer
    logic [7:0]    r_s_rsb   [DEPTH];      // AXI5: the response sideband echo
    logic [DEPTH-1:0] r_s_uq;              // AXI5: accepted with ARIDUNQ

    // =========================================================================
    // AR accept
    // =========================================================================
    logic [31:0] r_thr, r_rnd;
    logic        r_arready, r_rpass;

    assign fub_axi_arready = r_arready && !tb_full && (tb_count < w_max_out);
    assign w_ar_hs         = fub_axi_arvalid && fub_axi_arready;

    logic [31:0] w_faddr;
    assign w_faddr = cfg.offset_mode
                   ? ((cfg.size_lg2 < 6'd32)
                      ? ((cfg.base & ~((32'd1 << cfg.size_lg2) - 32'd1))
                         | (fub_axi_araddr & ((32'd1 << cfg.size_lg2) - 32'd1)))
                      : fub_axi_araddr)
                   : fub_axi_araddr;

    logic w_in_win;
    assign w_in_win = (cfg.size_lg2 >= 6'd32) ? 1'b1
                    : cfg.offset_mode
                      ? ((fub_axi_araddr >> cfg.size_lg2) == '0)
                      : (((fub_axi_araddr ^ cfg.base) >> cfg.size_lg2) == '0);

    logic [8:0] w_dly;
    assign w_dly = 9'(cfg.lat_min) + 9'(r_rnd[7:0] & cfg.lat_mask);

    always_ff @(posedge aclk) begin
        for (int i = 0; i < DEPTH; i++)
            if (r_s_dly[i] != '0 && !(w_ar_hs && tb_alloc_idx == XW'(i)))
                r_s_dly[i] <= r_s_dly[i] - 9'd1;
        if (w_ar_hs) begin
            r_s_id   [tb_alloc_idx] <= fub_axi_arid;
            r_s_addr [tb_alloc_idx] <= w_faddr;
            r_s_size [tb_alloc_idx] <= fub_axi_arsize;
            r_s_len  [tb_alloc_idx] <= fub_axi_arlen;
            r_s_burst[tb_alloc_idx] <= fub_axi_arburst;
            r_s_left [tb_alloc_idx] <= fub_axi_arlen;
            r_s_resp [tb_alloc_idx] <= (cfg.err_en && ((w_faddr & cfg.err_mask) == cfg.err_base))
                                       ? RESP_SLVERR : RESP_OKAY;
            r_s_dly  [tb_alloc_idx] <= w_dly;
            r_s_rsb  [tb_alloc_idx] <= f_rsb(fub_axi_arsb) & RSB_MASK;
            r_s_uq   [tb_alloc_idx] <= UNIQUE && fub_axi_aridunq;
        end
        if (w_rmake) begin
            r_s_addr[w_pick_idx] <= f_next_addr(r_s_addr[w_pick_idx], r_s_size[w_pick_idx],
                                                r_s_len[w_pick_idx], r_s_burst[w_pick_idx]);
            r_s_left[w_pick_idx] <= r_s_left[w_pick_idx] - 8'd1;
        end
    end

    // registered request checks
    logic          r_q_valid, r_q_win;
    logic [IW-1:0] r_q_id;
    logic [31:0]   r_q_addr;
    logic [7:0]    r_q_len;
    logic [2:0]    r_q_size;
    logic [1:0]    r_q_burst;
    logic [31:0]   r_q_faddr;
    logic [31:0] r_q_sb;

    always_ff @(posedge aclk) begin
        if (w_ar_hs) begin
            r_q_win   <= w_in_win;
            r_q_faddr <= w_faddr;
            r_q_sb    <= fub_axi_arsb;
            r_q_id    <= fub_axi_arid;
            r_q_addr  <= fub_axi_araddr;
            r_q_len   <= fub_axi_arlen;
            r_q_size  <= fub_axi_arsize;
            r_q_burst <= fub_axi_arburst;
        end
    end

    // AXI5: the request sideband, expected only from a master that carries it
    localparam int  SRC_W_P   = (SRC_W > 0) ? SRC_W   : 1;
    localparam int  SRC_LSB_P = (SRC_W > 0) ? SRC_LSB : 0;
    logic [2:0]     w_q_src;
    logic [31:0] w_q_sb_exp;
    logic           w_q_sb_err;
    always_comb begin
        w_q_src = '0;
        if (SRC_W > 0) w_q_src = 3'(r_q_id[SRC_LSB_P +: SRC_W_P]);
        w_q_sb_exp = cfg.sb_src[w_q_src] ? (f_sb(r_q_faddr, cfg_hash_seed) & SB_MASK) : '0;
    end
    assign w_q_sb_err = (SB_MASK != '0) && r_q_valid && ((r_q_sb & SB_MASK) != w_q_sb_exp);

    // AXI5 IDUNQ (A5.2): per ID, bursts held (request accepted, response not
    // yet made) and whether the held one is unique. A request breaks the rule
    // when it is unique and its ID already has a burst held, or its ID's held
    // burst is unique. The master sees its bursts outstanding for longer than
    // this slave holds them, so a master that keeps the rule never trips it.
    logic w_q_uq_err;
    generate if (UNIQUE) begin : g_uq
        localparam int NID = 1 << IW;
        logic [XW:0]     r_cnt [NID];
        logic [NID-1:0]  r_flag;
        logic            r_q_uq_bad;
        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                r_flag     <= '0;
                r_q_uq_bad <= 1'b0;
                for (int i = 0; i < NID; i++) r_cnt[i] <= '0;
            end else begin
                if (w_ar_hs)
                    r_q_uq_bad <= fub_axi_aridunq ? (r_cnt[fub_axi_arid] != '0) : r_flag[fub_axi_arid];
                for (int i = 0; i < NID; i++) begin
                    r_cnt[i] <= r_cnt[i] + (XW+1)'(w_ar_hs && (fub_axi_arid == IW'(i)))
                                         - (XW+1)'(tb_retire && (r_s_id[w_pick_idx] == IW'(i)));
                    if (w_ar_hs && fub_axi_aridunq && (fub_axi_arid == IW'(i)))
                        r_flag[i] <= 1'b1;
                    else if (tb_retire && r_s_uq[w_pick_idx] && (r_s_id[w_pick_idx] == IW'(i)))
                        r_flag[i] <= 1'b0;
                end
            end
        )
        assign w_q_uq_err = r_q_valid && r_q_uq_bad;
    end else begin : g_no_uq
        assign w_q_uq_err = 1'b0;
    end endgenerate

    logic w_q_addr_err, w_q_proto_err;
    assign w_q_addr_err  = r_q_valid && !r_q_win;
    assign w_q_proto_err = r_q_valid && f_burst_illegal(r_q_addr, r_q_len, r_q_size,
                                                        r_q_burst, 3'(BUS_LG2));

    // =========================================================================
    // R scheduler
    // =========================================================================
    logic [DEPTH-1:0] w_elig;
    always_comb
        for (int i = 0; i < DEPTH; i++)
            w_elig[i] = tb_valid[i] && tb_head[i] && (r_s_dly[i] == '0);

    logic          r_lock;                // non-interleaved: on one burst to RLAST
    logic [XW-1:0] r_lock_idx;
    logic          w_have;
    logic [XW-1:0] w_rand_idx;

    always_comb begin
        w_rand_idx = '0;
        w_have     = 1'b0;
        for (int k = DEPTH - 1; k >= 0; k--) begin
            if (w_elig[XW'(int'(r_rnd[31:24]) + k)]) begin
                w_rand_idx = XW'(int'(r_rnd[31:24]) + k);
                w_have     = 1'b1;
            end
        end
        if (r_lock) begin
            w_pick_idx = r_lock_idx;
            w_have     = 1'b1;
        end else begin
            w_pick_idx = w_rand_idx;
        end
    end

    assign w_rmake   = w_have && r_rpass && (!r_rv || fub_axi_rready);
    assign tb_retire = w_rmake && (r_s_left[w_pick_idx] == 8'd0);

    logic [DW-1:0] w_rdata;
    always_comb
        for (int l = 0; l < NL; l++)
            w_rdata[l*32 +: 32] = f_word({r_s_addr[w_pick_idx][31:BUS_LG2], BUS_LG2'(l * 4)},
                                         cfg_hash_seed, cfg.tag, 1'b1);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_thr     <= 32'h3C6E_F372;
            r_rnd     <= 32'h1;
            r_arready <= 1'b0;
            r_rpass   <= 1'b0;
            r_rv      <= 1'b0;
            r_lock    <= 1'b0;
            r_q_valid <= 1'b0;
        end else begin
            r_thr     <= f_xs32(r_thr);
            r_rnd     <= (clear) ? f_xs32((cfg.seed == '0) ? 32'hA54F_F53A : cfg.seed)
                                 : f_xs32(r_rnd);
            r_arready <= f_pass(r_thr[3:0], cfg.req_throttle);
            r_rpass   <= f_pass(r_thr[7:4], cfg.data_throttle);
            r_q_valid <= w_ar_hs;
            if (w_rmake)             r_rv <= 1'b1;
            else if (fub_axi_rready) r_rv <= 1'b0;
            if (w_rmake) begin
                r_lock     <= !cfg.interleave && (r_s_left[w_pick_idx] != 8'd0);
                r_lock_idx <= w_pick_idx;
            end
        end
    )

    always_ff @(posedge aclk) begin
        if (w_rmake) begin
            fub_axi_rid   <= r_s_id[w_pick_idx];
            fub_axi_rdata <= w_rdata;
            fub_axi_rresp <= r_s_resp[w_pick_idx];
            fub_axi_rlast <= (r_s_left[w_pick_idx] == 8'd0);
            fub_axi_rsb   <= r_s_rsb[w_pick_idx];
            fub_axi_rpoison <= POISON && f_poison(r_s_addr[w_pick_idx], cfg_hash_seed,
                                                  cfg.poison_lg2);
            fub_axi_ridunq  <= r_s_uq[w_pick_idx];
        end
    end

    assign fub_axi_rvalid = r_rv;
    assign fub_axi_ruser  = '0;

    // =========================================================================
    // Status
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            sts <= '0;
        end else if (clear) begin
            sts      <= '0;
            sts.runs <= sts.runs + 8'd1;
        end else begin
            if (w_ar_hs)                    sts.bursts <= sts.bursts + 32'd1;
            if (r_rv && fub_axi_rready)     sts.beats  <= sts.beats + 32'd1;
            if (w_q_addr_err)  sts.err_mask[ERR_S_ADDR]  <= 1'b1;
            if (w_q_proto_err) sts.err_mask[ERR_S_PROTO] <= 1'b1;
            if (w_q_sb_err || w_q_uq_err) sts.err_mask[ERR_S_SB] <= 1'b1;
            if (w_q_addr_err || w_q_proto_err || w_q_sb_err || w_q_uq_err)
                sts.err_cnt <= (sts.err_cnt > 16'hFFFB) ? 16'hFFFF
                             : sts.err_cnt + 16'(w_q_addr_err) + 16'(w_q_proto_err)
                               + 16'(w_q_sb_err) + 16'(w_q_uq_err);
            if (!sts.fe_valid && (w_q_addr_err || w_q_proto_err)) begin
                sts.fe_valid <= 1'b1;
                sts.fe_kind  <= w_q_addr_err ? 4'(ERR_S_ADDR) : 4'(ERR_S_PROTO);
                sts.fe_id    <= 16'(r_q_id);
                sts.fe_addr  <= r_q_addr;
                sts.fe_exp   <= 32'({r_q_size, r_q_len});
                sts.fe_act   <= {30'd0, r_q_burst};
            end else if (!sts.fe_valid && w_q_sb_err) begin
                sts.fe_valid <= 1'b1;
                sts.fe_kind  <= 4'(ERR_S_SB);
                sts.fe_id    <= 16'(r_q_id);
                sts.fe_addr  <= r_q_addr;
                sts.fe_exp   <= 32'(w_q_sb_exp);
                sts.fe_act   <= 32'(r_q_sb);
            end else if (!sts.fe_valid && w_q_uq_err) begin
                sts.fe_valid <= 1'b1;
                sts.fe_kind  <= 4'(ERR_S_SB);
                sts.fe_id    <= 16'(r_q_id);
                sts.fe_addr  <= r_q_addr;
                sts.fe_exp   <= 32'h0;
                sts.fe_act   <= 32'h1D00_0000;     // IDUNQ rule
            end
            sts.out_now <= 8'(tb_count);
            if (8'(tb_count) > sts.out_max) sts.out_max <= 8'(tb_count);
        end
    )

    wire unused = ^{fub_axi_arlock, fub_axi_arcache, fub_axi_arprot, fub_axi_arqos,
                    fub_axi_arregion, fub_axi_aruser};

endmodule : axi_stress_slv_rd
