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
// On a mem window (a real memory) the lanes carry
// f_word(f_maddr(beat address), tag, RD) instead: the value a later read of
// that byte expects, so every write is idempotent (axi_stress_pkg f_maddr).
//
// B: the handshake is registered, then BID finds the oldest burst of that ID.
// Checks: ERR_WR_STRAY, ERR_WR_EARLY (a B for a burst whose last W has not
// left this block), ERR_WR_RESP, ERR_HANG. Data is checked at the slave.
//
// AXI5 sideband (SB_MASK / RSB_MASK / POISON, all off for AXI3/AXI4): AWSB is
// f_sb(AWADDR) & SB_MASK, WPOISON of each beat is f_poison(beat address,
// the window's rate), and the B response sideband must echo the
// request's (f_rsb(AWSB) & RSB_MASK: BTRACE = AWTRACE) when the window says
// responses echo (its sb), else 0 (ERR_M_SB). The slave checks AWSB and
// WPOISON.
//
// AXI5 IDUNQ (UNIQUE, cfg.idunq): as axi_stress_mst_rd, AWIDUNQ on eligible
// bursts, nothing else on a unique burst's ID until its B, and every BIDUNQ
// must be the bit its burst was issued with (ERR_M_SB).
//
// AXI5 atomics (ATOMIC, cfg.atom_lg2, window atomic): an address hash makes 1
// burst in 2^n to an atomic window an atomic, reshaped into one legal beat
// (axi_stress_pkg f_atom_pick) on an ID from the upper half (ID MSB set; no
// other write uses it, and the host keeps reads below it). An atomic waits
// until its ID has nothing outstanding -- no burst, no read-return still
// owed (the AXI5 atomic ID rule). Its operand is ordinary write data. A
// read-return class (AWATOP[5]) also expects one R beat with its ID, which
// the shell steers here (fub_axi_atr_*): RLAST, RRESP against the window,
// the lanes against f_word(address, tag, RD), and RTRACE / RPOISON /
// RIDUNQ as on a read. Misses use the read codes (ERR_RD_STRAY / LAST /
// RESP / DATA) and ERR_M_SB in this block's status.
//
// AXI5 MTE (MTE): AWTAGOP is f_awtagop(AWADDR) (Invalid on an atomic); each W
// beat carries WTAG / WTAGUPDATE per 16-byte slot as axi_stress_pkg sets out,
// and BTAGMATCH must be f_btagmatch(AWADDR, AWTAGOP), or 2'b00 when the
// window's far end does not answer tags (window mte) (ERR_M_SB). The slave
// checks the request and W side.
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
    parameter logic [31:0] SB_MASK  = '0,  // AXI5 request sideband bits carried (SB_* layout)
    parameter logic [7:0]  RSB_MASK = '0,  // AXI5 response sideband bits carried (RSB_* layout)
    parameter bit POISON  = 1'b0,        // AXI5 WPOISON driven
    parameter bit UNIQUE  = 1'b0,        // AXI5 AWIDUNQ driven, BIDUNQ checked
    parameter bit ATOMIC  = 1'b0,        // AXI5 atomics issued (needs IW >= 2)
    parameter bit MTE     = 1'b0,        // AXI5 AWTAGOP / WTAG driven, BTAGMATCH checked
    parameter int XW      = $clog2(DEPTH),
    parameter int NB      = DW / 8,
    parameter int BUS_LG2 = $clog2(NB),
    parameter int NL      = DW / 32,
    parameter int NT      = (DW / 128 > 0) ? DW / 128 : 1,   // MTE tag slots per beat
    parameter int TW      = 4 * NT
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
    output logic [31:0]      fub_axi_awsb,
    output logic                fub_axi_awidunq,
    output logic [5:0]          fub_axi_awatop,
    output logic [1:0]          fub_axi_awtagop,
    output logic                fub_axi_awvalid,
    input  logic                fub_axi_awready,

    output logic [DW-1:0]       fub_axi_wdata,
    output logic [NB-1:0]       fub_axi_wstrb,
    output logic [IW-1:0]       fub_axi_wid,
    output logic                fub_axi_wlast,
    output logic [UW-1:0]       fub_axi_wuser,
    output logic                fub_axi_wpoison,
    output logic [TW-1:0]       fub_axi_wtag,
    output logic [NT-1:0]       fub_axi_wtagupdate,
    output logic                fub_axi_wvalid,
    input  logic                fub_axi_wready,

    input  logic [IW-1:0]       fub_axi_bid,
    input  logic [1:0]          fub_axi_bresp,
    input  logic [UW-1:0]       fub_axi_buser,
    input  logic [7:0]     fub_axi_bsb,
    input  logic                fub_axi_bidunq,
    input  logic [1:0]          fub_axi_btagmatch,
    input  logic                fub_axi_bvalid,
    output logic                fub_axi_bready,

    // AXI5: the R beats of read-return atomics (RID MSB set), from the shell
    input  logic                fub_axi_atr_valid,
    output logic                fub_axi_atr_ready,
    input  logic [IW-1:0]       fub_axi_atr_id,
    input  logic [DW-1:0]       fub_axi_atr_data,
    input  logic [1:0]          fub_axi_atr_resp,
    input  logic                fub_axi_atr_last,
    input  logic [7:0]          fub_axi_atr_rsb,
    input  logic                fub_axi_atr_poison,
    input  logic                fub_axi_atr_ridunq
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
    logic          t_valid, t_ready, t_strb_rand, t_sb, t_atom, t_mte, t_mem;
    logic [3:0]    t_plg2;
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
        .cfg_fill     (cfg.fill),
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
        .txn_plg2     (t_plg2),
        .txn_atom     (t_atom),
        .txn_mte      (t_mte),
        .txn_mem      (t_mem)
    );

    // =========================================================================
    // AXI5 atomics: the burst as issued (e_*)
    // =========================================================================
    logic [31:0]   w_ah;
    logic [8:0]    w_apick;              // {AWATOP, AWSIZE}
    logic          w_atom, w_atom_rr;
    logic [31:0]   e_addr;
    logic [7:0]    e_len;
    logic [2:0]    e_size;
    logic [1:0]    e_burst;
    logic [IW-1:0] e_id;
    logic          e_srand;

    assign w_ah      = f_hk(t_addr, cfg_hash_seed, 32'hA70B_1C55);
    assign w_apick   = f_atom_pick(f_xs32(w_ah), 3'(BUS_LG2));
    assign w_atom    = ATOMIC && t_atom && (cfg.atom_lg2 != 4'd0)
                    && ((w_ah[31:16] & ((16'd1 << cfg.atom_lg2) - 16'd1)) == 16'd0);
    assign w_atom_rr = w_atom && w_apick[8];
    always_comb begin
        e_addr  = t_addr;
        e_len   = t_len;
        e_size  = t_size;
        e_burst = t_burst;
        e_srand = t_strb_rand;
        e_id    = t_id;
        if (ATOMIC) e_id[IW-1] = w_atom;
        if (w_atom) begin
            e_size  = w_apick[2:0];
            e_addr  = t_addr & ~((32'd1 << w_apick[2:0]) - 32'd1);
            e_len   = 8'd0;
            e_burst = BURST_INCR;
            e_srand = 1'b0;               // every operand byte strobed
        end
    end

    // =========================================================================
    // Outstanding table
    // =========================================================================
    logic          tb_full, tb_lk_hit, tb_retire;
    logic [XW-1:0] tb_alloc_idx, tb_lk_idx;
    logic [XW:0]   tb_count;
    logic [DEPTH-1:0] tb_tail_vec;
    logic          w_issue;

    logic          r_b_valid;
    logic [IW-1:0] r_b_id;
    logic [1:0]    r_b_resp;
    logic [7:0] r_b_bsb;
    logic          r_b_bidunq;
    logic [1:0]    r_b_btm;

    axi_stress_ord_table #(.DEPTH(DEPTH), .KW(IW)) u_tbl (
        .aclk, .aresetn,
        .clear        (w_go),
        .alloc_valid  (w_issue),
        .alloc_key    (e_id),
        .alloc_idx    (tb_alloc_idx),
        .alloc_tail_vec (tb_tail_vec),
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
    logic [31:0]      r_s_ts    [DEPTH];
    logic [DEPTH-1:0] r_s_wdone;           // the burst's last W has left
    logic [7:0]  r_s_bsb   [DEPTH];   // AXI5: the B sideband expected
    logic [1:0]  r_s_btm   [DEPTH];   // AXI5: the BTAGMATCH expected
    logic [DEPTH-1:0] r_s_uq;         // AXI5: issued with AWIDUNQ
    logic [DEPTH-1:0] r_s_ex;         // AXI5: unique or atomic -- its ID waits

    // AXI5 IDUNQ, as axi_stress_mst_rd: blocked while the ID's newest burst
    // is unique; unique only when nothing on the ID is outstanding. An atomic
    // is held the same way, and also while its ID owes a read-return.
    logic w_uq_blk, w_uq, w_rr_id_live, w_rr_full;
    logic [31:0] w_uq_h;           // a named wire: IEEE 1800 has no select on a call
    assign w_uq_h = f_hk(t_addr, cfg_hash_seed, 32'h7F4A_7C15);
    assign w_uq_blk = ((UNIQUE || ATOMIC) && (|(tb_tail_vec & r_s_ex)))
                   || (w_atom && ((|tb_tail_vec) || w_rr_id_live || w_rr_full));
    assign w_uq     = UNIQUE && cfg.idunq && !(|tb_tail_vec)
                   && w_uq_h[0];

    // =========================================================================
    // W queue: one entry per issued burst, in AW order
    // =========================================================================
    localparam int WQW = XW + IW + 32 + 8 + 3 + 2 + 8 + 1 + 4 + 2 + 1;

    // AXI5 MTE: the burst's tag operation (none on an atomic)
    logic [1:0] w_tagop;
    assign w_tagop = (MTE && !w_atom) ? f_awtagop(e_addr, cfg_hash_seed) : TAGOP_INVALID;

    logic           wq_wr_ready, wq_rd_valid, wq_rd_ready;
    logic [WQW-1:0] wq_rd_data;

    gaxi_fifo_sync #(
        .REGISTERED(0), .DATA_WIDTH(WQW), .DEPTH(DEPTH)
    ) u_wq (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_issue),
        .wr_ready    (wq_wr_ready),
        .wr_data     ({tb_alloc_idx, e_id, e_addr, e_len, e_size, e_burst, t_tag, e_srand,
                       t_plg2, w_tagop, t_mem}),
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
    logic [3:0]    q_plg2;
    logic [1:0]    q_tagop;
    logic          q_mem;
    assign {q_idx, q_id, q_addr, q_len, q_size, q_burst, q_tag, q_srand, q_plg2, q_tagop,
            q_mem} = wq_rd_data;

    // =========================================================================
    // AW issue
    // =========================================================================
    logic        r_aw_valid;
    logic [7:0]  r_gap_cnt;
    logic [31:0] r_now;

    assign w_issue = r_run && t_valid && w_budget_left && (r_gap_cnt == '0)
                  && !tb_full && (tb_count < w_max_out) && wq_wr_ready && !w_uq_blk
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
            fub_axi_awid    <= e_id;
            fub_axi_awaddr  <= e_addr;
            fub_axi_awlen   <= e_len;
            fub_axi_awsize  <= e_size;
            fub_axi_awburst <= e_burst;
            fub_axi_awqos   <= t_qos;
            fub_axi_awsb    <= (SB_MASK != '0) ? (f_sb(e_addr, cfg_hash_seed) & SB_MASK) : '0;
            fub_axi_awidunq <= w_uq;
            fub_axi_awatop  <= w_atom ? w_apick[8:3] : 6'd0;
            fub_axi_awtagop <= w_tagop;
            r_s_btm [tb_alloc_idx] <= (MTE && t_mte) ? f_btagmatch(e_addr, cfg_hash_seed, w_tagop)
                                                     : 2'b00;
            r_s_uq  [tb_alloc_idx] <= w_uq;
            r_s_ex  [tb_alloc_idx] <= w_uq || w_atom;
            r_s_resp[tb_alloc_idx] <= t_resp;
            r_s_bsb [tb_alloc_idx] <= t_sb ? (f_rsb(f_sb(e_addr, cfg_hash_seed) & SB_MASK)
                                              & RSB_MASK) : '0;
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
    logic [3:0]    r_wa_plg2;
    logic [1:0]    r_wa_tagop;
    logic          r_wa_mem;

    // the beat to send: the part-sent burst, else the queue head
    logic          c_valid;
    logic [XW-1:0] c_idx;
    logic [IW-1:0] c_id;
    logic [31:0]   c_addr;
    logic [7:0]    c_len, c_left, c_tag;
    logic [2:0]    c_size;
    logic [1:0]    c_burst;
    logic          c_srand;
    logic [3:0]    c_plg2;
    logic [1:0]    c_tagop;
    logic          c_mem;
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
        c_plg2  = r_wa ? r_wa_plg2  : q_plg2;
        c_tagop = r_wa ? r_wa_tagop : q_tagop;
        c_mem   = r_wa ? r_wa_mem   : q_mem;
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
            // a mem window's write carries what a read of the byte expects
            word = f_word(f_maddr({c_addr[31:BUS_LG2], BUS_LG2'(l * 4)}, c_mem, cfg.mem_lg2),
                          cfg_hash_seed, c_tag, c_mem);
            for (int b = 0; b < 4; b++)
                w_data[l*32 + b*8 +: 8] = w_lanes[l*4 + b] ? word[b*8 +: 8] : ~word[b*8 +: 8];
        end
    end

    // AXI5 MTE: the beat's tags and tag-update bits, one per 16-byte slot
    logic [TW-1:0] w_wtag;
    logic [NT-1:0] w_wtagupd;
    always_comb begin
        logic [31:0] slot;
        slot      = '0;
        w_wtag    = '0;
        w_wtagupd = '0;
        if (MTE && c_tagop != TAGOP_INVALID)
            for (int i = 0; i < NT; i++) begin
                slot = {c_addr[31:BUS_LG2], BUS_LG2'(0)} + 32'(i * 16);
                w_wtag[i*4 +: 4] = f_tag(slot, cfg_hash_seed, 1'b0);
                w_wtagupd[i]     = (c_tagop == TAGOP_UPDATE) && f_tagupd(slot, cfg_hash_seed);
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
            r_wa_plg2     <= c_plg2;
            r_wa_tagop    <= c_tagop;
            r_wa_mem      <= c_mem;
            r_wv_idx      <= c_idx;
            r_wv_last     <= (c_left == 8'd0);
            fub_axi_wdata <= w_data;
            fub_axi_wstrb <= w_lanes & ~(c_srand ? w_sclr : '0);
            fub_axi_wid   <= c_id;
            fub_axi_wlast <= (c_left == 8'd0);
            fub_axi_wpoison <= POISON && f_poison(c_addr, cfg_hash_seed, c_plg2);
            fub_axi_wtag       <= w_wtag;
            fub_axi_wtagupdate <= w_wtagupd;
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
            r_b_bsb  <= fub_axi_bsb;
            r_b_bidunq <= fub_axi_bidunq;
            r_b_btm    <= fub_axi_btagmatch;
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

    // AXI5: the B response sideband
    logic w_bsb_err;
    assign w_bsb_err = r_b_valid && tb_lk_hit
                    && (((RSB_MASK != '0) && ((r_b_bsb & RSB_MASK) != r_s_bsb[tb_lk_idx]))
                        || (UNIQUE && (r_b_bidunq != r_s_uq[tb_lk_idx]))
                        || (MTE && (r_b_btm != r_s_btm[tb_lk_idx])));

    // =========================================================================
    // AXI5 read-return atomics: the R beats owed, and their checks
    // =========================================================================
    // One entry per read-return atomic issued, until its R beat arrives. A
    // later atomic on the same ID waits for it (w_rr_id_live). Two stages
    // after the registered handshake: B finds the entry by RID and checks
    // RLAST / RRESP / sideband, C checks the lanes.
    logic [DEPTH-1:0] r_rr_v;
    logic [IW-1:0]    r_rr_id   [DEPTH];
    logic [31:0]      r_rr_addr [DEPTH];
    logic [2:0]       r_rr_size [DEPTH];
    logic [7:0]       r_rr_tag  [DEPTH];
    logic [1:0]       r_rr_resp [DEPTH];
    logic [7:0]       r_rr_rsb  [DEPTH];
    logic [3:0]       r_rr_plg2 [DEPTH];
    logic [DEPTH-1:0] r_rr_uq;

    logic [XW-1:0] w_rr_free;
    logic          w_rr_alloc;
    always_comb begin
        w_rr_free    = '0;
        w_rr_full    = 1'b1;
        w_rr_id_live = 1'b0;
        for (int i = DEPTH - 1; i >= 0; i--) begin
            if (!r_rr_v[i]) begin
                w_rr_free = XW'(i);
                w_rr_full = 1'b0;
            end
            if (r_rr_v[i] && (r_rr_id[i] == e_id)) w_rr_id_live = 1'b1;
        end
        if (!ATOMIC) w_rr_full = 1'b0;
    end
    assign w_rr_alloc = w_issue && w_atom_rr;

    // stage A: the handshake
    logic          r_ra_valid, r_ra_last, r_ra_poison, r_ra_ridunq;
    logic [IW-1:0] r_ra_id;
    logic [DW-1:0] r_ra_data;
    logic [1:0]    r_ra_resp;
    logic [7:0]    r_ra_rsb;
    wire           w_atr_hs = ATOMIC && fub_axi_atr_valid;
    assign fub_axi_atr_ready = 1'b1;

    always_ff @(posedge aclk) begin
        if (w_atr_hs) begin
            r_ra_id     <= fub_axi_atr_id;
            r_ra_data   <= fub_axi_atr_data;
            r_ra_resp   <= fub_axi_atr_resp;
            r_ra_last   <= fub_axi_atr_last;
            r_ra_rsb    <= fub_axi_atr_rsb;
            r_ra_poison <= fub_axi_atr_poison;
            r_ra_ridunq <= fub_axi_atr_ridunq;
        end
    end

    // stage B: which atomic, and its control checks
    logic          w_rb_hit;
    logic [XW-1:0] w_rb_idx;
    always_comb begin
        w_rb_hit = 1'b0;
        w_rb_idx = '0;
        for (int i = 0; i < DEPTH; i++)
            if (r_rr_v[i] && (r_rr_id[i] == r_ra_id)) begin
                w_rb_hit = 1'b1;
                w_rb_idx = XW'(i);
            end
    end

    logic        w_rb_err, w_rb_sb_err;
    logic [3:0]  w_rb_kind;
    logic [31:0] w_rb_exp, w_rb_act;
    logic        w_rb_p_exp;
    assign w_rb_p_exp = POISON && f_poison(r_rr_addr[w_rb_idx], cfg_hash_seed, r_rr_plg2[w_rb_idx]);
    always_comb begin
        w_rb_err  = 1'b0;
        w_rb_kind = 4'(ERR_RD_STRAY);
        w_rb_exp  = '0;
        w_rb_act  = '0;
        if (r_ra_valid) begin
            if (!w_rb_hit) begin
                w_rb_err = 1'b1;
                w_rb_act = r_ra_data[31:0];
            end else if (!r_ra_last) begin
                w_rb_err  = 1'b1;
                w_rb_kind = 4'(ERR_RD_LAST);
                w_rb_exp  = 32'd1;
            end else if (r_ra_resp != r_rr_resp[w_rb_idx]) begin
                w_rb_err  = 1'b1;
                w_rb_kind = 4'(ERR_RD_RESP);
                w_rb_exp  = {30'd0, r_rr_resp[w_rb_idx]};
                w_rb_act  = {30'd0, r_ra_resp};
            end
        end
    end
    assign w_rb_sb_err = r_ra_valid && w_rb_hit
                      && (((r_ra_rsb & RSB_MASK) != r_rr_rsb[w_rb_idx])
                          || (POISON && (r_ra_poison != w_rb_p_exp))
                          || (UNIQUE && (r_ra_ridunq != r_rr_uq[w_rb_idx])));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_ra_valid <= 1'b0;
            r_rr_v     <= '0;
        end else begin
            r_ra_valid <= w_atr_hs;
            if (w_go) r_rr_v <= '0;
            else begin
                if (r_ra_valid && w_rb_hit) r_rr_v[w_rb_idx] <= 1'b0;
                if (w_rr_alloc)             r_rr_v[w_rr_free] <= 1'b1;
            end
        end
    )

    always_ff @(posedge aclk) begin
        if (w_rr_alloc) begin
            r_rr_id  [w_rr_free] <= e_id;
            r_rr_addr[w_rr_free] <= e_addr;
            r_rr_size[w_rr_free] <= e_size;
            r_rr_tag [w_rr_free] <= t_tag;
            r_rr_resp[w_rr_free] <= t_resp;
            r_rr_rsb [w_rr_free] <= t_sb ? (f_rsb(f_sb(e_addr, cfg_hash_seed) & SB_MASK)
                                            & RSB_MASK) : '0;
            r_rr_plg2[w_rr_free] <= t_plg2;
            r_rr_uq  [w_rr_free] <= w_uq;
        end
    end

    // stage C: the lanes
    logic            r_rc_valid;
    logic [31:0]     r_rc_addr;
    logic [2:0]      r_rc_size;
    logic [7:0]      r_rc_tag;
    logic [IW-1:0]   r_rc_id;
    logic [DW-1:0]   r_rc_data;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_rc_valid <= 1'b0;
        else r_rc_valid <= r_ra_valid && w_rb_hit && r_ra_last
                        && (r_rr_resp[w_rb_idx] == RESP_OKAY) && (r_ra_resp == RESP_OKAY);
    )

    always_ff @(posedge aclk) begin
        if (r_ra_valid) begin
            r_rc_addr <= r_rr_addr[w_rb_idx];
            r_rc_size <= r_rr_size[w_rb_idx];
            r_rc_tag  <= r_rr_tag[w_rb_idx];
            r_rc_id   <= r_ra_id;
            r_rc_data <= r_ra_data;
        end
    end

    logic        w_rc_err;
    logic [31:0] w_rc_exp_w, w_rc_act_w, w_rc_addr_w;
    always_comb begin
        logic [BUS_LG2:0] lo, hi;
        logic [31:0]      bytes, word;
        logic [NL-1:0]    bad;
        bytes = 32'd1 << r_rc_size;
        lo    = (BUS_LG2+1)'(r_rc_addr[BUS_LG2-1:0]);
        hi    = lo + (BUS_LG2+1)'(bytes) - (BUS_LG2+1)'(1);   // aligned: one run of lanes
        w_rc_exp_w  = '0;
        w_rc_act_w  = '0;
        w_rc_addr_w = '0;
        for (int l = NL - 1; l >= 0; l--) begin
            word   = f_word({r_rc_addr[31:BUS_LG2], BUS_LG2'(l * 4)}, cfg_hash_seed, r_rc_tag, 1'b1);
            bad[l] = 1'b0;
            for (int b = 0; b < 4; b++)
                if (((BUS_LG2+1)'(l*4 + b) >= lo) && ((BUS_LG2+1)'(l*4 + b) <= hi)
                    && (word[b*8 +: 8] != r_rc_data[l*32 + b*8 +: 8]))
                    bad[l] = 1'b1;
            if (bad[l]) begin
                w_rc_exp_w  = word;
                w_rc_act_w  = r_rc_data[l*32 +: 32];
                w_rc_addr_w = {r_rc_addr[31:BUS_LG2], BUS_LG2'(l * 4)};
            end
        end
        w_rc_err = r_rc_valid && (|bad);
    end

    // =========================================================================
    // Hang detection and status
    // =========================================================================
    logic [31:0] r_idle;
    logic        w_hang;

    // Issue-to-retire latency, modulo 2^32 (43 s at 100 MHz). The stamps, the
    // clock and the difference are all 32 bits, so no tool can widen the
    // subtraction past its operands: with 16-bit stamps inside a 32'() cast,
    // Vivado extended both to 32 bits first and a wrapped stamp read ~4 billion,
    // while Verilator computed it at 16 bits. They were 16 bits until
    // 2026-10-22, and a burst slower than 65,535 cycles read wrapped.
    logic [31:0] w_lat;
    assign w_lat = r_now - r_s_ts[tb_lk_idx];
    // LAT_SUM saturates; a 33-bit sum, because one latency can now be large
    logic [32:0] w_lat_sum;
    assign w_lat_sum = {1'b0, sts.lat_sum} + {1'b0, w_lat};
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
            r_now <= r_now + 32'd1;
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

                if (w_b_hs || w_w_hs || w_atr_hs || (tb_count == '0 && r_rr_v == '0))
                    r_idle <= '0;
                else if (!r_idle[31])
                    r_idle <= r_idle + 32'd1;

                if (w_b_err)     sts.err_mask[w_b_kind]    <= 1'b1;
                if (w_bsb_err)   sts.err_mask[ERR_M_SB]    <= 1'b1;
                if (w_rb_err)    sts.err_mask[w_rb_kind]   <= 1'b1;
                if (w_rb_sb_err) sts.err_mask[ERR_M_SB]    <= 1'b1;
                if (w_rc_err)    sts.err_mask[ERR_RD_DATA] <= 1'b1;
                if (w_hang)      sts.err_mask[ERR_HANG]    <= 1'b1;
                if (w_b_err || w_bsb_err || w_rb_err || w_rb_sb_err || w_rc_err || w_hang)
                    sts.err_cnt <= (sts.err_cnt > 16'hFFF9) ? 16'hFFFF
                                 : sts.err_cnt + 16'(w_b_err) + 16'(w_bsb_err) + 16'(w_rb_err)
                                   + 16'(w_rb_sb_err) + 16'(w_rc_err) + 16'(w_hang);
                if (!sts.fe_valid) begin
                    if (w_rc_err) begin
                        sts.fe_valid <= 1'b1;
                        sts.fe_kind  <= 4'(ERR_RD_DATA);
                        sts.fe_id    <= 16'(r_rc_id);
                        sts.fe_addr  <= w_rc_addr_w;
                        sts.fe_exp   <= w_rc_exp_w;
                        sts.fe_act   <= w_rc_act_w;
                    end else if (w_rb_err) begin
                        sts.fe_valid <= 1'b1;
                        sts.fe_kind  <= w_rb_kind;
                        sts.fe_id    <= 16'(r_ra_id);
                        sts.fe_addr  <= w_rb_hit ? r_rr_addr[w_rb_idx] : 32'd0;
                        sts.fe_exp   <= w_rb_exp;
                        sts.fe_act   <= w_rb_act;
                    end else if (w_rb_sb_err) begin
                        sts.fe_valid <= 1'b1;
                        sts.fe_kind  <= 4'(ERR_M_SB);
                        sts.fe_id    <= 16'(r_ra_id);
                        sts.fe_addr  <= r_rr_addr[w_rb_idx];
                        sts.fe_exp   <= {w_rb_p_exp,  r_rr_uq[w_rb_idx], 22'd0, r_rr_rsb[w_rb_idx]};
                        sts.fe_act   <= {r_ra_poison, r_ra_ridunq, 22'd0, r_ra_rsb};
                    end else if (w_b_err) begin
                        sts.fe_valid <= 1'b1;
                        sts.fe_kind  <= w_b_kind;
                        sts.fe_id    <= 16'(r_b_id);
                        sts.fe_addr  <= '0;
                        sts.fe_exp   <= w_b_exp;
                        sts.fe_act   <= w_b_act;
                    end else if (w_bsb_err) begin
                        sts.fe_valid <= 1'b1;
                        sts.fe_kind  <= 4'(ERR_M_SB);
                        sts.fe_id    <= 16'(r_b_id);
                        sts.fe_addr  <= '0;
                        sts.fe_exp   <= {r_s_uq[tb_lk_idx], r_s_btm[tb_lk_idx], 21'd0, r_s_bsb[tb_lk_idx]};
                        sts.fe_act   <= {r_b_bidunq, r_b_btm, 21'd0, r_b_bsb};
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
                    sts.lat_sum <= w_lat_sum[32] ? 32'hFFFF_FFFF : w_lat_sum[31:0];
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
                     && !wq_rd_valid && !r_b_valid
                     && (r_rr_v == '0) && !r_ra_valid && !r_rc_valid;

    wire unused = ^{fub_axi_buser};

endmodule : axi_stress_mst_wr
