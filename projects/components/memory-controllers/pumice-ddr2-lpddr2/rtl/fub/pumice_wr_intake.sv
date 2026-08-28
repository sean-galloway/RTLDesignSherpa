// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_wr_intake
// Purpose: Dumb AXI4 write intake. One AXI burst == one DFI burst (the host or
//          the front splitter guarantees (awlen+1)*GEAR == BL). No pointer, no
//          CAM, no forwarding — that lives downstream in the wr-data CAM.
//
// Structure (exactly three things, per the locked uArch spec):
//   1. axi4_slave_wr      — AXI protocol / skid buffering
//   2. AW-meta FIFO       — {err, id, addr} captured per burst
//   3. wr-data FIFO       — {data, strb, last} per AXI beat (GEAR repack is
//                           deferred to the DFI data path on the pop side)
//   + addr_mapper         — head addr -> {rank,bank,row,col} for the push
//
// Boundaries:
//   - aw_push_* : decoded write command to the wr-data CAM (drained in order)
//   - wdata_*   : write-data pop to wr_beat_sequencer (commit order)
//   - wr_done_* : downstream commit completion -> B (commit-driven B)
//   - ragged burst ((awlen+1)*GEAR != BL): sim assertion + aw_push_err_o +
//     bresp=SLVERR (the intake self-generates the error B; downstream drops it).
//
// Documentation: rtl/PUMICE_AXI4_IFC_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_wr_intake #(
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 64,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int DRAM_BEAT_WIDTH   = 64,   // GEAR = AXI_DATA_WIDTH / DRAM_BEAT_WIDTH
    parameter int NUM_RANKS         = 1,
    parameter int NUM_BANKS         = 8,
    parameter int ROW_WIDTH         = 14,
    parameter int COL_WIDTH         = 10,
    parameter int BYTE_OFFSET_WIDTH = 3,
    parameter int RAGGED_ASSERT     = 1,    // 0 disables the ragged-burst $error (SLVERR test)
    parameter int BL                = 4,    // DRAM burst length, in DRAM beats
    parameter int AW_FIFO_DEPTH     = 4,
    parameter int WDATA_FIFO_DEPTH  = 16,
    parameter int B_FIFO_DEPTH      = 4,
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    // Derived
    parameter int IW  = AXI_ID_WIDTH,
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int DW  = AXI_DATA_WIDTH,
    parameter int UW  = AXI_USER_WIDTH,
    parameter int SW  = AXI_DATA_WIDTH / 8,
    parameter int GEAR         = AXI_DATA_WIDTH / DRAM_BEAT_WIDTH,
    parameter int EXP_AXI_BEATS = BL / GEAR,   // AXI beats that make one DRAM burst
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS)
) (
    input  logic                     aclk,
    input  logic                     aresetn,

    // Address-map config (passed to addr_mapper — ADDR_MAP register)
    input  logic [4:0]               bank_lsb_i,
    input  logic                     hash_en_i,
    input  logic [7:0]               hash_seed_i,

    //=========================================================================
    // AXI4 write slave (post-split: each burst is exactly one DRAM burst)
    //=========================================================================
    input  logic [IW-1:0]            s_axi_awid,
    input  logic [AW-1:0]            s_axi_awaddr,
    input  logic [7:0]               s_axi_awlen,
    input  logic [2:0]               s_axi_awsize,
    input  logic [1:0]               s_axi_awburst,
    input  logic                     s_axi_awlock,
    input  logic [3:0]               s_axi_awcache,
    input  logic [2:0]               s_axi_awprot,
    input  logic [3:0]               s_axi_awqos,
    input  logic [3:0]               s_axi_awregion,
    input  logic [UW-1:0]            s_axi_awuser,
    input  logic                     s_axi_awvalid,
    output logic                     s_axi_awready,
    // aggregation sideband (aligned with s_axi_aw, from the splitter)
    input  logic                     aw_agg_i,
    input  logic                     aw_last_i,

    input  logic [DW-1:0]            s_axi_wdata,
    input  logic [SW-1:0]            s_axi_wstrb,
    input  logic                     s_axi_wlast,
    input  logic [UW-1:0]            s_axi_wuser,
    input  logic                     s_axi_wvalid,
    output logic                     s_axi_wready,

    output logic [IW-1:0]            s_axi_bid,
    output logic [1:0]               s_axi_bresp,
    output logic [UW-1:0]            s_axi_buser,
    output logic                     s_axi_bvalid,
    input  logic                     s_axi_bready,

    //=========================================================================
    // Downstream write-command push (to the wr-data CAM)
    //=========================================================================
    output logic                     aw_push_valid_o,
    input  logic                     aw_push_ready_i,
    output logic [RKW-1:0]           aw_push_rank_o,
    output logic [BKW-1:0]           aw_push_bank_o,
    output logic [ROW_WIDTH-1:0]     aw_push_row_o,
    output logic [COL_WIDTH-1:0]     aw_push_col_o,
    output logic [IW-1:0]            aw_push_id_o,
    output logic [3:0]               aw_push_qos_o,   // AxQOS -> CAM (QOS_EN pick)
    output logic                     aw_push_err_o,   // ragged burst (illegal)
    output logic                     aw_push_agg_o,   // part of a split
    output logic                     aw_push_last_o,  // final sub of the burst

    //=========================================================================
    // Write-data pop (to wr_beat_sequencer, drained in commit order)
    //=========================================================================
    output logic                     wdata_valid_o,
    input  logic                     wdata_ready_i,
    output logic [DW-1:0]            wdata_o,
    output logic [SW-1:0]            wstrb_o,
    output logic                     wlast_o,

    //=========================================================================
    // Write completion from downstream commit -> B (commit-driven)
    //=========================================================================
    input  logic                     wr_done_valid_i,
    input  logic [IW-1:0]            wr_done_id_i,
    input  logic [1:0]               wr_done_resp_i,

    output logic                     busy_o
);

    import pumice_pkg::*;

    localparam logic [1:0] RESP_OKAY   = 2'b00;
    localparam logic [1:0] RESP_SLVERR = 2'b10;

    // ---- post-skid AXI (from axi4_slave_wr) --------------------------------
    logic [IW-1:0] fub_awid;    logic [AW-1:0] fub_awaddr;  logic [7:0] fub_awlen;
    logic [2:0]    fub_awsize;  logic [1:0]    fub_awburst; logic       fub_awlock;
    logic [3:0]    fub_awcache; logic [2:0]    fub_awprot;  logic [3:0] fub_awqos;
    logic [3:0]    fub_awregion;logic [UW-1:0] fub_awuser;
    logic          fub_awvalid; logic          fub_awready;

    logic [DW-1:0] fub_wdata;   logic [SW-1:0] fub_wstrb;   logic fub_wlast;
    logic [UW-1:0] fub_wuser;   logic          fub_wvalid;  logic fub_wready;

    logic [IW-1:0] fub_bid;     logic [1:0]    fub_bresp;   logic [UW-1:0] fub_buser;
    logic          fub_bvalid;  logic          fub_bready;
    logic          w_slave_busy;

    axi4_slave_wr #(
        .SKID_DEPTH_AW (SKID_DEPTH_AW),
        .SKID_DEPTH_W  (SKID_DEPTH_W),
        .SKID_DEPTH_B  (SKID_DEPTH_B),
        .AXI_ID_WIDTH  (IW),
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_USER_WIDTH(UW)
    ) u_slave_wr (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .s_axi_awid      (s_axi_awid),
        .s_axi_awaddr    (s_axi_awaddr),
        .s_axi_awlen     (s_axi_awlen),
        .s_axi_awsize    (s_axi_awsize),
        .s_axi_awburst   (s_axi_awburst),
        .s_axi_awlock    (s_axi_awlock),
        .s_axi_awcache   (s_axi_awcache),
        .s_axi_awprot    (s_axi_awprot),
        .s_axi_awqos     (s_axi_awqos),
        .s_axi_awregion  (s_axi_awregion),
        .s_axi_awuser    (s_axi_awuser),
        .s_axi_awvalid   (s_axi_awvalid),
        .s_axi_awready   (s_axi_awready),
        .s_axi_wdata     (s_axi_wdata),
        .s_axi_wstrb     (s_axi_wstrb),
        .s_axi_wlast     (s_axi_wlast),
        .s_axi_wuser     (s_axi_wuser),
        .s_axi_wvalid    (s_axi_wvalid),
        .s_axi_wready    (s_axi_wready),
        .s_axi_bid       (s_axi_bid),
        .s_axi_bresp     (s_axi_bresp),
        .s_axi_buser     (s_axi_buser),
        .s_axi_bvalid    (s_axi_bvalid),
        .s_axi_bready    (s_axi_bready),
        .fub_axi_awid    (fub_awid),
        .fub_axi_awaddr  (fub_awaddr),
        .fub_axi_awlen   (fub_awlen),
        .fub_axi_awsize  (fub_awsize),
        .fub_axi_awburst (fub_awburst),
        .fub_axi_awlock  (fub_awlock),
        .fub_axi_awcache (fub_awcache),
        .fub_axi_awprot  (fub_awprot),
        .fub_axi_awqos   (fub_awqos),
        .fub_axi_awregion(fub_awregion),
        .fub_axi_awuser  (fub_awuser),
        .fub_axi_awvalid (fub_awvalid),
        .fub_axi_awready (fub_awready),
        .fub_axi_wdata   (fub_wdata),
        .fub_axi_wstrb   (fub_wstrb),
        .fub_axi_wlast   (fub_wlast),
        .fub_axi_wuser   (fub_wuser),
        .fub_axi_wvalid  (fub_wvalid),
        .fub_axi_wready  (fub_wready),
        .fub_axi_bid     (fub_bid),
        .fub_axi_bresp   (fub_bresp),
        .fub_axi_buser   (fub_buser),
        .fub_axi_bvalid  (fub_bvalid),
        .fub_axi_bready  (fub_bready),
        .busy            (w_slave_busy)
    );

    // ========================================================================
    // Aggregation sideband skid-alignment FIFO
    // ------------------------------------------------------------------------
    // aw_agg_i/aw_last_i arrive aligned with s_axi_aw (pre-skid). axi4_slave_wr
    // buffers AW in-order, so the sideband is captured on s_axi_aw acceptance
    // and replayed on fub_aw acceptance (1:1, in order), where it merges into
    // the AW-meta FIFO. Depth covers the AW skid occupancy.
    // ========================================================================
    logic       w_side_wr_valid, w_side_rd_ready;
    logic [1:0] w_side_rd_data;
    logic       w_side_agg, w_side_last;

    assign w_side_wr_valid = s_axi_awvalid && s_axi_awready;

    gaxi_fifo_sync #(.DATA_WIDTH(2), .DEPTH(SKID_DEPTH_AW + AW_FIFO_DEPTH)) u_aw_side_fifo (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_side_wr_valid),
        .wr_data    ({aw_agg_i, aw_last_i}),
        .rd_ready   (w_side_rd_ready),
        .rd_valid   (),
        .rd_data    (w_side_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .wr_ready(),
        .count   ()
        /* verilator lint_on PINCONNECTEMPTY */
    );
    assign {w_side_agg, w_side_last} = w_side_rd_data;
    // pop in lockstep with the AW-meta FIFO write (fub_aw acceptance)
    assign w_side_rd_ready = fub_awvalid && fub_awready;

    // ========================================================================
    // (2) AW-meta FIFO : {err, agg, last, id, addr}
    // ========================================================================
    localparam int AWM_W = 3 + 4 + IW + AW;   // {err,agg,last,QOS,id,addr}

    logic          w_aw_err;
    assign w_aw_err = ((32'(fub_awlen) + 32'd1) * GEAR != BL);

    logic             w_awm_wr_valid, w_awm_wr_ready;
    logic [AWM_W-1:0] w_awm_wr_data;
    logic             w_awm_rd_valid, w_awm_rd_ready;
    logic [AWM_W-1:0] w_awm_rd_data;

    assign w_awm_wr_valid = fub_awvalid;
    assign fub_awready    = w_awm_wr_ready;
    assign w_awm_wr_data  = {w_aw_err, w_side_agg, w_side_last, fub_awqos,
                             fub_awid, fub_awaddr};

    gaxi_fifo_sync #(.DATA_WIDTH(AWM_W), .DEPTH(AW_FIFO_DEPTH)) u_aw_meta_fifo (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_awm_wr_valid),
        .wr_ready   (w_awm_wr_ready),
        .wr_data    (w_awm_wr_data),
        .rd_ready   (w_awm_rd_ready),
        .count      (),
        .rd_valid   (w_awm_rd_valid),
        .rd_data    (w_awm_rd_data)
    );

    logic          w_head_err, w_head_agg, w_head_last;
    logic [IW-1:0] w_head_id;
    logic [3:0]    w_head_qos;
    logic [AW-1:0] w_head_addr;
    assign {w_head_err, w_head_agg, w_head_last, w_head_qos,
            w_head_id, w_head_addr} = w_awm_rd_data;

    // Decode the head burst's address to {rank,bank,row,col}
    logic [RKW-1:0]        w_rank;
    logic [BKW-1:0]        w_bank;
    logic [ROW_WIDTH-1:0]  w_row;
    logic [COL_WIDTH-1:0]  w_col;

    addr_mapper #(
        .AXI_ADDR_WIDTH   (AW),
        .NUM_RANKS        (NUM_RANKS),
        .NUM_BANKS        (NUM_BANKS),
        .ROW_WIDTH        (ROW_WIDTH),
        .COL_WIDTH        (COL_WIDTH),
        .BYTE_OFFSET_WIDTH(BYTE_OFFSET_WIDTH)
    ) u_addr_mapper (
        .axi_addr_i (w_head_addr),
        .bank_lsb_i (bank_lsb_i),
        .hash_en_i  (hash_en_i),
        .hash_seed_i(hash_seed_i),
        .rank_o     (w_rank),
        .bank_o     (w_bank),
        .row_o      (w_row),
        .col_o      (w_col)
    );

    // aw_push = decoded head; pop the AW-meta FIFO on handshake.
    assign aw_push_valid_o = w_awm_rd_valid;
    assign aw_push_rank_o  = w_rank;
    assign aw_push_bank_o  = w_bank;
    assign aw_push_row_o   = w_row;
    assign aw_push_col_o   = w_col;
    assign aw_push_id_o    = w_head_id;
    assign aw_push_qos_o   = w_head_qos;
    assign aw_push_err_o   = w_head_err;
    assign aw_push_agg_o   = w_head_agg;
    assign aw_push_last_o  = w_head_last;
    assign w_awm_rd_ready  = aw_push_ready_i;

    // ========================================================================
    // (3) wr-data FIFO : {last, strb, data} (per AXI beat)
    // ========================================================================
    localparam int WD_W = 1 + SW + DW;

    logic            w_wd_wr_valid, w_wd_wr_ready;
    logic [WD_W-1:0] w_wd_wr_data;
    logic            w_wd_rd_valid, w_wd_rd_ready;
    logic [WD_W-1:0] w_wd_rd_data;

    assign w_wd_wr_valid = fub_wvalid;
    assign fub_wready    = w_wd_wr_ready;
    assign w_wd_wr_data  = {fub_wlast, fub_wstrb, fub_wdata};

    gaxi_fifo_sync #(.DATA_WIDTH(WD_W), .DEPTH(WDATA_FIFO_DEPTH)) u_wr_data_fifo (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_wd_wr_valid),
        .wr_ready   (w_wd_wr_ready),
        .wr_data    (w_wd_wr_data),
        .rd_ready   (w_wd_rd_ready),
        .count      (),
        .rd_valid   (w_wd_rd_valid),
        .rd_data    (w_wd_rd_data)
    );

    assign wdata_valid_o = w_wd_rd_valid;
    assign {wlast_o, wstrb_o, wdata_o} = w_wd_rd_data;
    assign w_wd_rd_ready = wdata_ready_i;

    // ========================================================================
    // B response FIFO : {resp, id}
    //   - good burst : pushed on downstream wr_done (OKAY / carried resp)
    //   - ragged burst: intake self-generates SLVERR at the aw_push pop
    // ========================================================================
    localparam int B_W = 2 + IW;

    logic          w_aw_push_fire;
    assign w_aw_push_fire = aw_push_valid_o && aw_push_ready_i;

    logic          w_err_b_fire;
    assign w_err_b_fire = w_aw_push_fire && w_head_err;

    logic            w_b_wr_valid, w_b_wr_ready;
    logic [B_W-1:0]  w_b_wr_data;
    logic            w_b_rd_valid, w_b_rd_ready;
    logic [B_W-1:0]  w_b_rd_data;

    // err B takes priority; a good-burst wr_done should not coincide with a
    // ragged aw pop for the same slot (asserted below).
    assign w_b_wr_valid = w_err_b_fire || wr_done_valid_i;
    assign w_b_wr_data  = w_err_b_fire ? {RESP_SLVERR, w_head_id}
                                       : {wr_done_resp_i, wr_done_id_i};

    gaxi_fifo_sync #(.DATA_WIDTH(B_W), .DEPTH(B_FIFO_DEPTH)) u_b_fifo (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_b_wr_valid),
        .wr_ready   (w_b_wr_ready),
        .wr_data    (w_b_wr_data),
        .rd_ready   (w_b_rd_ready),
        .count      (),
        .rd_valid   (w_b_rd_valid),
        .rd_data    (w_b_rd_data)
    );

    assign {fub_bresp, fub_bid} = w_b_rd_data;
    assign fub_buser  = '0;
    assign fub_bvalid = w_b_rd_valid;
    assign w_b_rd_ready = fub_bready;

    assign busy_o = w_awm_rd_valid || w_wd_rd_valid || w_b_rd_valid;

    // ---- guardrails --------------------------------------------------------
    // synthesis translate_off
    always_ff @(posedge aclk) begin
        if (aresetn) begin
            if ((RAGGED_ASSERT != 0) && w_awm_wr_valid && w_awm_wr_ready && w_aw_err)
                $error("pumice_wr_intake: ragged burst awlen+1=%0d GEAR=%0d BL=%0d (must satisfy (awlen+1)*GEAR==BL)",
                       fub_awlen + 8'd1, GEAR, BL);
            if (w_err_b_fire && wr_done_valid_i)
                $error("pumice_wr_intake: B push collision (err + wr_done same cycle)");
        end
    end
    // synthesis translate_on

endmodule : pumice_wr_intake
