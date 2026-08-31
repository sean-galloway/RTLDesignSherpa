// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_rd_intake
// Purpose: Dumb AXI4 read intake, mirror of pumice_wr_intake, plus the read
//          snarf path. One AXI burst == one DFI burst.
//
// Structure:
//   1. axi4_slave_rd    — AXI protocol / skid buffering
//   2. addr_mapper      — AR addr -> {rank,bank,row,col}
//   3. SNARF PROBE at the AR inlet: query the wr CAM with {bank,row,col}.
//        HIT  -> source = snarf (data streamed from the CAM's wr-data SRAM)
//        MISS -> source = DFI   -> emit ar_push to the scheduler / rd CAM
//   4. order FIFO       — {source, id} per admitted read, preserves AR order
//   5. source arbiter   — per order-FIFO head, fill the rd-data FIFO from the
//                         tagged source (snarf stream OR DFI read-return)
//   6. rd-data FIFO     — {data, id, last, resp} -> AXI R channel
//
// A CAM hit forces snarf (DRAM is stale for in-flight writes). In-order R:
// a snarf-ready read still waits behind an earlier DFI read at the head.
//
// Documentation: rtl/PUMICE_AXI4_IFC_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_rd_intake #(
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 64,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int DRAM_BEAT_WIDTH   = 64,
    parameter int NUM_RANKS         = 1,
    parameter int NUM_BANKS         = 8,
    parameter int ROW_WIDTH         = 14,
    parameter int COL_WIDTH         = 10,
    parameter int BYTE_OFFSET_WIDTH = 3,
    parameter int AXI_BEATS_PER_BURST                = 4,
    parameter int AR_FIFO_DEPTH     = 4,
    parameter int ORDER_FIFO_DEPTH  = 8,
    parameter int RD_FIFO_DEPTH     = 16,
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // Derived
    parameter int IW  = AXI_ID_WIDTH,
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int DW  = AXI_DATA_WIDTH,
    parameter int UW  = AXI_USER_WIDTH,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS)
) (
    input  logic                     aclk,
    input  logic                     aresetn,

    input  logic [4:0]               bank_lsb_i,
    input  logic                     hash_en_i,
    input  logic [7:0]               hash_seed_i,

    //=========================================================================
    // AXI4 read slave (post-split: each burst is exactly one DRAM burst)
    //=========================================================================
    input  logic [IW-1:0]            s_axi_arid,
    input  logic [AW-1:0]            s_axi_araddr,
    input  logic [7:0]               s_axi_arlen,
    input  logic [2:0]               s_axi_arsize,
    input  logic [1:0]               s_axi_arburst,
    input  logic                     s_axi_arlock,
    input  logic [3:0]               s_axi_arcache,
    input  logic [2:0]               s_axi_arprot,
    input  logic [3:0]               s_axi_arqos,
    input  logic [3:0]               s_axi_arregion,
    input  logic [UW-1:0]            s_axi_aruser,
    input  logic                     s_axi_arvalid,
    output logic                     s_axi_arready,
    // aggregation sideband (aligned with s_axi_ar, from the splitter): agg=1
    // when the host read splits into >1 sub-command, last=1 on the final sub.
    // Used to collapse per-sub RLAST. Default (agg=0) => pass RLAST per sub.
    input  logic                     ar_agg_i,
    input  logic                     ar_last_i,

    output logic [IW-1:0]            s_axi_rid,
    output logic [DW-1:0]            s_axi_rdata,
    output logic [1:0]               s_axi_rresp,
    output logic                     s_axi_rlast,
    output logic [UW-1:0]            s_axi_ruser,
    output logic                     s_axi_rvalid,
    input  logic                     s_axi_rready,

    //=========================================================================
    // MISS path: read-command push to the scheduler / rd CAM
    //=========================================================================
    output logic                     ar_push_valid_o,
    input  logic                     ar_push_ready_i,
    output logic [RKW-1:0]           ar_push_rank_o,
    output logic [BKW-1:0]           ar_push_bank_o,
    output logic [ROW_WIDTH-1:0]     ar_push_row_o,
    output logic [COL_WIDTH-1:0]     ar_push_col_o,
    output logic [IW-1:0]            ar_push_id_o,
    output logic [3:0]               ar_push_qos_o,   // AxQOS -> CAM (QOS_EN pick)

    //=========================================================================
    // Snarf probe at the AR inlet (to the wr CAM). Combinational hit.
    //=========================================================================
    output logic                     snarf_probe_valid_o,
    output logic [RKW-1:0]           snarf_probe_rank_o,
    output logic [BKW-1:0]           snarf_probe_bank_o,
    output logic [ROW_WIDTH-1:0]     snarf_probe_row_o,
    output logic [COL_WIDTH-1:0]     snarf_probe_col_o,
    output logic [IW-1:0]            snarf_probe_id_o,     // read AXI id
    output logic [7:0]               snarf_probe_len_o,    // read AXI arlen
    input  logic                     snarf_hit_i,
    output logic                     snarf_accept_o,   // AR admitted AND hit

    //=========================================================================
    // Snarf data stream (captured burst from the CAM, in snarf-admit order)
    //=========================================================================
    input  logic                     snarf_rd_valid_i,
    output logic                     snarf_rd_ready_o,
    input  logic [DW-1:0]            snarf_rd_data_i,
    input  logic                     snarf_rd_last_i,

    //=========================================================================
    // DFI read-return stream (for MISS reads, in ar_push order)
    //=========================================================================
    input  logic                     dfi_rd_valid_i,
    output logic                     dfi_rd_ready_o,
    input  logic [DW-1:0]            dfi_rd_data_i,
    input  logic                     dfi_rd_last_i,
    input  logic [1:0]               dfi_rd_resp_i,

    output logic                     busy_o
);

    import pumice_pkg::*;

    localparam logic SRC_DFI   = 1'b0;
    localparam logic SRC_SNARF = 1'b1;

    // ---- post-skid AXI (from axi4_slave_rd) --------------------------------
    logic [IW-1:0] fub_arid;    logic [AW-1:0] fub_araddr;  logic [7:0] fub_arlen;
    logic [2:0]    fub_arsize;  logic [1:0]    fub_arburst; logic       fub_arlock;
    logic [3:0]    fub_arcache; logic [2:0]    fub_arprot;  logic [3:0] fub_arqos;
    logic [3:0]    fub_arregion;logic [UW-1:0] fub_aruser;
    logic          fub_arvalid; logic          fub_arready;

    logic [IW-1:0] fub_rid;     logic [DW-1:0] fub_rdata;   logic [1:0] fub_rresp;
    logic          fub_rlast;   logic [UW-1:0] fub_ruser;   logic       fub_rvalid;
    logic          fub_rready;
    logic          w_slave_busy;

    axi4_slave_rd #(
        .SKID_DEPTH_AR (SKID_DEPTH_AR),
        .SKID_DEPTH_R  (SKID_DEPTH_R),
        .AXI_ID_WIDTH  (IW),
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_USER_WIDTH(UW)
    ) u_slave_rd (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .s_axi_arid      (s_axi_arid),
        .s_axi_araddr    (s_axi_araddr),
        .s_axi_arlen     (s_axi_arlen),
        .s_axi_arsize    (s_axi_arsize),
        .s_axi_arburst   (s_axi_arburst),
        .s_axi_arlock    (s_axi_arlock),
        .s_axi_arcache   (s_axi_arcache),
        .s_axi_arprot    (s_axi_arprot),
        .s_axi_arqos     (s_axi_arqos),
        .s_axi_arregion  (s_axi_arregion),
        .s_axi_aruser    (s_axi_aruser),
        .s_axi_arvalid   (s_axi_arvalid),
        .s_axi_arready   (s_axi_arready),
        .s_axi_rid       (s_axi_rid),
        .s_axi_rdata     (s_axi_rdata),
        .s_axi_rresp     (s_axi_rresp),
        .s_axi_rlast     (s_axi_rlast),
        .s_axi_ruser     (s_axi_ruser),
        .s_axi_rvalid    (s_axi_rvalid),
        .s_axi_rready    (s_axi_rready),
        .fub_axi_arid    (fub_arid),
        .fub_axi_araddr  (fub_araddr),
        .fub_axi_arlen   (fub_arlen),
        .fub_axi_arsize  (fub_arsize),
        .fub_axi_arburst (fub_arburst),
        .fub_axi_arlock  (fub_arlock),
        .fub_axi_arcache (fub_arcache),
        .fub_axi_arprot  (fub_arprot),
        .fub_axi_arqos   (fub_arqos),
        .fub_axi_arregion(fub_arregion),
        .fub_axi_aruser  (fub_aruser),
        .fub_axi_arvalid (fub_arvalid),
        .fub_axi_arready (fub_arready),
        .fub_axi_rid     (fub_rid),
        .fub_axi_rdata   (fub_rdata),
        .fub_axi_rresp   (fub_rresp),
        .fub_axi_rlast   (fub_rlast),
        .fub_axi_ruser   (fub_ruser),
        .fub_axi_rvalid  (fub_rvalid),
        .fub_axi_rready  (fub_rready),
        .busy            (w_slave_busy)
    );

    // ---- decode the AR at the inlet ----------------------------------------
    logic [RKW-1:0]       w_rank;
    logic [BKW-1:0]       w_bank;
    logic [ROW_WIDTH-1:0] w_row;
    logic [COL_WIDTH-1:0] w_col;

    // Align the mapped address DOWN to the AXI BEAT. addr_mapper indexes at
    // DEVICE-word granularity (BYTE_OFFSET_WIDTH = log2(DRAM_DEVICE_WIDTH/8)),
    // which is FINER than one AXI beat whenever a beat spans several device
    // words -- e.g. a 128-bit beat over a 64-bit device word. The byte lanes
    // inside a beat are already carried by WSTRB, so an unaligned start
    // address must NOT also shift the column: doing both counts the offset
    // twice and the write lands a beat further on, leaving the requested
    // address untouched. AXI4 requires exactly this: an unaligned first beat
    // keeps the aligned address and narrows the strobes.
    //
    // Aligned traffic is bit-identical (the low bits are already zero). The
    // 64->128 dwidth converter is what produces unaligned beats here, by
    // turning one narrow host beat into a wide beat in its lane.
    localparam int BEAT_BO = $clog2(DW / 8);
    logic [AW-1:0] w_map_addr_rd;
    assign w_map_addr_rd = {fub_araddr[AW-1:BEAT_BO], {BEAT_BO{1'b0}}};

    addr_mapper #(
        .AXI_ADDR_WIDTH   (AW),
        .NUM_RANKS        (NUM_RANKS),
        .NUM_BANKS        (NUM_BANKS),
        .ROW_WIDTH        (ROW_WIDTH),
        .COL_WIDTH        (COL_WIDTH),
        .BYTE_OFFSET_WIDTH(BYTE_OFFSET_WIDTH)
    ) u_addr_mapper (
        .axi_addr_i (w_map_addr_rd),
        .bank_lsb_i (bank_lsb_i),
        .hash_en_i  (hash_en_i),
        .hash_seed_i(hash_seed_i),
        .rank_o     (w_rank),
        .bank_o     (w_bank),
        .row_o      (w_row),
        .col_o      (w_col)
    );

    // snarf probe = combinational lookup of the AR under inspection
    assign snarf_probe_valid_o = fub_arvalid;
    assign snarf_probe_rank_o  = w_rank;
    assign snarf_probe_bank_o  = w_bank;
    assign snarf_probe_row_o   = w_row;
    assign snarf_probe_col_o   = w_col;
    assign snarf_probe_id_o    = fub_arid;
    assign snarf_probe_len_o   = fub_arlen;

    logic w_hit;
    assign w_hit = snarf_hit_i;

    // ---- aggregation sideband skid-alignment FIFO --------------------------
    // ar_last_i arrives with s_axi_ar (pre-skid). axi4_slave_rd buffers AR in
    // order (registered skid, >=1 cycle), so capture the sideband on s_axi_ar
    // acceptance and replay it on fub_ar admission (1:1, in order), where it
    // rides into the AR-order FIFO to collapse per-sub RLAST.
    logic       w_side_wr_valid, w_side_rd_ready;
    logic [1:0] w_side_data;
    logic       w_side_agg, w_side_last;

    assign w_side_wr_valid = s_axi_arvalid && s_axi_arready;

    gaxi_fifo_sync #(.DATA_WIDTH(2), .DEPTH(SKID_DEPTH_AR + AR_FIFO_DEPTH)) u_ar_side_fifo (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_side_wr_valid),
        .wr_data    ({ar_agg_i, ar_last_i}),
        .rd_ready   (w_side_rd_ready),
        .rd_valid   (),
        .rd_data    (w_side_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .wr_ready(),
        .count   ()
        /* verilator lint_on PINCONNECTEMPTY */
    );
    assign {w_side_agg, w_side_last} = w_side_data;

    // ---- order FIFO : {orig_agg, orig_last, source, len, id} ---------------
    // `len` is the sub-command's AxLEN. A DRAM burst always returns AXI_BEATS_PER_BURST beats,
    // but the host may have asked for FEWER (any legal AxLEN, down to a single
    // beat). The beats past the request are drained from the CAM and DROPPED
    // here rather than pushed at the host -- without this a 1-beat read got AXI_BEATS_PER_BURST
    // R beats and the read never framed correctly.
    localparam int ORD_W = 3 + 8 + IW;

    logic             w_ord_wr_valid, w_ord_wr_ready;
    logic [ORD_W-1:0] w_ord_wr_data;
    logic             w_ord_rd_valid, w_ord_rd_ready;
    logic [ORD_W-1:0] w_ord_rd_data;

    // The snarf probe is REGISTERED in the wr CAM (pipelines the rd_intake->
    // wr_cam cross-module route, the worst w_sys_i path), so the hit lands one
    // cycle after the probe is presented. r_armed marks that the registered
    // probe belongs to the CURRENT head AR (the AR was held stable last cycle);
    // only then is w_hit meaningful and the AR admissible. This costs one extra
    // cycle of admit latency per read (reads self-limit to <= DRAM read rate, so
    // no sustained-throughput loss), and does not change the RAW-forward result
    // (the compare still runs against the live wr-CAM state at admit).
    logic r_armed, w_can_admit, w_admit;
    assign w_can_admit = w_ord_wr_ready && (w_hit ? 1'b1 : ar_push_ready_i);
    assign w_admit     = fub_arvalid && r_armed && w_can_admit;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_armed <= 1'b0;
        else                        r_armed <= fub_arvalid && !w_admit;
    )

    assign fub_arready    = r_armed && w_can_admit;
    assign w_ord_wr_valid = w_admit;
    // pop the sideband in lockstep with the order-FIFO write (fub_ar admit)
    assign w_side_rd_ready = w_ord_wr_valid;
    assign w_ord_wr_data  = {w_side_agg, w_side_last, w_hit /*SRC_SNARF=1*/,
                             fub_arlen, fub_arid};

    // snarf accept = this AR was admitted as a snarf hit
    assign snarf_accept_o = w_admit && w_hit;

    // MISS -> ar_push (fires with admission)
    assign ar_push_valid_o = fub_arvalid && r_armed && !w_hit && w_ord_wr_ready;
    assign ar_push_rank_o  = w_rank;
    assign ar_push_bank_o  = w_bank;
    assign ar_push_row_o   = w_row;
    assign ar_push_col_o   = w_col;
    assign ar_push_id_o    = fub_arid;
    assign ar_push_qos_o   = fub_arqos;

    gaxi_fifo_sync #(.DATA_WIDTH(ORD_W), .DEPTH(ORDER_FIFO_DEPTH)) u_order_fifo (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_ord_wr_valid),
        .wr_ready   (w_ord_wr_ready),
        .wr_data    (w_ord_wr_data),
        .rd_ready   (w_ord_rd_ready),
        .count      (),
        .rd_valid   (w_ord_rd_valid),
        .rd_data    (w_ord_rd_data)
    );

    logic          w_head_agg, w_head_last, w_head_src;
    logic [IW-1:0] w_head_id;
    logic [7:0]    w_head_len;
    assign {w_head_agg, w_head_last, w_head_src,
            w_head_len, w_head_id} = w_ord_rd_data;

    // ---- source arbiter : select snarf/DFI by the order-FIFO head ----------
    logic          w_src_valid, w_src_last;
    logic [DW-1:0] w_src_data;
    logic [1:0]    w_src_resp;

    always_comb begin
        if (w_head_src == SRC_SNARF) begin
            w_src_valid = snarf_rd_valid_i;
            w_src_data  = snarf_rd_data_i;
            w_src_last  = snarf_rd_last_i;
            w_src_resp  = 2'b00; // OKAY
        end else begin
            w_src_valid = dfi_rd_valid_i;
            w_src_data  = dfi_rd_data_i;
            w_src_last  = dfi_rd_last_i;
            w_src_resp  = dfi_rd_resp_i;
        end
    end

    // ---- rd-data FIFO : {resp, last, id, data} -----------------------------
    localparam int RD_W = 2 + 1 + IW + DW;

    logic            w_rd_wr_valid, w_rd_wr_ready;
    logic [RD_W-1:0] w_rd_wr_data;
    logic            w_rd_rd_valid, w_rd_rd_ready;
    logic [RD_W-1:0] w_rd_rd_data;

    // A source beat is consumed when the head is valid, the source has a beat,
    // and the rd-data FIFO has room.
    // Beats the host actually asked for are FORWARDED; the remainder of the
    // DRAM burst is consumed from the source and dropped. A dropped beat needs
    // no room in the rd-data FIFO, so it must not wait on w_rd_wr_ready.
    logic       w_fwd_beat, w_sub_last;
    logic [7:0] r_fwd;                 // beats forwarded so far, this sub
    assign w_fwd_beat = (r_fwd <= w_head_len);
    assign w_sub_last = (r_fwd == w_head_len);

    logic w_beat_fire;
    assign w_beat_fire   = w_ord_rd_valid && w_src_valid
                           && (!w_fwd_beat || w_rd_wr_ready);

    assign w_rd_wr_valid = w_ord_rd_valid && w_src_valid && w_fwd_beat;
    // Collapse per-sub RLAST: for a split (agg=1) the host sees RLAST only on
    // the final beat of the final sub (w_head_last); a non-split read (agg=0)
    // passes RLAST per sub unchanged. The order FIFO still pops per sub (on
    // w_src_last) to advance through the burst's sub-commands.
    // RLAST rides the last REQUESTED beat, not the last beat the DRAM burst
    // happened to return (w_src_last), which may be several beats later.
    assign w_rd_wr_data  = {w_src_resp,
                            w_sub_last && (!w_head_agg || w_head_last),
                            w_head_id, w_src_data};

    // Ready back to whichever source the head selects.
    assign snarf_rd_ready_o = w_ord_rd_valid && (w_head_src == SRC_SNARF)
                              && (!w_fwd_beat || w_rd_wr_ready);
    assign dfi_rd_ready_o   = w_ord_rd_valid && (w_head_src == SRC_DFI)
                              && (!w_fwd_beat || w_rd_wr_ready);

    // Pop the order FIFO when the last beat of the burst is accepted.
    assign w_ord_rd_ready = w_beat_fire && w_src_last;

    // Forward counter: advances per consumed beat, rearms when the DRAM burst
    // ends (which is also when the order FIFO pops to the next sub-command).
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))  r_fwd <= 8'd0;
        else if (w_beat_fire)        r_fwd <= w_src_last ? 8'd0 : (r_fwd + 8'd1);
    )

    gaxi_fifo_sync #(.DATA_WIDTH(RD_W), .DEPTH(RD_FIFO_DEPTH)) u_rd_data_fifo (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_rd_wr_valid),
        .wr_ready   (w_rd_wr_ready),
        .wr_data    (w_rd_wr_data),
        .rd_ready   (w_rd_rd_ready),
        .count      (),
        .rd_valid   (w_rd_rd_valid),
        .rd_data    (w_rd_rd_data)
    );

    assign {fub_rresp, fub_rlast, fub_rid, fub_rdata} = w_rd_rd_data;
    assign fub_ruser  = '0;
    assign fub_rvalid = w_rd_rd_valid;
    assign w_rd_rd_ready = fub_rready;

    assign busy_o = w_ord_rd_valid || w_rd_rd_valid || w_slave_busy;

endmodule : pumice_rd_intake
