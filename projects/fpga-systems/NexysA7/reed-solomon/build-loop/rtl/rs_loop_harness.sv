// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rs_loop_harness
// Purpose:
//   The Reed-Solomon loop under host control: pattern generator -> RS encoder
//   -> error injector -> two RS decoders (riBM and Euclid, fed the same coded
//   stream) -> a pattern checker per decoder, plus a beat-by-beat comparator
//   of the two decoders and per-block verdict tallies, all behind one CSR
//   block on AXI4-Lite.
//
// Documentation: projects/fpga-systems/NexysA7/reed-solomon/README.md
// Subsystem: reed-solomon (NexysA7 harness)
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: rs_loop_harness
//==============================================================================
// Description:
//   How the two solvers are validated on the board: the same corrupted blocks
//   reach both decoders, each decoder's output is checked against the
//   generator's regenerated pattern and CRC (so a decoder that corrects is
//   proven against a reference that never saw the errors), and a comparator
//   requires the two decoders to agree beat for beat and verdict for verdict.
//   With more than t errors per block neither decoder can restore the data,
//   so the checkers report a CRC mismatch there by design; the verdict tallies
//   (uncorrectable) and the comparator are the evidence in that regime.
//
//   The error injector sits AFTER the encoder. An error injected into the
//   generator's data would be encoded faithfully and be invisible to the code,
//   which is why the generator was not given an injection mode.
//
//   Bypass mode routes the generator straight to both checkers, proving the
//   generator / checker / CRC / UART plumbing with the codec out of the loop.
//
//   Geometry comes from rs_loop_cfg_pkg only.
//
//==============================================================================

module rs_loop_harness
    import rs_loop_cfg_pkg::*;
    import rs_loop_regs_pkg::*;
#(
    parameter int AXIL_ADDR_WIDTH = 12
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // AXI4-Lite slave (from the UART bridge)
    input  logic [AXIL_ADDR_WIDTH-1:0]  s_axil_awaddr,
    input  logic [2:0]                  s_axil_awprot,
    input  logic                        s_axil_awvalid,
    output logic                        s_axil_awready,
    input  logic [31:0]                 s_axil_wdata,
    input  logic [3:0]                  s_axil_wstrb,
    input  logic                        s_axil_wvalid,
    output logic                        s_axil_wready,
    output logic [1:0]                  s_axil_bresp,
    output logic                        s_axil_bvalid,
    input  logic                        s_axil_bready,
    input  logic [AXIL_ADDR_WIDTH-1:0]  s_axil_araddr,
    input  logic [2:0]                  s_axil_arprot,
    input  logic                        s_axil_arvalid,
    output logic                        s_axil_arready,
    output logic [31:0]                 s_axil_rdata,
    output logic [1:0]                  s_axil_rresp,
    output logic                        s_axil_rvalid,
    input  logic                        s_axil_rready,

    // for the board's LEDs
    output logic                        o_busy,
    output logic                        o_gen_done,
    output logic                        o_chk_a_ok,
    output logic                        o_chk_b_ok,
    output logic                        o_cmp_err
);

    localparam int M    = CFG_SYMBOL_WIDTH;
    localparam int T    = CFG_T_SYMBOLS;
    localparam int N    = CFG_N_SYMBOLS;
    localparam int S    = CFG_SPB;
    localparam int DW   = CFG_DATA_WIDTH;
    localparam int SC_W = $clog2(T + 1);

    // =========================================================================
    // CSR block: AXI-Lite -> passthrough cpuif -> generated regblock
    // =========================================================================
    logic        w_cpuif_req, w_cpuif_req_is_wr, w_cpuif_stall_wr, w_cpuif_stall_rd;
    logic [AXIL_ADDR_WIDTH-1:0] w_cpuif_addr;
    logic [31:0] w_cpuif_wr_data, w_cpuif_wr_biten, w_cpuif_rd_data;
    logic        w_cpuif_rd_ack, w_cpuif_rd_err, w_cpuif_wr_ack, w_cpuif_wr_err;

    rs_loop_regs__in_t  hwif_in;
    rs_loop_regs__out_t hwif_out;

    axil4_to_peakrdl #(.ADDR_WIDTH(AXIL_ADDR_WIDTH), .DATA_WIDTH(32)) u_axil2cpuif (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_awaddr(s_axil_awaddr), .s_axil_awprot(s_axil_awprot),
        .s_axil_awvalid(s_axil_awvalid), .s_axil_awready(s_axil_awready),
        .s_axil_wdata(s_axil_wdata), .s_axil_wstrb(s_axil_wstrb),
        .s_axil_wvalid(s_axil_wvalid), .s_axil_wready(s_axil_wready),
        .s_axil_bresp(s_axil_bresp), .s_axil_bvalid(s_axil_bvalid), .s_axil_bready(s_axil_bready),
        .s_axil_araddr(s_axil_araddr), .s_axil_arprot(s_axil_arprot),
        .s_axil_arvalid(s_axil_arvalid), .s_axil_arready(s_axil_arready),
        .s_axil_rdata(s_axil_rdata), .s_axil_rresp(s_axil_rresp),
        .s_axil_rvalid(s_axil_rvalid), .s_axil_rready(s_axil_rready),
        .cpuif_req(w_cpuif_req), .cpuif_req_is_wr(w_cpuif_req_is_wr), .cpuif_addr(w_cpuif_addr),
        .cpuif_wr_data(w_cpuif_wr_data), .cpuif_wr_biten(w_cpuif_wr_biten),
        .cpuif_req_stall_wr(w_cpuif_stall_wr), .cpuif_req_stall_rd(w_cpuif_stall_rd),
        .cpuif_rd_ack(w_cpuif_rd_ack), .cpuif_rd_err(w_cpuif_rd_err), .cpuif_rd_data(w_cpuif_rd_data),
        .cpuif_wr_ack(w_cpuif_wr_ack), .cpuif_wr_err(w_cpuif_wr_err));

    rs_loop_regs u_regs (
        .clk(aclk), .rst(!aresetn),
        .s_cpuif_req(w_cpuif_req), .s_cpuif_req_is_wr(w_cpuif_req_is_wr),
        .s_cpuif_addr(w_cpuif_addr[6:0]),
        .s_cpuif_wr_data(w_cpuif_wr_data), .s_cpuif_wr_biten(w_cpuif_wr_biten),
        .s_cpuif_req_stall_wr(w_cpuif_stall_wr), .s_cpuif_req_stall_rd(w_cpuif_stall_rd),
        .s_cpuif_rd_ack(w_cpuif_rd_ack), .s_cpuif_rd_err(w_cpuif_rd_err), .s_cpuif_rd_data(w_cpuif_rd_data),
        .s_cpuif_wr_ack(w_cpuif_wr_ack), .s_cpuif_wr_err(w_cpuif_wr_err),
        .hwif_in(hwif_in), .hwif_out(hwif_out));

    // -------------------------------------------------------------------------
    // Control decode
    // -------------------------------------------------------------------------
    logic        w_start, w_clear, w_soft_reset, w_bypass;
    logic        dp_rstn;            // datapath reset: board reset or CTRL.soft_reset
    logic [15:0] w_blocks;

    assign w_start      = hwif_out.CTRL.start.value;
    assign w_clear      = hwif_out.CTRL.clear.value;
    assign w_soft_reset = hwif_out.CTRL.soft_reset.value;
    assign w_bypass     = hwif_out.CTRL.bypass.value;
    assign w_blocks     = hwif_out.GEN_BLOCKS.blocks.value;

    // registered so the pulse becomes a clean one-cycle reset of the datapath
    logic r_dp_rst_pulse;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_dp_rst_pulse <= 1'b0;
        else                        r_dp_rst_pulse <= w_soft_reset;
    )
    assign dp_rstn = aresetn && !r_dp_rst_pulse;

    // =========================================================================
    // Pattern generator (one channel, 32-bit beats, one packet per block)
    // =========================================================================
    logic        gen_tvalid, gen_tready, gen_tlast;
    logic [DW-1:0]   gen_tdata;
    logic [DW/8-1:0] gen_tstrb;
    logic        gen_busy, gen_done;
    logic [0:0][31:0] gen_crc;
    logic [0:0]       gen_crc_valid;
    logic [0:0][31:0] gen_beats_ch;
    logic [31:0] gen_beats_total;
    logic [31:0] w_num_beats;

    assign w_num_beats = 32'(w_blocks) * 32'(CFG_K_BEATS);

    /* verilator lint_off PINCONNECTEMPTY */
    axis4_master_pattern_gen #(
        .NUM_CHANNELS(1), .AXIS_DATA_WIDTH(DW), .AXIS_ID_WIDTH(1), .AXIS_DEST_WIDTH(1), .AXIS_USER_WIDTH(1)
    ) u_gen (
        .clk(aclk), .rst_n(dp_rstn),
        .cfg_start(w_start), .cfg_lfsr_seed(hwif_out.GEN_SEED.value.value),
        .cfg_channel_mask(1'b1), .cfg_num_beats(w_num_beats),
        .cfg_beats_per_pkt(32'(CFG_K_BEATS)), .cfg_interleave(1'b0),
        .cfg_tdest(1'b0), .cfg_last_bytes(8'd0),
        .cfg_busy(gen_busy), .cfg_done(gen_done),
        .o_expected_crc(gen_crc), .o_expected_crc_valid(gen_crc_valid),
        .o_beat_count(gen_beats_ch), .o_beat_count_total(gen_beats_total),
        .m_axis_tvalid(gen_tvalid), .m_axis_tready(gen_tready),
        .m_axis_tdata(gen_tdata), .m_axis_tstrb(gen_tstrb), .m_axis_tlast(gen_tlast),
        .m_axis_tid(), .m_axis_tdest(), .m_axis_tuser());
    /* verilator lint_on PINCONNECTEMPTY */

    // =========================================================================
    // Encoder -> injector -> two decoders
    // =========================================================================
    logic          enc_in_valid, enc_in_ready, enc_out_valid, enc_out_ready, enc_out_last, enc_frame_err;
    logic [DW-1:0] enc_out_data;
    logic [S-1:0]  enc_out_keep;

    // the generator's tstrb is a byte mask; at m = 8 it is the symbol keep
    assign enc_in_valid = gen_tvalid && !w_bypass;

    rs_encoder_core #(
        .SYMBOL_WIDTH(M), .PRIM_POLY(CFG_PRIM_POLY), .T_SYMBOLS(T), .N_SYMBOLS(N),
        .FIRST_ROOT(CFG_FIRST_ROOT), .DATA_WIDTH(DW)
    ) u_enc (
        .aclk(aclk), .aresetn(dp_rstn),
        .in_valid(enc_in_valid), .in_ready(enc_in_ready), .in_data(gen_tdata),
        .in_keep(gen_tstrb), .in_last(gen_tlast),
        .out_valid(enc_out_valid), .out_ready(enc_out_ready), .out_data(enc_out_data),
        .out_keep(enc_out_keep), .out_last(enc_out_last),
        .frame_err(enc_frame_err));

    logic          inj_out_valid, inj_out_ready, inj_out_last;
    logic [DW-1:0] inj_out_data;
    logic [S-1:0]  inj_out_keep;
    logic [31:0]   inj_symbols, inj_blocks, inj_over_t;
    logic [7:0]    inj_last;

    rs_error_injector #(
        .SYMBOL_WIDTH(M), .T_SYMBOLS(T), .N_SYMBOLS(N), .SYMBOLS_PER_BEAT(S)
    ) u_inj (
        .aclk(aclk), .aresetn(dp_rstn),
        .in_valid(enc_out_valid), .in_ready(enc_out_ready), .in_data(enc_out_data),
        .in_keep(enc_out_keep), .in_last(enc_out_last),
        .out_valid(inj_out_valid), .out_ready(inj_out_ready), .out_data(inj_out_data),
        .out_keep(inj_out_keep), .out_last(inj_out_last),
        .cfg_mode(hwif_out.INJ_CFG.mode.value), .cfg_count(hwif_out.INJ_CFG.errors.value),
        .cfg_rate(hwif_out.INJ_CFG.rate.value), .cfg_seed(hwif_out.INJ_SEED.value.value),
        .cfg_seed_load(w_start && hwif_out.CTRL.inj_seed_on_start.value), .cfg_clear(w_clear),
        .o_inj_symbols(inj_symbols), .o_inj_blocks(inj_blocks), .o_inj_over_t(inj_over_t),
        .o_last_block_errors(inj_last));

    // broadcast to the two decoders: a beat moves when both can take it
    logic          dec_in_ready [2];
    logic          dec_out_valid [2], dec_out_ready [2], dec_out_last [2];
    logic [DW-1:0] dec_out_data [2];
    logic [S-1:0]  dec_out_keep [2];
    logic          dec_ok [2], dec_unc [2], dec_frame [2];
    logic [SC_W-1:0] dec_corr [2];

    assign inj_out_ready = dec_in_ready[0] && dec_in_ready[1];

    for (genvar d = 0; d < 2; d++) begin : g_dec
        rs_decoder_core #(
            .SYMBOL_WIDTH(M), .PRIM_POLY(CFG_PRIM_POLY), .T_SYMBOLS(T), .N_SYMBOLS(N),
            .FIRST_ROOT(CFG_FIRST_ROOT), .DATA_WIDTH(DW),
            .KES_ALGO((d == 0) ? CFG_KES_A : CFG_KES_B)
        ) u_dec (
            .aclk(aclk), .aresetn(dp_rstn),
            .in_valid(inj_out_valid && dec_in_ready[1-d]), .in_ready(dec_in_ready[d]),
            .in_data(inj_out_data), .in_keep(inj_out_keep), .in_last(inj_out_last),
            .out_valid(dec_out_valid[d]), .out_ready(dec_out_ready[d]), .out_data(dec_out_data[d]),
            .out_keep(dec_out_keep[d]), .out_last(dec_out_last[d]),
            .out_status_ok(dec_ok[d]), .out_status_corrected(dec_corr[d]),
            .out_status_uncorrectable(dec_unc[d]), .out_status_frame_err(dec_frame[d]));
    end

    // =========================================================================
    // Checkers: one per decoder; in bypass both watch the generator directly
    // =========================================================================
    logic          chk_tvalid [2], chk_tready [2], chk_tlast [2];
    logic [DW-1:0] chk_tdata [2];
    logic [DW/8-1:0] chk_tstrb [2];
    logic          chk_ready_en [2];
    logic [0:0][31:0] chk_crc [2];
    logic [0:0]       chk_crc_valid [2];
    logic          chk_data_err [2];
    logic [31:0]   chk_pkts [2];
    logic [0:0][31:0] chk_beats_ch [2];
    logic [31:0]   chk_beats_total [2];

    // random ready for back-pressure runs
    logic [15:0] w_thr_lfsr;
    /* verilator lint_off PINCONNECTEMPTY */
    shifter_lfsr #(.WIDTH(16), .TAP_INDEX_WIDTH(12), .TAP_COUNT(4)) u_thr (
        .clk(aclk), .rst_n(dp_rstn), .enable(1'b1), .seed_load(w_start),
        .seed_data(16'hB5A3), .taps({12'd16, 12'd15, 12'd13, 12'd4}), .lfsr_out(w_thr_lfsr), .lfsr_done());
    /* verilator lint_on PINCONNECTEMPTY */
    assign chk_ready_en[0] = !hwif_out.CTRL.throttle_a.value || w_thr_lfsr[0];
    assign chk_ready_en[1] = !hwif_out.CTRL.throttle_b.value || w_thr_lfsr[7];

    always_comb begin
        for (int d = 0; d < 2; d++) begin
            if (w_bypass) begin
                chk_tvalid[d] = gen_tvalid && chk_tready[1-d];
                chk_tdata[d]  = gen_tdata;
                chk_tstrb[d]  = gen_tstrb;
                chk_tlast[d]  = gen_tlast;
            end else begin
                chk_tvalid[d] = dec_out_valid[d];
                chk_tdata[d]  = dec_out_data[d];
                chk_tstrb[d]  = dec_out_keep[d];
                chk_tlast[d]  = dec_out_last[d];
            end
            dec_out_ready[d] = !w_bypass && chk_tready[d];
        end
        gen_tready = w_bypass ? (chk_tready[0] && chk_tready[1]) : enc_in_ready;
    end

    for (genvar d = 0; d < 2; d++) begin : g_chk
        axis4_slave_pattern_check #(
            .NUM_CHANNELS(1), .AXIS_DATA_WIDTH(DW), .AXIS_ID_WIDTH(1), .AXIS_DEST_WIDTH(1), .AXIS_USER_WIDTH(1)
        ) u_chk (
            .clk(aclk), .rst_n(dp_rstn),
            .cfg_start(w_start), .cfg_lfsr_seed(hwif_out.GEN_SEED.value.value),
            .ready_en(chk_ready_en[d]),
            .o_actual_crc(chk_crc[d]), .o_actual_crc_valid(chk_crc_valid[d]),
            .o_data_error(chk_data_err[d]),
            .o_beat_count(chk_beats_ch[d]), .o_beat_count_total(chk_beats_total[d]),
            .o_pkt_count(chk_pkts[d]),
            .s_axis_tvalid(chk_tvalid[d]), .s_axis_tready(chk_tready[d]),
            .s_axis_tdata(chk_tdata[d]), .s_axis_tstrb(chk_tstrb[d]), .s_axis_tlast(chk_tlast[d]),
            .s_axis_tid(1'b0), .s_axis_tdest(1'b0), .s_axis_tuser(1'b0));
    end

    // =========================================================================
    // Per-decoder verdict tallies
    // =========================================================================
    logic [31:0] r_blk_ok [2], r_blk_corr [2], r_blk_unc [2], r_blk_frame [2], r_sym_corr [2];

    for (genvar d = 0; d < 2; d++) begin : g_tally
        logic w_fire, w_last;
        assign w_fire = dec_out_valid[d] && dec_out_ready[d];
        assign w_last = w_fire && dec_out_last[d];
        `ALWAYS_FF_RST(aclk, dp_rstn,
            if (`RST_ASSERTED(dp_rstn)) begin
                r_blk_ok[d] <= '0; r_blk_corr[d] <= '0; r_blk_unc[d] <= '0;
                r_blk_frame[d] <= '0; r_sym_corr[d] <= '0;
            end else if (w_clear) begin
                r_blk_ok[d] <= '0; r_blk_corr[d] <= '0; r_blk_unc[d] <= '0;
                r_blk_frame[d] <= '0; r_sym_corr[d] <= '0;
            end else if (w_last) begin
                if (dec_frame[d])                 r_blk_frame[d] <= r_blk_frame[d] + 32'd1;
                else if (dec_unc[d])              r_blk_unc[d]   <= r_blk_unc[d] + 32'd1;
                else if (dec_ok[d])               r_blk_ok[d]    <= r_blk_ok[d] + 32'd1;
                else begin
                    r_blk_corr[d] <= r_blk_corr[d] + 32'd1;
                    r_sym_corr[d] <= r_sym_corr[d] + 32'(dec_corr[d]);
                end
            end
        )
    end

    // =========================================================================
    // Comparator: the two decoders must agree beat for beat and on the verdict
    // =========================================================================
    localparam int CMP_W = 1 + S + DW + 3 + SC_W;
    logic             cmp_wr_ready [2], cmp_rd_valid [2];
    logic [CMP_W-1:0] cmp_rd_data [2];
    logic             w_cmp_pop;
    logic [31:0]      r_cmp_data_mm, r_cmp_status_mm, r_cmp_beats;
    logic             r_cmp_err;

    for (genvar d = 0; d < 2; d++) begin : g_cmp_fifo
        /* verilator lint_off PINCONNECTEMPTY */
        gaxi_fifo_sync #(.DATA_WIDTH(CMP_W), .DEPTH(64), .REGISTERED(0)) u_fifo (
            .axi_aclk(aclk), .axi_aresetn(dp_rstn),
            .wr_valid(dec_out_valid[d] && dec_out_ready[d]), .wr_ready(cmp_wr_ready[d]),
            .wr_data({dec_out_last[d], dec_out_keep[d], dec_out_data[d],
                      dec_ok[d], dec_unc[d], dec_frame[d], dec_corr[d]}),
            .rd_ready(w_cmp_pop), .count(), .rd_valid(cmp_rd_valid[d]), .rd_data(cmp_rd_data[d]));
        /* verilator lint_on PINCONNECTEMPTY */
    end

    assign w_cmp_pop = cmp_rd_valid[0] && cmp_rd_valid[1];

    logic w_cmp_data_diff, w_cmp_status_diff, w_cmp_is_last;
    assign w_cmp_data_diff   = cmp_rd_data[0][CMP_W-1 -: 1 + S + DW] != cmp_rd_data[1][CMP_W-1 -: 1 + S + DW];
    assign w_cmp_status_diff = cmp_rd_data[0][3 + SC_W - 1:0] != cmp_rd_data[1][3 + SC_W - 1:0];
    assign w_cmp_is_last     = cmp_rd_data[0][CMP_W-1];

    `ALWAYS_FF_RST(aclk, dp_rstn,
        if (`RST_ASSERTED(dp_rstn)) begin
            r_cmp_data_mm <= '0; r_cmp_status_mm <= '0; r_cmp_beats <= '0; r_cmp_err <= 1'b0;
        end else if (w_clear) begin
            r_cmp_data_mm <= '0; r_cmp_status_mm <= '0; r_cmp_beats <= '0; r_cmp_err <= 1'b0;
        end else if (w_cmp_pop) begin
            r_cmp_beats <= r_cmp_beats + 32'd1;
            if (w_cmp_data_diff) begin r_cmp_data_mm <= r_cmp_data_mm + 32'd1; r_cmp_err <= 1'b1; end
            if (w_cmp_is_last && w_cmp_status_diff) begin
                r_cmp_status_mm <= r_cmp_status_mm + 32'd1; r_cmp_err <= 1'b1;
            end
        end
    )

    // =========================================================================
    // Run timer and done flags
    // =========================================================================
    logic        r_busy, r_gen_done;
    logic [31:0] r_cycles;
    logic        w_chk_a_done, w_chk_b_done, w_all_done;

    assign w_chk_a_done = (chk_pkts[0] == 32'(w_blocks));
    assign w_chk_b_done = (chk_pkts[1] == 32'(w_blocks));
    assign w_all_done   = r_gen_done && w_chk_a_done && w_chk_b_done;

    `ALWAYS_FF_RST(aclk, dp_rstn,
        if (`RST_ASSERTED(dp_rstn)) begin
            r_busy <= 1'b0; r_gen_done <= 1'b0; r_cycles <= '0;
        end else begin
            if (w_start) begin
                r_busy <= 1'b1; r_gen_done <= 1'b0; r_cycles <= '0;
            end else if (r_busy) begin
                r_cycles <= r_cycles + 32'd1;
                if (gen_done) r_gen_done <= 1'b1;
                if (w_all_done) r_busy <= 1'b0;
            end else if (gen_done) begin
                r_gen_done <= 1'b1;
            end
        end
    )

    logic w_crc_a_ok, w_crc_b_ok;
    assign w_crc_a_ok = chk_crc_valid[0][0] && gen_crc_valid[0] && (chk_crc[0][0] == gen_crc[0]);
    assign w_crc_b_ok = chk_crc_valid[1][0] && gen_crc_valid[0] && (chk_crc[1][0] == gen_crc[0]);

    assign o_busy     = r_busy;
    assign o_gen_done = r_gen_done;
    assign o_chk_a_ok = w_chk_a_done && !chk_data_err[0] && w_crc_a_ok;
    assign o_chk_b_ok = w_chk_b_done && !chk_data_err[1] && w_crc_b_ok;
    assign o_cmp_err  = r_cmp_err;

    // =========================================================================
    // Status back to the CSRs
    // =========================================================================
    always_comb begin
        hwif_in = '{default: '0};
        hwif_in.BUILD_ID.value.next      = CFG_BUILD_ID;
        hwif_in.STATUS.busy.next         = r_busy;
        hwif_in.STATUS.gen_done.next     = r_gen_done;
        hwif_in.STATUS.chk_a_done.next   = w_chk_a_done;
        hwif_in.STATUS.chk_b_done.next   = w_chk_b_done;
        hwif_in.STATUS.data_err_a.next   = chk_data_err[0];
        hwif_in.STATUS.data_err_b.next   = chk_data_err[1];
        hwif_in.STATUS.cmp_err.next      = r_cmp_err;
        hwif_in.STATUS.crc_a_ok.next     = w_crc_a_ok;
        hwif_in.STATUS.crc_b_ok.next     = w_crc_b_ok;
        hwif_in.PROFILE.n.next           = 16'(N);
        hwif_in.PROFILE.t.next           = 8'(T);
        hwif_in.PROFILE.m.next           = 4'(M);
        hwif_in.PROFILE.spb.next         = 4'(S);
        hwif_in.CRC_EXPECTED.value.next  = gen_crc[0];
        hwif_in.CRC_A.value.next         = chk_crc[0][0];
        hwif_in.CRC_B.value.next         = chk_crc[1][0];
        hwif_in.PKTS_A.value.next        = chk_pkts[0];
        hwif_in.PKTS_B.value.next        = chk_pkts[1];
        hwif_in.CYCLES.value.next        = r_cycles;
        hwif_in.BLK_OK_A.value.next      = r_blk_ok[0];
        hwif_in.BLK_CORR_A.value.next    = r_blk_corr[0];
        hwif_in.BLK_UNC_A.value.next     = r_blk_unc[0];
        hwif_in.BLK_FRAME_A.value.next   = r_blk_frame[0];
        hwif_in.SYM_CORR_A.value.next    = r_sym_corr[0];
        hwif_in.BLK_OK_B.value.next      = r_blk_ok[1];
        hwif_in.BLK_CORR_B.value.next    = r_blk_corr[1];
        hwif_in.BLK_UNC_B.value.next     = r_blk_unc[1];
        hwif_in.BLK_FRAME_B.value.next   = r_blk_frame[1];
        hwif_in.SYM_CORR_B.value.next    = r_sym_corr[1];
        hwif_in.INJ_SYMBOLS.value.next   = inj_symbols;
        hwif_in.INJ_BLOCKS.value.next    = inj_blocks;
        hwif_in.INJ_OVER_T.value.next    = inj_over_t;
        hwif_in.INJ_LAST.value.next      = inj_last;
        hwif_in.CMP_DATA_MISMATCH.value.next   = r_cmp_data_mm;
        hwif_in.CMP_STATUS_MISMATCH.value.next = r_cmp_status_mm;
        hwif_in.CMP_BEATS.value.next     = r_cmp_beats;
    end

    // unused outputs of the shared blocks
    logic unused_h;
    assign unused_h = gen_busy ^ enc_frame_err ^ (^gen_beats_total) ^ (^gen_beats_ch[0])
                    ^ (^chk_beats_total[0]) ^ (^chk_beats_total[1]) ^ (^chk_beats_ch[0][0]) ^ (^chk_beats_ch[1][0])
                    ^ cmp_wr_ready[0] ^ cmp_wr_ready[1] ^ (^w_cpuif_addr[AXIL_ADDR_WIDTH-1:7]);

endmodule : rs_loop_harness
