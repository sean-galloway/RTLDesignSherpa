// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: bch_loop_harness
// Purpose:
//   The BCH loop under host control: pattern generator -> BCH encoder ->
//   bit-granular error injector -> BCH decoder (RIBM) -> pattern checker,
//   all behind one CSR block on AXI4-Lite.
//
// Documentation: projects/fpga-systems/Genesys2/bch/README.md
// Subsystem: bch (NexysA7 harness)
//
// Author: sean galloway
// Created: 2026-10-04

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: bch_loop_harness
//==============================================================================
// Description:
//   Validates the landed BCH(4224,4120) t=8 component wrappers on the Nexys A7.
//   The same corrupted blocks reach one RIBM decoder, whose output is compared
//   beat by beat against the generator's regenerated pattern. Bypass mode
//   routes the generator straight to the checker to prove the generator /
//   checker / UART plumbing with the codec out of the loop.
//
//   The error injector sits AFTER the encoder. An error injected into the
//   generator's data would be encoded faithfully and be invisible to the code.
//
//   Geometry comes from bch_loop_cfg_pkg only.
//
//   Byte-granular checker (BYTE_CRC=1): the final recovered beat carries 24
//   valid bits (3 bytes), so the checker runs in byte mode. The generator is
//   reused as-is and strobes the same 3 bytes on the final beat; the checker's
//   CRC is then over the valid bytes only. The generator's o_expected_crc is
//   over full 32-bit words, so the RTL crc_a_ok compare is not byte-consistent
//   and is reported as a delivery hint only; the host computes the byte-granular
//   expected CRC in software.
//==============================================================================

module bch_loop_harness
    import bch_loop_cfg_pkg::*;
    import bch_loop_regs_pkg::*;
#(
    parameter int AXIL_ADDR_WIDTH = 32,
    parameter string IFACE        = "AXIS"
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

    initial begin : csr_fit_check
        if (BCH_LOOP_REGS_MIN_ADDR_WIDTH > 12)
            $error("bch_loop_harness: the register block needs %0d address bits, more than the 4 KB window",
                   BCH_LOOP_REGS_MIN_ADDR_WIDTH);
    end

    localparam int M    = CFG_FIELD_DIM;
    localparam int T    = CFG_T_BITS;
    localparam int N    = CFG_N_BITS;
    localparam int K    = CFG_K_BITS;
    localparam int DW   = CFG_DATA_WIDTH;
    localparam int S    = DW / 8;            // byte lanes per beat
    localparam int SC_W = $clog2(T + 1);

    // Control signals decoded from the CSRs further down.
    logic        w_start, w_clear, w_soft_reset, w_bypass;
    logic [15:0] w_blocks;

    // =========================================================================
    // Bus fabric: host AXI4-Lite -> generated 1x3 bridge -> APB slave windows
    // =========================================================================
    logic        bch_loop_apb_PSEL, bch_loop_apb_PENABLE, bch_loop_apb_PWRITE;
    logic        bch_loop_apb_PREADY, bch_loop_apb_PSLVERR;
    logic [31:0] bch_loop_apb_PADDR, bch_loop_apb_PWDATA, bch_loop_apb_PRDATA;
    logic [3:0]  bch_loop_apb_PSTRB;
    logic [2:0]  bch_loop_apb_PPROT;

    logic        bch_regs_apb_PSEL, bch_regs_apb_PENABLE, bch_regs_apb_PWRITE;
    logic [31:0] bch_regs_apb_PADDR, bch_regs_apb_PWDATA;
    logic [3:0]  bch_regs_apb_PSTRB;
    logic [2:0]  bch_regs_apb_PPROT;
    logic        obs_apb_PSEL, obs_apb_PENABLE, obs_apb_PWRITE;
    logic [31:0] w_obs_prdata;
    logic        w_obs_pready, w_obs_pslverr;
    logic [31:0] w_obs4_prdata;
    logic        w_obs4_pready, w_obs4_pslverr;
    logic [31:0] obs_apb_PADDR, obs_apb_PWDATA;
    logic [3:0]  obs_apb_PSTRB;
    logic [2:0]  obs_apb_PPROT;

    logic        w_unmapped_irq, w_unmapped_clear;
    logic [31:0] w_unmapped_addr;
    logic [31:0] w_unmapped_count;

    bridge_bch_loop_axil u_bridge (
        .aclk    (aclk),
        .aresetn (aresetn),

        .host_axi_awaddr  (s_axil_awaddr),      .host_axi_awprot  (s_axil_awprot),
        .host_axi_awvalid (s_axil_awvalid),     .host_axi_awready (s_axil_awready),
        .host_axi_wdata   (s_axil_wdata),       .host_axi_wstrb   (s_axil_wstrb),
        .host_axi_wvalid  (s_axil_wvalid),      .host_axi_wready  (s_axil_wready),
        .host_axi_bresp   (s_axil_bresp),       .host_axi_bvalid  (s_axil_bvalid),
        .host_axi_bready  (s_axil_bready),
        .host_axi_araddr  (s_axil_araddr),      .host_axi_arprot  (s_axil_arprot),
        .host_axi_arvalid (s_axil_arvalid),     .host_axi_arready (s_axil_arready),
        .host_axi_rdata   (s_axil_rdata),       .host_axi_rresp   (s_axil_rresp),
        .host_axi_rvalid  (s_axil_rvalid),      .host_axi_rready  (s_axil_rready),

        .bch_loop_apb_PSEL   (bch_loop_apb_PSEL),   .bch_loop_apb_PADDR  (bch_loop_apb_PADDR),
        .bch_loop_apb_PENABLE(bch_loop_apb_PENABLE), .bch_loop_apb_PWRITE(bch_loop_apb_PWRITE),
        .bch_loop_apb_PWDATA (bch_loop_apb_PWDATA), .bch_loop_apb_PSTRB (bch_loop_apb_PSTRB),
        .bch_loop_apb_PPROT  (bch_loop_apb_PPROT),  .bch_loop_apb_PRDATA(bch_loop_apb_PRDATA),
        .bch_loop_apb_PREADY (bch_loop_apb_PREADY), .bch_loop_apb_PSLVERR(bch_loop_apb_PSLVERR),

        .bch_regs_apb_PSEL   (bch_regs_apb_PSEL),   .bch_regs_apb_PADDR  (bch_regs_apb_PADDR),
        .bch_regs_apb_PENABLE(bch_regs_apb_PENABLE), .bch_regs_apb_PWRITE(bch_regs_apb_PWRITE),
        .bch_regs_apb_PWDATA (bch_regs_apb_PWDATA), .bch_regs_apb_PSTRB (bch_regs_apb_PSTRB),
        .bch_regs_apb_PPROT  (bch_regs_apb_PPROT),
        .bch_regs_apb_PRDATA (w_obs4_prdata),
        .bch_regs_apb_PREADY (w_obs4_pready),      .bch_regs_apb_PSLVERR(w_obs4_pslverr),

        .obs_apb_PSEL   (obs_apb_PSEL),   .obs_apb_PADDR  (obs_apb_PADDR),
        .obs_apb_PENABLE(obs_apb_PENABLE), .obs_apb_PWRITE(obs_apb_PWRITE),
        .obs_apb_PWDATA (obs_apb_PWDATA), .obs_apb_PSTRB (obs_apb_PSTRB),
        .obs_apb_PPROT  (obs_apb_PPROT),  .obs_apb_PRDATA(w_obs_prdata),
        .obs_apb_PREADY (w_obs_pready),   .obs_apb_PSLVERR(w_obs_pslverr),

        .unmapped_irq   (w_unmapped_irq),
        .unmapped_addr  (w_unmapped_addr),
        .unmapped_count (w_unmapped_count),
        .unmapped_clear (w_clear));

    // -------------------------------------------------------------------------
    // The loop's register block: APB window -> the shared apb4_to_peakrdl shim
    // -------------------------------------------------------------------------
    logic        w_cpuif_req, w_cpuif_req_is_wr, w_cpuif_stall_wr, w_cpuif_stall_rd;
    logic [11:0] w_cpuif_addr;
    logic [31:0] w_cpuif_wr_data, w_cpuif_wr_biten, w_cpuif_rd_data;
    logic        w_cpuif_rd_ack, w_cpuif_rd_err, w_cpuif_wr_ack, w_cpuif_wr_err;

    bch_loop_regs__in_t  hwif_in;
    bch_loop_regs__out_t hwif_out;

    apb4_to_peakrdl #(
        .ADDR_WIDTH(12), .DATA_WIDTH(32), .USE_2_PHASE_CDC(1'b1)
    ) u_apb2cpuif (
        .aclk(aclk), .aresetn(aresetn), .pclk(aclk), .presetn(aresetn),
        .s_apb_PSEL   (bch_loop_apb_PSEL),        .s_apb_PENABLE(bch_loop_apb_PENABLE),
        .s_apb_PREADY (bch_loop_apb_PREADY),      .s_apb_PADDR  (bch_loop_apb_PADDR[11:0]),
        .s_apb_PWRITE (bch_loop_apb_PWRITE),      .s_apb_PWDATA (bch_loop_apb_PWDATA),
        .s_apb_PSTRB  (bch_loop_apb_PSTRB),       .s_apb_PPROT  (bch_loop_apb_PPROT),
        .s_apb_PRDATA (bch_loop_apb_PRDATA),      .s_apb_PSLVERR(bch_loop_apb_PSLVERR),
        .cpuif_req(w_cpuif_req), .cpuif_req_is_wr(w_cpuif_req_is_wr), .cpuif_addr(w_cpuif_addr),
        .cpuif_wr_data(w_cpuif_wr_data), .cpuif_wr_biten(w_cpuif_wr_biten),
        .cpuif_req_stall_wr(w_cpuif_stall_wr), .cpuif_req_stall_rd(w_cpuif_stall_rd),
        .cpuif_rd_ack(w_cpuif_rd_ack), .cpuif_rd_err(w_cpuif_rd_err), .cpuif_rd_data(w_cpuif_rd_data),
        .cpuif_wr_ack(w_cpuif_wr_ack), .cpuif_wr_err(w_cpuif_wr_err));

    bch_loop_regs u_regs (
        .clk(aclk), .rst(!aresetn),
        .s_cpuif_req(w_cpuif_req), .s_cpuif_req_is_wr(w_cpuif_req_is_wr),
        .s_cpuif_addr(w_cpuif_addr[BCH_LOOP_REGS_MIN_ADDR_WIDTH-1:0]),
        .s_cpuif_wr_data(w_cpuif_wr_data), .s_cpuif_wr_biten(w_cpuif_wr_biten),
        .s_cpuif_req_stall_wr(w_cpuif_stall_wr), .s_cpuif_req_stall_rd(w_cpuif_stall_rd),
        .s_cpuif_rd_ack(w_cpuif_rd_ack), .s_cpuif_rd_err(w_cpuif_rd_err), .s_cpuif_rd_data(w_cpuif_rd_data),
        .s_cpuif_wr_ack(w_cpuif_wr_ack), .s_cpuif_wr_err(w_cpuif_wr_err),
        .hwif_in(hwif_in), .hwif_out(hwif_out));

    // -------------------------------------------------------------------------
    // Control decode
    // -------------------------------------------------------------------------
    logic dp_rstn;

    logic r_start_d, r_clear_d, r_soft_reset_d;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_start_d      <= 1'b0;
            r_clear_d      <= 1'b0;
            r_soft_reset_d <= 1'b0;
        end else begin
            r_start_d      <= hwif_out.GO.start.value;
            r_clear_d      <= hwif_out.CTRL.clear.value;
            r_soft_reset_d <= hwif_out.CTRL.soft_reset.value;
        end
    )

    assign w_clear      = hwif_out.CTRL.clear.value      && !r_clear_d;
    assign w_soft_reset = hwif_out.CTRL.soft_reset.value && !r_soft_reset_d;
    assign w_bypass     = hwif_out.CTRL.bypass.value;
    assign w_blocks     = hwif_out.GEN_BLOCKS.blocks.value;

    logic w_axi4_overflow, w_start_req;
    assign w_axi4_overflow = (IFACE != "AXIS")
                          && (32'(w_blocks) > 32'(CFG_AXI4_MAX_BLOCKS));

    assign w_start_req  = hwif_out.GO.start.value && !r_start_d;
    assign w_start      = w_start_req && !w_axi4_overflow;

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
        .cfg_tdest(1'b0), .cfg_last_bytes(8'(CFG_K_TAIL / 8)),
        .cfg_busy(gen_busy), .cfg_done(gen_done),
        .o_expected_crc(gen_crc), .o_expected_crc_valid(gen_crc_valid),
        .o_beat_count(gen_beats_ch), .o_beat_count_total(gen_beats_total),
        .m_axis_tvalid(gen_tvalid), .m_axis_tready(gen_tready),
        .m_axis_tdata(gen_tdata), .m_axis_tstrb(gen_tstrb), .m_axis_tlast(gen_tlast),
        .m_axis_tid(), .m_axis_tdest(), .m_axis_tuser());
    /* verilator lint_on PINCONNECTEMPTY */

    // =========================================================================
    // Encoder -> packer -> injector -> decoder
    // =========================================================================
    // bch_encoder_axis4 emits a partial data beat mid-block and starts parity on
    // a fresh beat; bch_decoder_core expects partial keep only on a block's LAST
    // beat.  The bch_beat_packer repacks the encoder output into ceil(n/B) beats
    // so the injector and decoder see the same packed codeword the AXI4 flavour
    // uses internally.
    // =========================================================================
    logic          enc_in_valid, enc_in_ready, enc_out_valid, enc_out_ready, enc_out_last, enc_frame_err;
    logic          cw_out_valid, cw_out_ready;
    logic          cw_in_valid,  cw_in_ready;
    logic          cw_out_window, cw_in_window;
    logic [DW-1:0] enc_out_data;
    logic [S-1:0]  enc_out_keep;
    logic [DW-1:0] enc_out_bitkeep;

    always_comb begin
        for (int i = 0; i < S; i++)
            enc_out_bitkeep[i*8 +: 8] = {8{enc_out_keep[i]}};
    end

    assign enc_in_valid = gen_tvalid && !w_bypass;

    if ((IFACE != "AXIS") && (IFACE != "AXI4"))
        $fatal(1, "bch_loop_harness: IFACE=%s is not a datapath; expected \"AXIS\" or \"AXI4\".", IFACE);

    localparam int ND = 1;

    logic          pkt_valid, pkt_ready, pkt_last;
    logic [DW-1:0] pkt_data;
    logic [DW-1:0] pkt_keep;      // per-bit, packed
    logic [S-1:0]  pkt_strb;

    logic          inj_out_valid, inj_out_ready, inj_out_last;
    logic [DW-1:0] inj_out_data;
    logic [DW-1:0] inj_out_keep;  // per-bit, packed
    logic [S-1:0]  inj_out_strb;
    logic [31:0]   inj_bits, inj_blocks, inj_over_t;
    logic [7:0]    inj_last;

    logic            dec_in_ready [2], dec_in_valid [2];
    logic            dec_out_valid [2], dec_out_ready [2], dec_out_last [2];
    logic [DW-1:0]   dec_out_data [2];
    logic [S-1:0]    dec_out_keep [2];
    logic            dec_ok [2], dec_unc [2], dec_frame [2];
    logic [SC_W-1:0] dec_corr [2];

    logic        w_pipe_busy, w_pipe_done, w_pipe_resp_err;
    logic        w_enc_active, w_dec_active;
    logic [31:0] w_pipe_ok, w_pipe_corr, w_pipe_unc, w_pipe_frame, w_pipe_sym;
    logic [4:0]  w_pipe_stage;

    if (IFACE == "AXIS") begin : g_axis_path

    // convert packed per-bit keep to byte strobe for the byte-aligned decoder
    always_comb begin
        for (int i = 0; i < S; i++) begin
            pkt_strb[i]      = &pkt_keep[i*8 +: 8];
            inj_out_strb[i]  = &inj_out_keep[i*8 +: 8];
        end
    end

    /* verilator lint_off PINCONNECTEMPTY */
    bch_encoder_axis4 #(
        .FIELD_DIM(M), .PRIM_POLY(CFG_PRIM_POLY), .T_BITS(T), .N_BITS(N),
        .FIRST_ROOT(CFG_FIRST_ROOT), .BITS_PER_BEAT(DW),
        .AXIS_ID_WIDTH(0), .AXIS_DEST_WIDTH(0), .AXIS_USER_WIDTH(0)
    ) u_enc (
        .aclk(aclk), .aresetn(dp_rstn),
        .s_axis_tdata(gen_tdata), .s_axis_tstrb(gen_tstrb), .s_axis_tlast(gen_tlast),
        .s_axis_tid('0), .s_axis_tdest('0), .s_axis_tuser('0),
        .s_axis_tvalid(enc_in_valid), .s_axis_tready(enc_in_ready),
        .m_axis_tdata(enc_out_data), .m_axis_tstrb(enc_out_keep),
        .m_axis_tlast(enc_out_last), .m_axis_tid(), .m_axis_tdest(), .m_axis_tuser(),
        .m_axis_tvalid(enc_out_valid), .m_axis_tready(enc_out_ready),
        .frame_err(enc_frame_err));

    bch_beat_packer #(
        .BITS_PER_BEAT(DW), .DATA_WIDTH(DW)
    ) u_packer (
        .aclk(aclk), .aresetn(dp_rstn),
        .in_valid(enc_out_valid), .in_ready(enc_out_ready),
        .in_data(enc_out_data), .in_keep(enc_out_bitkeep), .in_last(enc_out_last),
        .out_valid(pkt_valid), .out_ready(pkt_ready),
        .out_data(pkt_data), .out_keep(pkt_keep), .out_last(pkt_last));

    error_injector #(
        .SYMBOL_WIDTH(1), .SYMBOLS_PER_BEAT(DW), .N_SYMBOLS(N), .T_SYMBOLS(T),
        .DATA_WIDTH(DW)
    ) u_inj (
        .aclk(aclk), .aresetn(dp_rstn),
        .in_valid(pkt_valid), .in_ready(pkt_ready), .in_data(pkt_data),
        .in_keep(pkt_keep), .in_last(pkt_last),
        .out_valid(inj_out_valid), .out_ready(inj_out_ready), .out_data(inj_out_data),
        .out_keep(inj_out_keep), .out_last(inj_out_last),
        .out_erasure(),
        .cfg_mode(hwif_out.INJ_CFG.mode.value), .cfg_count(hwif_out.INJ_CFG.errors.value),
        .cfg_rate(hwif_out.INJ_CFG.rate.value), .cfg_seed(hwif_out.INJ_SEED.value.value),
        .cfg_seed_load(w_start && hwif_out.CTRL.inj_seed_on_start.value), .cfg_clear(w_clear),
        .cfg_mark_erasure(1'b0),
        .cfg_cnt_min(hwif_out.INJ_CNT.cnt_min.value),  .cfg_cnt_max(hwif_out.INJ_CNT.cnt_max.value),
        .cfg_len_min(hwif_out.INJ_LEN.len_min.value),  .cfg_len_max(hwif_out.INJ_LEN.len_max.value),
        .o_inj_symbols(inj_bits), .o_inj_blocks(inj_blocks), .o_inj_over_t(inj_over_t),
        .o_last_block_errors(inj_last));

    assign inj_out_ready = dec_in_ready[0];
    assign dec_in_valid[0] = inj_out_valid;

    assign cw_out_valid  = enc_out_valid;
    assign cw_out_ready  = enc_out_ready;
    assign cw_in_valid   = dec_in_valid[0];
    assign cw_in_ready   = dec_in_ready[0];
    assign w_enc_active  = 1'b1;
    assign w_dec_active  = 1'b1;

    assign w_obs4_prdata  = 32'h0;
    assign w_obs4_pready  = 1'b1;
    assign w_obs4_pslverr = 1'b0;

    bch_decoder_axis4 #(
        .FIELD_DIM(M), .PRIM_POLY(CFG_PRIM_POLY), .T_BITS(T), .N_BITS(N),
        .FIRST_ROOT(CFG_FIRST_ROOT), .BITS_PER_BEAT(DW),
        .AXIS_ID_WIDTH(0), .AXIS_DEST_WIDTH(0), .AXIS_USER_WIDTH(0)
    ) u_dec (
        .aclk(aclk), .aresetn(dp_rstn),
        .s_axis_tdata(inj_out_data), .s_axis_tstrb(inj_out_strb),
        .s_axis_tlast(inj_out_last),
        .s_axis_tid('0), .s_axis_tdest('0), .s_axis_tuser('0),
        .s_axis_tvalid(dec_in_valid[0]), .s_axis_tready(dec_in_ready[0]),
        .m_axis_tdata(dec_out_data[0]), .m_axis_tstrb(dec_out_keep[0]),
        .m_axis_tlast(dec_out_last[0]),
        .m_axis_tid(), .m_axis_tdest(), .m_axis_tuser(),
        .m_axis_tvalid(dec_out_valid[0]), .m_axis_tready(dec_out_ready[0]),
        .out_status_ok(dec_ok[0]), .out_status_corrected(dec_corr[0]),
        .out_status_uncorrectable(dec_unc[0]), .out_status_frame_err(dec_frame[0]));
    /* verilator lint_on PINCONNECTEMPTY */

    assign w_pipe_busy     = 1'b0;
    assign w_pipe_done     = 1'b0;
    assign w_pipe_resp_err = 1'b0;
    assign w_pipe_ok       = '0;
    assign w_pipe_corr     = '0;
    assign w_pipe_unc      = '0;
    assign w_pipe_frame    = '0;
    assign w_pipe_sym      = '0;
    assign w_pipe_stage    = '0;

    // tie off the unbuilt second decoder slot
    assign dec_in_ready[1]  = 1'b1;
    assign dec_in_valid[1]  = 1'b0;
    assign dec_out_valid[1] = 1'b0;
    assign dec_out_data[1]  = '0;
    assign dec_out_keep[1]  = '0;
    assign dec_out_last[1]  = 1'b0;
    assign dec_ok[1]        = 1'b0;
    assign dec_corr[1]      = '0;
    assign dec_unc[1]       = 1'b0;
    assign dec_frame[1]     = 1'b0;

    end else begin : g_axi4_path

    bch_axi4_pipeline #(
        .FIELD_DIM(M), .PRIM_POLY(CFG_PRIM_POLY), .T_BITS(T), .N_BITS(N),
        .FIRST_ROOT(CFG_FIRST_ROOT), .DATA_WIDTH(DW), .ADDR_WIDTH(32),
        .ID_WIDTH(4), .MEM_DEPTH(CFG_AXI4_MEM_DEPTH),
        .MAX_OUTSTANDING(4)
    ) u_pipe (
        .aclk(aclk), .aresetn(dp_rstn),
        .start(w_start), .cfg_blocks(16'(w_blocks)),
        .cfg_burst_len(CFG_AXI4_BURST_LEN),
        .busy(w_pipe_busy), .done(w_pipe_done),
        .in_valid(enc_in_valid), .in_ready(enc_in_ready),
        .in_data(gen_tdata), .in_last(gen_tlast),
        .obs_cw_out_valid(cw_out_valid), .obs_cw_out_ready(cw_out_ready),
        .obs_cw_in_valid(cw_in_valid),   .obs_cw_in_ready(cw_in_ready),
        .obs_enc_active(w_enc_active),   .obs_dec_active(w_dec_active),
        .obs_meter_clear(w_clear),
        .obs_apb_psel(bch_regs_apb_PSEL),       .obs_apb_penable(bch_regs_apb_PENABLE),
        .obs_apb_pready(w_obs4_pready),        .obs_apb_paddr(bch_regs_apb_PADDR[11:0]),
        .obs_apb_pwrite(bch_regs_apb_PWRITE),   .obs_apb_pwdata(bch_regs_apb_PWDATA),
        .obs_apb_pstrb(bch_regs_apb_PSTRB),     .obs_apb_prdata(w_obs4_prdata),
        .obs_apb_pslverr(w_obs4_pslverr),
        .out_valid(dec_out_valid[0]), .out_ready(dec_out_ready[0]),
        .out_data(dec_out_data[0]), .out_keep(dec_out_keep[0]),
        .out_last(dec_out_last[0]),
        .inj_mode(hwif_out.INJ_CFG.mode.value),
        .inj_count(hwif_out.INJ_CFG.errors.value),
        .inj_rate(hwif_out.INJ_CFG.rate.value),
        .inj_seed(hwif_out.INJ_SEED.value.value),
        .inj_seed_load(w_start && hwif_out.CTRL.inj_seed_on_start.value),
        .inj_clear(w_clear),
        .inj_cnt_min(hwif_out.INJ_CNT.cnt_min.value),  .inj_cnt_max(hwif_out.INJ_CNT.cnt_max.value),
        .inj_len_min(hwif_out.INJ_LEN.len_min.value),  .inj_len_max(hwif_out.INJ_LEN.len_max.value),
        .resp_err(w_pipe_resp_err), .enc_frame_err(enc_frame_err),
        .blk_ok(w_pipe_ok), .blk_corr(w_pipe_corr), .blk_unc(w_pipe_unc),
        .blk_frame(w_pipe_frame), .sym_corr(w_pipe_sym),
        .inj_bits(inj_bits), .inj_blocks(inj_blocks),
        .inj_over_t(inj_over_t), .inj_last(inj_last),
        .stage_done(w_pipe_stage));

    assign enc_out_valid = 1'b0;
    assign enc_out_ready = 1'b1;
    assign enc_out_data  = '0;
    assign enc_out_keep  = '0;
    assign enc_out_last  = 1'b0;
    assign inj_out_valid = 1'b0;
    assign inj_out_ready = 1'b1;
    assign inj_out_data  = '0;
    assign inj_out_keep  = '0;
    assign inj_out_last  = 1'b0;
    assign dec_in_ready[0]  = 1'b1;
    assign dec_in_ready[1]  = 1'b1;
    assign dec_in_valid[0]  = 1'b0;
    assign dec_in_valid[1]  = 1'b0;
    assign dec_ok[0]        = 1'b0;
    assign dec_corr[0]      = '0;
    assign dec_unc[0]       = 1'b0;
    assign dec_frame[0]     = 1'b0;
    assign dec_out_valid[1] = 1'b0;
    assign dec_out_data[1]  = '0;
    assign dec_out_keep[1]  = '0;
    assign dec_out_last[1]  = 1'b0;
    assign dec_ok[1]        = 1'b0;
    assign dec_corr[1]      = '0;
    assign dec_unc[1]       = 1'b0;
    assign dec_frame[1]     = 1'b0;

    end

    // =========================================================================
    // Checkers: one decoder; in bypass both watch the generator directly
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

    logic [15:0] w_thr_lfsr;
    /* verilator lint_off PINCONNECTEMPTY */
    shifter_lfsr #(.WIDTH(16), .TAP_INDEX_WIDTH(12), .TAP_COUNT(4)) u_thr (
        .clk(aclk), .rst_n(dp_rstn), .enable(1'b1), .seed_load(w_start),
        .seed_data(16'hB5A3), .taps({12'd16, 12'd15, 12'd13, 12'd4}), .lfsr_out(w_thr_lfsr), .lfsr_done());
    /* verilator lint_on PINCONNECTEMPTY */
    assign chk_ready_en[0] = !hwif_out.CTRL.throttle_a.value || w_thr_lfsr[0];
    assign chk_ready_en[1] = !hwif_out.CTRL.throttle_b.value || w_thr_lfsr[7];

    // unbuilt checker B: ready reads 1 so gen_tready in bypass is checker A's
    // alone, and its outputs read 0 so the B-side CSRs stay at zero
    assign chk_tvalid[1]      = 1'b0;
    assign chk_tdata[1]       = '0;
    assign chk_tstrb[1]       = '0;
    assign chk_tlast[1]       = 1'b0;
    assign chk_tready[1]      = 1'b1;
    assign chk_crc[1]         = '0;
    assign chk_crc_valid[1]   = '0;
    assign chk_data_err[1]    = 1'b0;
    assign chk_pkts[1]        = '0;
    assign chk_beats_ch[1]    = '0;
    assign chk_beats_total[1] = '0;

    always_comb begin
        if (w_bypass) begin
            chk_tvalid[0] = gen_tvalid;
            chk_tdata[0]  = gen_tdata;
            chk_tstrb[0]  = gen_tstrb;
            chk_tlast[0]  = gen_tlast;
        end else begin
            chk_tvalid[0] = dec_out_valid[0];
            chk_tdata[0]  = dec_out_data[0];
            chk_tstrb[0]  = dec_out_keep[0];
            chk_tlast[0]  = dec_out_last[0];
        end
        dec_out_ready[0] = !w_bypass && chk_tready[0];
        gen_tready = w_bypass ? chk_tready[0] : enc_in_ready;
    end

    for (genvar d = 0; d < ND; d++) begin : g_chk
        axis4_slave_pattern_check #(
            .NUM_CHANNELS(1), .AXIS_DATA_WIDTH(DW), .BYTE_CRC(1'b1),
            .AXIS_ID_WIDTH(1), .AXIS_DEST_WIDTH(1), .AXIS_USER_WIDTH(1)
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
    logic [31:0] r_blk_ok [2], r_blk_corr [2], r_blk_unc [2], r_blk_frame [2], r_bit_corr [2];

    for (genvar d = 0; d < 2; d++) begin : g_tally
        logic w_fire, w_last;
        assign w_fire = dec_out_valid[d] && dec_out_ready[d];
        assign w_last = w_fire && dec_out_last[d];
        `ALWAYS_FF_RST(aclk, dp_rstn,
            if (`RST_ASSERTED(dp_rstn)) begin
                r_blk_ok[d] <= '0; r_blk_corr[d] <= '0; r_blk_unc[d] <= '0;
                r_blk_frame[d] <= '0; r_bit_corr[d] <= '0;
            end else if (w_clear) begin
                r_blk_ok[d] <= '0; r_blk_corr[d] <= '0; r_blk_unc[d] <= '0;
                r_blk_frame[d] <= '0; r_bit_corr[d] <= '0;
            end else if (w_last) begin
                if (dec_frame[d])                 r_blk_frame[d] <= r_blk_frame[d] + 32'd1;
                else if (dec_unc[d])              r_blk_unc[d]   <= r_blk_unc[d] + 32'd1;
                else if (dec_ok[d])               r_blk_ok[d]    <= r_blk_ok[d] + 32'd1;
                else begin
                    r_blk_corr[d] <= r_blk_corr[d] + 32'd1;
                    r_bit_corr[d] <= r_bit_corr[d] + 32'(dec_corr[d]);
                end
            end
        )
    end

    // =========================================================================
    // Run timer and done flags
    // =========================================================================
    logic        r_busy, r_gen_done;
    logic [31:0] r_cycles;
    logic        w_chk_a_done, w_all_done;

    assign w_chk_a_done = (chk_pkts[0] == 32'(w_blocks));
    assign w_all_done   = r_gen_done && w_chk_a_done;

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
    assign o_chk_b_ok = 1'b0;   // checker B is not built
    assign o_cmp_err  = 1'b0;   // no comparator in this build

    // =========================================================================
    // Bandwidth meters on the codec's two ends
    // =========================================================================
    assign cw_out_window = r_busy && w_enc_active;
    assign cw_in_window  = r_busy && w_dec_active;

    logic [31:0] w_obs_prod [4], w_obs_bp [4], w_obs_starv [4], w_obs_idle [4];

    /* verilator lint_off PINCONNECTEMPTY */
    axi_bus_meter #(.NUM_CHANNELS(1)) u_obs_in (
        .aclk(aclk), .aresetn(dp_rstn),
        .i_clear(w_clear), .i_freeze(!r_busy),
        .i_valid(enc_in_valid), .i_ready(enc_in_ready),
        .i_channel_id('0), .i_channel_valid(1'b0),
        .o_agg_productive(w_obs_prod[0]), .o_agg_backpressure(w_obs_bp[0]),
        .o_agg_starvation(w_obs_starv[0]), .o_agg_idle(w_obs_idle[0]),
        .o_ch_productive(), .o_ch_backpressure(), .o_ch_starvation(),
        .o_ch_idle(), .o_ch_overflow());

    axi_bus_meter #(.NUM_CHANNELS(1)) u_obs_out (
        .aclk(aclk), .aresetn(dp_rstn),
        .i_clear(w_clear), .i_freeze(!r_busy),
        .i_valid(dec_out_valid[0]), .i_ready(dec_out_ready[0]),
        .i_channel_id('0), .i_channel_valid(1'b0),
        .o_agg_productive(w_obs_prod[1]), .o_agg_backpressure(w_obs_bp[1]),
        .o_agg_starvation(w_obs_starv[1]), .o_agg_idle(w_obs_idle[1]),
        .o_ch_productive(), .o_ch_backpressure(), .o_ch_starvation(),
        .o_ch_idle(), .o_ch_overflow());

    axi_bus_meter #(.NUM_CHANNELS(1)) u_obs_cw_out (
        .aclk(aclk), .aresetn(dp_rstn),
        .i_clear(w_clear), .i_freeze(!cw_out_window),
        .i_valid(cw_out_valid), .i_ready(cw_out_ready),
        .i_channel_id('0), .i_channel_valid(1'b0),
        .o_agg_productive(w_obs_prod[2]), .o_agg_backpressure(w_obs_bp[2]),
        .o_agg_starvation(w_obs_starv[2]), .o_agg_idle(w_obs_idle[2]),
        .o_ch_productive(), .o_ch_backpressure(), .o_ch_starvation(),
        .o_ch_idle(), .o_ch_overflow());

    axi_bus_meter #(.NUM_CHANNELS(1)) u_obs_cw_in (
        .aclk(aclk), .aresetn(dp_rstn),
        .i_clear(w_clear), .i_freeze(!cw_in_window),
        .i_valid(cw_in_valid), .i_ready(cw_in_ready),
        .i_channel_id('0), .i_channel_valid(1'b0),
        .o_agg_productive(w_obs_prod[3]), .o_agg_backpressure(w_obs_bp[3]),
        .o_agg_starvation(w_obs_starv[3]), .o_agg_idle(w_obs_idle[3]),
        .o_ch_productive(), .o_ch_backpressure(), .o_ch_starvation(),
        .o_ch_idle(), .o_ch_overflow());
    /* verilator lint_on PINCONNECTEMPTY */

    // =========================================================================
    // Interface observer on the four AXIS seams
    // =========================================================================
    localparam int OBS_PORTS = 4;

    logic [OBS_PORTS-1:0][DW-1:0] w_obs_tdata;
    logic [OBS_PORTS-1:0][DW/8-1:0] w_obs_tstrb;
    logic [OBS_PORTS-1:0]         w_obs_tlast, w_obs_tvalid, w_obs_tready;

    always_comb begin
        w_obs_tdata  = '0;  w_obs_tstrb = '0;
        w_obs_tlast  = '0;  w_obs_tvalid = '0;  w_obs_tready = '0;

        w_obs_tdata[0]  = gen_tdata;      w_obs_tstrb[0]  = {(DW/8){1'b1}};
        w_obs_tlast[0]  = gen_tlast;
        w_obs_tvalid[0] = enc_in_valid;   w_obs_tready[0] = enc_in_ready;

        w_obs_tdata[1]  = enc_out_data;   w_obs_tstrb[1]  = enc_out_keep;
        w_obs_tlast[1]  = enc_out_last;
        w_obs_tvalid[1] = enc_out_valid;  w_obs_tready[1] = enc_out_ready;

        // tap 2 "cw_in": the coded stream into the decoder (injector output)
        w_obs_tdata[2]  = inj_out_data;   w_obs_tstrb[2]  = inj_out_strb;
        w_obs_tlast[2]  = inj_out_last;
        w_obs_tvalid[2] = dec_in_valid[0]; w_obs_tready[2] = dec_in_ready[0];

        // tap 3 "msg_out": the decoder's corrected data output
        w_obs_tdata[3]  = dec_out_data[0]; w_obs_tstrb[3]  = dec_out_keep[0];
        w_obs_tlast[3]  = dec_out_last[0];
        w_obs_tvalid[3] = dec_out_valid[0]; w_obs_tready[3] = dec_out_ready[0];
    end

    /* verilator lint_off PINCONNECTEMPTY */
    axis4_intf_observer #(
        .NUM_PORTS        (OBS_PORTS),
        .DATA_WIDTH       (DW),
        .AXIS_ID_WIDTH    (1),
        .AXIS_DEST_WIDTH  (1),
        .AXIS_USER_WIDTH  (1),
        .APB_ADDR_WIDTH   (12),
        .ENABLE_BUS_METER (1'b1),
        .ENABLE_MON_TAPS  (1'b0)
    ) u_obs (
        .aclk(aclk), .aresetn(dp_rstn),
        .s_apb_psel   (obs_apb_PSEL),
        .s_apb_penable(obs_apb_PENABLE),
        .s_apb_pready (w_obs_pready),
        .s_apb_paddr  (obs_apb_PADDR[11:0]),
        .s_apb_pwrite (obs_apb_PWRITE),
        .s_apb_pwdata (obs_apb_PWDATA),
        .s_apb_pstrb  (obs_apb_PSTRB),
        .s_apb_prdata (w_obs_prdata),
        .s_apb_pslverr(w_obs_pslverr),
        .obs_axis_tdata (w_obs_tdata),
        .obs_axis_tstrb (w_obs_tstrb),
        .obs_axis_tlast (w_obs_tlast),
        .obs_axis_tid   ('0),
        .obs_axis_tdest ('0),
        .obs_axis_tuser ('0),
        .obs_axis_tvalid(w_obs_tvalid),
        .obs_axis_tready(w_obs_tready),
        .i_meter_clear ({OBS_PORTS{w_clear}}),
        .i_meter_freeze({OBS_PORTS{~r_busy}}),
        .cam_clear(1'b0),
        .s_axil_arvalid(1'b0), .s_axil_araddr('0), .s_axil_arprot('0),
        .s_axil_rready(1'b0),
        .s_axil_arready(), .s_axil_rvalid(), .s_axil_rdata(), .s_axil_rresp(),
        .m_axi_awready(1'b0), .m_axi_wready(1'b0),
        .m_axi_bid('0), .m_axi_bresp('0), .m_axi_buser('0), .m_axi_bvalid(1'b0),
        .m_axi_awid(), .m_axi_awaddr(), .m_axi_awlen(), .m_axi_awsize(),
        .m_axi_awburst(), .m_axi_awlock(), .m_axi_awcache(), .m_axi_awprot(),
        .m_axi_awqos(), .m_axi_awregion(), .m_axi_awuser(), .m_axi_awvalid(),
        .m_axi_wdata(), .m_axi_wstrb(), .m_axi_wlast(), .m_axi_wuser(),
        .m_axi_wvalid(), .m_axi_bready(),
        .m_axil_awready(1'b0), .m_axil_wready(1'b0),
        .m_axil_bvalid(1'b0), .m_axil_bresp('0),
        .m_axil_awvalid(), .m_axil_awaddr(), .m_axil_awprot(),
        .m_axil_wvalid(), .m_axil_wdata(), .m_axil_wstrb(), .m_axil_bready(),
        .irq_out());
    /* verilator lint_on PINCONNECTEMPTY */

    // =========================================================================
    // Status back to the CSRs
    // =========================================================================
    always_comb begin
        hwif_in = '{default: '0};
        hwif_in.BUILD_ID.value.next      = CFG_BUILD_ID;
        hwif_in.STATUS.busy.next         = r_busy;
        hwif_in.STATUS.gen_done.next     = r_gen_done;
        hwif_in.STATUS.chk_a_done.next   = w_chk_a_done;
        hwif_in.STATUS.chk_b_done.next   = 1'b0;
        hwif_in.STATUS.data_err_a.next   = chk_data_err[0];
        hwif_in.STATUS.data_err_b.next   = chk_data_err[1];
        hwif_in.STATUS.crc_a_ok.next     = w_crc_a_ok;
        hwif_in.STATUS.crc_b_ok.next     = w_crc_b_ok;
        hwif_in.STATUS.axi4_resp_err.next  = w_pipe_resp_err;
        hwif_in.STATUS.axi4_overflow.next  = w_axi4_overflow;
        hwif_in.STATUS.axi4_stage.next     = w_pipe_stage;
        hwif_in.PROFILE.n.next           = 16'(N);
        hwif_in.PROFILE.t.next           = 8'(T);
        hwif_in.PROFILE.m.next           = 4'(M);
        hwif_in.PROFILE.spb.next         = 4'(DW / 8);   // bytes per beat, not bits
        hwif_in.TOPOLOGY.decoders.next   = 3'(ND);
        hwif_in.TOPOLOGY.kes_a.next      = 1'b0;        // RIBM = 0
        hwif_in.TOPOLOGY.iface.next      = (IFACE != "AXIS");
        hwif_in.CRC_EXPECTED.value.next  = gen_crc[0];
        hwif_in.CRC_A.value.next         = chk_crc[0][0];
        hwif_in.CRC_B.value.next         = chk_crc[1][0];
        hwif_in.PKTS_A.value.next        = chk_pkts[0];
        hwif_in.PKTS_B.value.next        = chk_pkts[1];
        hwif_in.CYCLES.value.next        = r_cycles;
        hwif_in.BLK_OK_A.value.next      = (IFACE == "AXIS") ? r_blk_ok[0] : w_pipe_ok;
        hwif_in.BLK_CORR_A.value.next    = (IFACE == "AXIS") ? r_blk_corr[0] : w_pipe_corr;
        hwif_in.BLK_UNC_A.value.next     = (IFACE == "AXIS") ? r_blk_unc[0] : w_pipe_unc;
        hwif_in.BLK_FRAME_A.value.next   = (IFACE == "AXIS") ? r_blk_frame[0] : w_pipe_frame;
        hwif_in.SYM_CORR_A.value.next    = (IFACE == "AXIS") ? r_bit_corr[0] : w_pipe_sym;
        hwif_in.BLK_OK_B.value.next      = r_blk_ok[1];
        hwif_in.BLK_CORR_B.value.next    = r_blk_corr[1];
        hwif_in.BLK_UNC_B.value.next     = r_blk_unc[1];
        hwif_in.BLK_FRAME_B.value.next   = r_blk_frame[1];
        hwif_in.SYM_CORR_B.value.next    = r_bit_corr[1];
        hwif_in.INJ_SYMBOLS.value.next   = inj_bits;
        hwif_in.INJ_BLOCKS.value.next    = inj_blocks;
        hwif_in.INJ_OVER_T.value.next    = inj_over_t;
        hwif_in.INJ_LAST.value.next      = inj_last;
        hwif_in.OBS_IN_PRODUCTIVE.value.next    = w_obs_prod[0];
        hwif_in.OBS_IN_BACKPRESSURE.value.next  = w_obs_bp[0];
        hwif_in.OBS_IN_STARVATION.value.next    = w_obs_starv[0];
        hwif_in.OBS_IN_IDLE.value.next          = w_obs_idle[0];
        hwif_in.OBS_OUT_PRODUCTIVE.value.next   = w_obs_prod[1];
        hwif_in.OBS_OUT_BACKPRESSURE.value.next = w_obs_bp[1];
        hwif_in.OBS_OUT_STARVATION.value.next   = w_obs_starv[1];
        hwif_in.OBS_OUT_IDLE.value.next         = w_obs_idle[1];
        hwif_in.OBS_CW_OUT_PRODUCTIVE.value.next   = w_obs_prod[2];
        hwif_in.OBS_CW_OUT_BACKPRESSURE.value.next = w_obs_bp[2];
        hwif_in.OBS_CW_OUT_STARVATION.value.next   = w_obs_starv[2];
        hwif_in.OBS_CW_OUT_IDLE.value.next         = w_obs_idle[2];
        hwif_in.OBS_CW_IN_PRODUCTIVE.value.next    = w_obs_prod[3];
        hwif_in.OBS_CW_IN_BACKPRESSURE.value.next  = w_obs_bp[3];
        hwif_in.OBS_CW_IN_STARVATION.value.next    = w_obs_starv[3];
        hwif_in.OBS_CW_IN_IDLE.value.next          = w_obs_idle[3];
    end

    logic unused_h;
    assign unused_h = gen_busy ^ enc_frame_err ^ w_pipe_busy ^ w_pipe_done ^ (^gen_beats_total) ^ (^gen_beats_ch[0])
                    ^ (^chk_beats_total[0]) ^ (^chk_beats_total[1]) ^ (^chk_beats_ch[0][0]) ^ (^chk_beats_ch[1][0])
                    ^ (^w_cpuif_addr[11:BCH_LOOP_REGS_MIN_ADDR_WIDTH])
                    ^ w_unmapped_irq ^ (^w_unmapped_addr) ^ (^w_unmapped_count)
                    ^ bch_regs_apb_PSEL ^ bch_regs_apb_PENABLE ^ bch_regs_apb_PWRITE
                    ^ (^bch_regs_apb_PADDR) ^ (^bch_regs_apb_PWDATA) ^ (^bch_regs_apb_PSTRB)
                    ^ (^bch_regs_apb_PPROT)
                    ^ (^obs_apb_PPROT);

endmodule : bch_loop_harness
