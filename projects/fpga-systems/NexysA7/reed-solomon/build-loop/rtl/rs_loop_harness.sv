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
//   reach both decoders, each decoder's output is compared beat by beat
//   against the generator's regenerated pattern (the checker's data_err -- so
//   a decoder that corrects is proven against a reference that never saw the
//   errors), and a comparator requires the two decoders to agree beat for beat
//   and verdict for verdict. With more than t errors per block neither decoder
//   can restore the data, so the checkers report mismatching beats there by
//   design; the verdict tallies and the comparator are the evidence in that
//   regime. The checker's CRC is computed over its REGENERATED words, so a CRC
//   match only shows the checker consumed as many words as the generator
//   produced; crc_a_ok / crc_b_ok are delivery checks, not data checks.
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
//   Bus structure, the common harness pattern: the host's UART -> AXI4-Lite
//   bridge drives a generated 1x3 fabric (bridge_rs_loop_axil), and every
//   register space in the design is a slave window on it. Today only the
//   loop's own block is populated, through the shared apb4_to_peakrdl shim;
//   the other two windows are the codec's rs_regs (PRD D9's standalone tops)
//   and an interface observer, tied off until they exist so a stray access
//   cannot hang the host bus. Adding a block is a bridge regeneration, not a
//   harness rewrite -- which is why the first cut of this file, with the UART
//   bridge wired straight into one flat register block, was wrong.
//
//==============================================================================

module rs_loop_harness
    import rs_loop_cfg_pkg::*;
    import rs_loop_regs_pkg::*;
#(
    // 32, not 12: the fabric decodes the window bits (rs_regs at 0x10000,
    // obs at 0x20000), so truncating the host address here makes those
    // windows unreachable -- every access folds back into the low window.
    // That is what the first cut of this rework did, and a board probe that
    // read 0x10000 and got the loop block's BUILD_ID is what found it.
    parameter int AXIL_ADDR_WIDTH = 32,

    // ONE SOLVER PER BITSTREAM (Sean, 2026-09-30). A board build carries
    // riBM OR Euclid, never both, and KES_ALGO_A says which. So the board
    // matrix is solver x datapath = four bitstreams, each with one encoder and
    // one decoder.
    //
    // ENABLE_COMPARE therefore defaults OFF. Turning it on builds a SECOND
    // decoder and the beat-for-beat comparator between the solvers, which
    // belongs in SIMULATION -- area is free there, riBM-against-Euclid
    // agreement is how solver equivalence gets checked, and it is what caught
    // two real harness bugs (dropped and duplicated beats under a skewed
    // drain). It is worth keeping; it is not worth a bitstream.
    //
    // Correctness on the board does not depend on it. The pattern checker
    // compares received words against the regenerated pattern, which is a
    // direct check against known-good data. Two solvers agreeing is the
    // weaker claim of the two, since both can agree on a wrong answer -- which
    // is exactly what a miscorrected block is.
    //
    // Which datapath is built. "AXIS" is the stream pipe the board was
    // validated on: generator, encoder, injector, decoder, checker, all
    // flowing. "AXI4" swaps the middle for rs_axi4_pipeline, where the codecs
    // are JOB engines over four memories and the stages run in sequence. The
    // generator and the checkers are the same blocks either way, so the CSRs,
    // the CRC comparison and the data_err evidence are unchanged.
    parameter string IFACE        = "AXIS",
    parameter string KES_ALGO_A   = CFG_KES_A,
    parameter string KES_ALGO_B   = CFG_KES_B,
    parameter bit    ENABLE_COMPARE = 1'b0
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

    // The fabric gives this block a 4 KB window; the regblock must fit inside
    // it, and the harness must carry every bit the regblock decodes.
    initial begin : csr_fit_check
        if (RS_LOOP_REGS_MIN_ADDR_WIDTH > 12)
            $error("rs_loop_harness: the register block needs %0d address bits, more than the 4 KB window",
                   RS_LOOP_REGS_MIN_ADDR_WIDTH);
    end

    localparam int M    = CFG_SYMBOL_WIDTH;
    localparam int T    = CFG_T_SYMBOLS;
    localparam int N    = CFG_N_SYMBOLS;
    localparam int S    = CFG_SPB;
    localparam int DW   = CFG_DATA_WIDTH;
    localparam int SC_W = $clog2(T + 1);

    // Control signals decoded from the CSRs further down. Declared here
    // because the fabric's unmapped-access clear is one of them, and a
    // forward reference in a port map becomes an implicit 1-bit net.
    logic        w_start, w_clear, w_soft_reset, w_bypass;
    logic [15:0] w_blocks;

    // =========================================================================
    // Bus fabric: host AXI4-Lite -> generated 1x3 bridge -> APB slave windows
    // =========================================================================
    logic        rs_loop_apb_PSEL, rs_loop_apb_PENABLE, rs_loop_apb_PWRITE;
    logic        rs_loop_apb_PREADY, rs_loop_apb_PSLVERR;
    logic [31:0] rs_loop_apb_PADDR, rs_loop_apb_PWDATA, rs_loop_apb_PRDATA;
    logic [3:0]  rs_loop_apb_PSTRB;
    logic [2:0]  rs_loop_apb_PPROT;

    // Expansion windows: rs_regs (PRD D9's codec register block) at 0x10000
    // and an interface observer at 0x20000. Tied off so a stray host access
    // completes instead of hanging the bus.
    logic        rs_regs_apb_PSEL, rs_regs_apb_PENABLE, rs_regs_apb_PWRITE;
    logic [31:0] rs_regs_apb_PADDR, rs_regs_apb_PWDATA;
    logic [3:0]  rs_regs_apb_PSTRB;
    logic [2:0]  rs_regs_apb_PPROT;
    logic        obs_apb_PSEL, obs_apb_PENABLE, obs_apb_PWRITE;
    logic [31:0] obs_apb_PADDR, obs_apb_PWDATA;
    logic [3:0]  obs_apb_PSTRB;
    logic [2:0]  obs_apb_PPROT;

    logic        w_unmapped_irq, w_unmapped_clear;
    logic [31:0] w_unmapped_addr;
    logic [31:0] w_unmapped_count;

    bridge_rs_loop_axil u_bridge (
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

        .rs_loop_apb_PSEL   (rs_loop_apb_PSEL),   .rs_loop_apb_PADDR  (rs_loop_apb_PADDR),
        .rs_loop_apb_PENABLE(rs_loop_apb_PENABLE), .rs_loop_apb_PWRITE(rs_loop_apb_PWRITE),
        .rs_loop_apb_PWDATA (rs_loop_apb_PWDATA), .rs_loop_apb_PSTRB (rs_loop_apb_PSTRB),
        .rs_loop_apb_PPROT  (rs_loop_apb_PPROT),  .rs_loop_apb_PRDATA(rs_loop_apb_PRDATA),
        .rs_loop_apb_PREADY (rs_loop_apb_PREADY), .rs_loop_apb_PSLVERR(rs_loop_apb_PSLVERR),

        .rs_regs_apb_PSEL   (rs_regs_apb_PSEL),   .rs_regs_apb_PADDR  (rs_regs_apb_PADDR),
        .rs_regs_apb_PENABLE(rs_regs_apb_PENABLE), .rs_regs_apb_PWRITE(rs_regs_apb_PWRITE),
        .rs_regs_apb_PWDATA (rs_regs_apb_PWDATA), .rs_regs_apb_PSTRB (rs_regs_apb_PSTRB),
        .rs_regs_apb_PPROT  (rs_regs_apb_PPROT),  .rs_regs_apb_PRDATA(32'h0),
        .rs_regs_apb_PREADY (1'b1),               .rs_regs_apb_PSLVERR(1'b0),

        .obs_apb_PSEL   (obs_apb_PSEL),   .obs_apb_PADDR  (obs_apb_PADDR),
        .obs_apb_PENABLE(obs_apb_PENABLE), .obs_apb_PWRITE(obs_apb_PWRITE),
        .obs_apb_PWDATA (obs_apb_PWDATA), .obs_apb_PSTRB (obs_apb_PSTRB),
        .obs_apb_PPROT  (obs_apb_PPROT),  .obs_apb_PRDATA(32'h0),
        .obs_apb_PREADY (1'b1),           .obs_apb_PSLVERR(1'b0),

        .unmapped_irq   (w_unmapped_irq),
        .unmapped_addr  (w_unmapped_addr),
        .unmapped_count (w_unmapped_count),
        .unmapped_clear (w_clear));

    // -------------------------------------------------------------------------
    // The loop's register block: APB window -> the shared apb4_to_peakrdl shim
    // -> the generated regblock. Same route char_engine_block uses for
    // chargen_regs; both clock inputs are aclk here (one clock in this design),
    // so the shim's CDC is degenerate and costs only handshake latency.
    // -------------------------------------------------------------------------
    logic        w_cpuif_req, w_cpuif_req_is_wr, w_cpuif_stall_wr, w_cpuif_stall_rd;
    logic [11:0] w_cpuif_addr;
    logic [31:0] w_cpuif_wr_data, w_cpuif_wr_biten, w_cpuif_rd_data;
    logic        w_cpuif_rd_ack, w_cpuif_rd_err, w_cpuif_wr_ack, w_cpuif_wr_err;

    rs_loop_regs__in_t  hwif_in;
    rs_loop_regs__out_t hwif_out;

    apb4_to_peakrdl #(
        .ADDR_WIDTH(12), .DATA_WIDTH(32), .USE_2_PHASE_CDC(1'b1)
    ) u_apb2cpuif (
        .aclk(aclk), .aresetn(aresetn), .pclk(aclk), .presetn(aresetn),
        .s_apb_PSEL   (rs_loop_apb_PSEL),        .s_apb_PENABLE(rs_loop_apb_PENABLE),
        .s_apb_PREADY (rs_loop_apb_PREADY),      .s_apb_PADDR  (rs_loop_apb_PADDR[11:0]),
        .s_apb_PWRITE (rs_loop_apb_PWRITE),      .s_apb_PWDATA (rs_loop_apb_PWDATA),
        .s_apb_PSTRB  (rs_loop_apb_PSTRB),       .s_apb_PPROT  (rs_loop_apb_PPROT),
        .s_apb_PRDATA (rs_loop_apb_PRDATA),      .s_apb_PSLVERR(rs_loop_apb_PSLVERR),
        .cpuif_req(w_cpuif_req), .cpuif_req_is_wr(w_cpuif_req_is_wr), .cpuif_addr(w_cpuif_addr),
        .cpuif_wr_data(w_cpuif_wr_data), .cpuif_wr_biten(w_cpuif_wr_biten),
        .cpuif_req_stall_wr(w_cpuif_stall_wr), .cpuif_req_stall_rd(w_cpuif_stall_rd),
        .cpuif_rd_ack(w_cpuif_rd_ack), .cpuif_rd_err(w_cpuif_rd_err), .cpuif_rd_data(w_cpuif_rd_data),
        .cpuif_wr_ack(w_cpuif_wr_ack), .cpuif_wr_err(w_cpuif_wr_err));

    rs_loop_regs u_regs (
        .clk(aclk), .rst(!aresetn),
        .s_cpuif_req(w_cpuif_req), .s_cpuif_req_is_wr(w_cpuif_req_is_wr),
        // Width from the GENERATED package, never a literal: the regblock says
        // how many address bits it needs, so adding a register can never
        // silently alias. A hardcoded [6:0] is what made GO at 0x080 fold onto
        // BUILD_ID the moment the map grew past 0x7F, and nothing ran.
        .s_cpuif_addr(w_cpuif_addr[RS_LOOP_REGS_MIN_ADDR_WIDTH-1:0]),
        .s_cpuif_wr_data(w_cpuif_wr_data), .s_cpuif_wr_biten(w_cpuif_wr_biten),
        .s_cpuif_req_stall_wr(w_cpuif_stall_wr), .s_cpuif_req_stall_rd(w_cpuif_stall_rd),
        .s_cpuif_rd_ack(w_cpuif_rd_ack), .s_cpuif_rd_err(w_cpuif_rd_err), .s_cpuif_rd_data(w_cpuif_rd_data),
        .s_cpuif_wr_ack(w_cpuif_wr_ack), .s_cpuif_wr_err(w_cpuif_wr_err),
        .hwif_in(hwif_in), .hwif_out(hwif_out));

    // -------------------------------------------------------------------------
    // Control decode (the signals are declared above the fabric)
    // -------------------------------------------------------------------------
    logic        dp_rstn;            // datapath reset: board reset or CTRL.soft_reset

    // The register write strobe reaching the regblock is HELD until the
    // regblock acks -- peakrdl_to_cmdrsp does that deliberately, and its
    // header records that reducing it to one cycle broke every read through
    // the bridge. So an RDL `singlepulse` field can be asserted for more than
    // one cycle, and every consumer here wants exactly one: the generator and
    // checker are armed by the same strobe, and a two-cycle arm reloads the
    // checker's LFSR seed a second time while the generator has already begun
    // advancing. In bypass, where the two are on the same cycle, that
    // desynchronised them and every beat mismatched. Take the rising edge.
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

    // A single AXI4 run cannot exceed what one memory holds: each region is
    // blocks * CFG_N_BEATS words and every memory is CFG_AXI4_MEM_DEPTH deep.
    // Past that a write engine wraps inside its memory and the decode reads
    // the wrong words -- a silently wrong answer, which is the one outcome
    // worth spending a register to prevent. The run is REFUSED, not clamped:
    // clamping would answer a question the host did not ask.
    logic w_axi4_overflow, w_start_req;
    assign w_axi4_overflow = (IFACE != "AXIS")
                          && (32'(w_blocks) > 32'(CFG_AXI4_MAX_BLOCKS));

    // The refusal gates the KICK, not just the pipeline. If the generator
    // started while the pipeline did not, it would stall on a seed engine
    // that never ran and the harness would sit busy until the host's own
    // timeout -- turning a clean refusal into a hang, and in the sim harness
    // burning the run's whole sim-time budget on a polling loop.
    assign w_start_req  = hwif_out.GO.start.value && !r_start_d;
    assign w_start      = w_start_req && !w_axi4_overflow;

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

    // The AXI4 path has one decoder. Building two would mean two more
    // memories and a second four-stage chain to compare beat for beat, and
    // the solver question it would answer is the one a million blocks on the
    // stream path already answered. This is a guard rather than a silent
    // override because a build asking for both has misunderstood which
    // question each flavour is for.
    if ((IFACE != "AXIS") && ENABLE_COMPARE)
        $fatal(1, "rs_loop_harness: IFACE=%s with ENABLE_COMPARE=1 is not built; the AXI4 datapath carries one decoder. Set ENABLE_COMPARE=0.", IFACE);
    if ((IFACE != "AXIS") && (IFACE != "AXI4"))
        $fatal(1, "rs_loop_harness: IFACE=%s is not a datapath; expected \"AXIS\" or \"AXI4\".", IFACE);

    localparam int ND = ENABLE_COMPARE ? 2 : 1;

    // The datapath nodes BOTH flavours expose. They live above the split
    // because the checkers, the tallies, the comparator and the CSRs below
    // read them, and only the middle that drives them differs.
    logic          inj_out_valid, inj_out_ready, inj_out_last;
    logic [DW-1:0] inj_out_data;
    logic [S-1:0]  inj_out_keep;
    logic [31:0]   inj_symbols, inj_blocks, inj_over_t;
    logic [7:0]    inj_last;

    logic            dec_in_ready [2], dec_in_valid [2];
    logic            dec_out_valid [2], dec_out_ready [2], dec_out_last [2];
    logic [DW-1:0]   dec_out_data [2];
    logic [S-1:0]    dec_out_keep [2];
    logic            dec_ok [2], dec_unc [2], dec_frame [2];
    logic [SC_W-1:0] dec_corr [2];

    // The AXI4 pipeline's own verdict totals. They cannot come through the
    // per-block tally below: the decoder reaches its verdict during the
    // DECODE stage while the beats the tally watches arrive later, during the
    // DRAIN, so the sideband would be stale by then. The CSR block selects
    // between these and the tally registers.
    logic        w_pipe_busy, w_pipe_done, w_pipe_resp_err;
    logic [31:0] w_pipe_ok, w_pipe_corr, w_pipe_unc, w_pipe_frame, w_pipe_sym;
    logic [4:0]  w_pipe_stage;

    // Where the two datapaths diverge. Everything above -- bridge, registers,
    // generator -- and everything below -- checkers, tallies, CRC, CSRs -- is
    // shared, so a run reports itself identically whichever middle is built.
    if (IFACE == "AXIS") begin : g_axis_path

    // The component's AXIS top, not the bare core: that is the deliverable a
    // consumer instantiates, so it is what the board should prove. At this
    // profile k fills its beats, so no beat packer is generated inside and the
    // datapath is the core plus two skid buffers. tid/tdest/tuser are unused
    // here, so their widths are 0 and the wrapper's 1-bit minimum applies.
    /* verilator lint_off PINCONNECTEMPTY */
    rs_encoder_axis4 #(
        .SYMBOL_WIDTH(M), .PRIM_POLY(CFG_PRIM_POLY), .T_SYMBOLS(T), .N_SYMBOLS(N),
        .FIRST_ROOT(CFG_FIRST_ROOT), .DATA_WIDTH(DW),
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
    /* verilator lint_on PINCONNECTEMPTY */

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

    // How many decoders exist. The arrays below stay 2 wide whatever ND is,
    // and the unbuilt half is tied off explicitly further down: sizing them
    // [ND] instead would make every `[1]` reference an out-of-range select at
    // elaboration, including the ones in dead ternary arms.

    assign inj_out_ready = dec_in_ready[0] && dec_in_ready[1];

    // With two decoders each one's valid is gated on the OTHER's ready, so a
    // beat lands on both in the same cycle. With one there is nobody to wait
    // for, and gating valid on its own ready would be a protocol violation.
    for (genvar d = 0; d < ND; d++) begin : g_dec_in
        if (ND == 2) assign dec_in_valid[d] = inj_out_valid && dec_in_ready[1-d];
        else         assign dec_in_valid[d] = inj_out_valid;
    end

    for (genvar d = 0; d < ND; d++) begin : g_dec
        // the component's AXIS top, as above
        /* verilator lint_off PINCONNECTEMPTY */
        rs_decoder_axis4 #(
            .SYMBOL_WIDTH(M), .PRIM_POLY(CFG_PRIM_POLY), .T_SYMBOLS(T), .N_SYMBOLS(N),
            .FIRST_ROOT(CFG_FIRST_ROOT), .DATA_WIDTH(DW),
            .KES_ALGO((d == 0) ? KES_ALGO_A : KES_ALGO_B),
            .AXIS_ID_WIDTH(0), .AXIS_DEST_WIDTH(0), .AXIS_USER_WIDTH(0)
        ) u_dec (
            .aclk(aclk), .aresetn(dp_rstn),
            .s_axis_tdata(inj_out_data), .s_axis_tstrb(inj_out_keep),
            .s_axis_tlast(inj_out_last),
            .s_axis_tid('0), .s_axis_tdest('0), .s_axis_tuser('0),
            .s_axis_tvalid(dec_in_valid[d]), .s_axis_tready(dec_in_ready[d]),
            .m_axis_tdata(dec_out_data[d]), .m_axis_tstrb(dec_out_keep[d]),
            .m_axis_tlast(dec_out_last[d]),
            .m_axis_tid(), .m_axis_tdest(), .m_axis_tuser(),
            .m_axis_tvalid(dec_out_valid[d]), .m_axis_tready(dec_out_ready[d]),
            .out_status_ok(dec_ok[d]), .out_status_corrected(dec_corr[d]),
            .out_status_uncorrectable(dec_unc[d]), .out_status_frame_err(dec_frame[d]));
        /* verilator lint_on PINCONNECTEMPTY */
    end

    // The unbuilt half. dec_in_ready[1] reads 1 so inj_out_ready above is
    // just decoder A's ready; everything else reads 0 so decoder B's tallies
    // and CSRs stay at zero and synthesis folds them away.
    // no AXI4 pipeline in this flavour
    assign w_pipe_busy     = 1'b0;
    assign w_pipe_done     = 1'b0;
    assign w_pipe_resp_err = 1'b0;
    assign w_pipe_ok       = '0;
    assign w_pipe_corr     = '0;
    assign w_pipe_unc      = '0;
    assign w_pipe_frame    = '0;
    assign w_pipe_sym      = '0;
    assign w_pipe_stage    = '0;

    if (ND < 2) begin : g_dec_b_tieoff
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
    end

    end else begin : g_axi4_path

    // =========================================================================
    // The AXI4 datapath: the same generator in, the same checker out, and a
    // memory-to-memory job chain in between.
    //
    // dec_out_*[0] is driven from the pipeline's DRAIN stage, so the checker,
    // the CRC comparison and the data_err evidence below are reached by the
    // same wires the stream path uses. What cannot come through g_tally is the
    // per-block verdict: the decoder reaches its verdict during the DECODE
    // stage, while these beats arrive later during the DRAIN, so the sideband
    // would be stale by the time the tally saw it. The pipeline accumulates
    // its own totals instead and the CSR block selects between the two
    // sources.
    // =========================================================================
    rs_axi4_pipeline #(
        .SYMBOL_WIDTH(M), .PRIM_POLY(CFG_PRIM_POLY), .T_SYMBOLS(T), .N_SYMBOLS(N),
        .FIRST_ROOT(CFG_FIRST_ROOT), .DATA_WIDTH(DW), .ADDR_WIDTH(32),
        .ID_WIDTH(4), .MEM_DEPTH(CFG_AXI4_MEM_DEPTH),
        .MAX_OUTSTANDING(4), .KES_ALGO(KES_ALGO_A)
    ) u_pipe (
        .aclk(aclk), .aresetn(dp_rstn),
        .start(w_start), .cfg_blocks(16'(w_blocks)),
        .cfg_burst_len(CFG_AXI4_BURST_LEN),
        .busy(w_pipe_busy), .done(w_pipe_done),
        .in_valid(enc_in_valid), .in_ready(enc_in_ready),
        .in_data(gen_tdata), .in_last(gen_tlast),
        .out_valid(dec_out_valid[0]), .out_ready(dec_out_ready[0]),
        .out_data(dec_out_data[0]), .out_keep(dec_out_keep[0]),
        .out_last(dec_out_last[0]),
        .inj_mode(hwif_out.INJ_CFG.mode.value),
        .inj_count(hwif_out.INJ_CFG.errors.value),
        .inj_rate(hwif_out.INJ_CFG.rate.value),
        .inj_seed(hwif_out.INJ_SEED.value.value),
        .inj_seed_load(w_start && hwif_out.CTRL.inj_seed_on_start.value),
        .inj_clear(w_clear),
        .resp_err(w_pipe_resp_err), .enc_frame_err(enc_frame_err),
        .blk_ok(w_pipe_ok), .blk_corr(w_pipe_corr), .blk_unc(w_pipe_unc),
        .blk_frame(w_pipe_frame), .sym_corr(w_pipe_sym),
        .inj_symbols(inj_symbols), .inj_blocks(inj_blocks),
        .inj_over_t(inj_over_t), .inj_last(inj_last),
        .stage_done(w_pipe_stage));

    // the stream path's internal nodes have no counterpart here
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
    // unbuilt checker B: ready reads 1 so gen_tready in bypass is checker A's
    // alone, and its outputs read 0 so the B-side CSRs stay at zero
    if (ND < 2) begin : g_chk_b_tieoff
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
    end

    // declared here because the drain logic below consumes cmp_wr_ready
    localparam int CMP_W = 1 + S + DW + 3 + SC_W;
    logic             cmp_wr_ready [2], cmp_rd_valid [2];
    logic [CMP_W-1:0] cmp_rd_data [2];
    logic             w_cmp_pop;
    logic [31:0]      r_cmp_data_mm, r_cmp_status_mm, r_cmp_beats;
    logic             r_cmp_err;


    always_comb begin
        for (int d = 0; d < ND; d++) begin
            if (w_bypass) begin
                // in bypass both checkers watch the generator, so with two
                // of them each waits on the other exactly as the decoders do
                chk_tvalid[d] = (ND == 2) ? (gen_tvalid && chk_tready[1-d]) : gen_tvalid;
                chk_tdata[d]  = gen_tdata;
                chk_tstrb[d]  = gen_tstrb;
                chk_tlast[d]  = gen_tlast;
            end else begin
                // cmp_wr_ready gates the VALID too, not just the decoder's
                // ready. The checker completes its own handshake on
                // chk_tvalid && chk_tready; if the comparator held the
                // decoder back while the checker was ready, the checker
                // consumed a beat the decoder never retired and then saw the
                // very same beat again. That duplicated beats on whichever
                // side the comparator stalled -- 6 packets counted for 4
                // blocks, with a data error and a bad CRC on a stream the
                // comparator simultaneously reported as beat-perfect.
                chk_tvalid[d] = dec_out_valid[d] && cmp_wr_ready[d];
                chk_tdata[d]  = dec_out_data[d];
                chk_tstrb[d]  = dec_out_keep[d];
                chk_tlast[d]  = dec_out_last[d];
            end
            // The comparator's ready is part of the drain condition. Without
            // it a full comparator FIFO silently DROPS a beat, after which the
            // comparator pairs beat N of one decoder with beat N+k of the
            // other and almost every beat "mismatches". That is what 30 of 64
            // random runs reported once the two checkers' throttles were drawn
            // independently -- with both throttled the same the FIFOs stayed
            // in lockstep and the bug was invisible. A slow checker on one
            // side now stalls both decoders, which is the right semantics for
            // a comparator: the two must stay in step.
            dec_out_ready[d] = !w_bypass && chk_tready[d] && cmp_wr_ready[d];
        end
        gen_tready = w_bypass ? (chk_tready[0] && chk_tready[ND-1]) : enc_in_ready;
    end

    for (genvar d = 0; d < ND; d++) begin : g_chk
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
    if (ENABLE_COMPARE) begin : g_compare
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

    end else begin : g_no_compare
        // One decoder: nothing to compare against. cmp_wr_ready reads 1 so it
        // drops out of the drain condition, and every count reads 0 so the
        // host sees an inactive comparator rather than a silent zero verdict.
        assign cmp_wr_ready[0] = 1'b1;
        assign cmp_wr_ready[1] = 1'b1;
        assign cmp_rd_valid[0] = 1'b0;
        assign cmp_rd_valid[1] = 1'b0;
        assign cmp_rd_data[0]  = '0;
        assign cmp_rd_data[1]  = '0;
        assign w_cmp_pop       = 1'b0;
        assign r_cmp_data_mm   = '0;
        assign r_cmp_status_mm = '0;
        assign r_cmp_beats     = '0;
        assign r_cmp_err       = 1'b0;
    end

    // =========================================================================
    // Run timer and done flags
    // =========================================================================
    logic        r_busy, r_gen_done;
    logic [31:0] r_cycles;
    logic        w_chk_a_done, w_chk_b_done, w_all_done;

    assign w_chk_a_done = (chk_pkts[0] == 32'(w_blocks));
    // With no decoder B there is nothing to wait for. Leaving this as the
    // packet compare would hold w_all_done low forever, because chk_pkts[1]
    // is tied to 0 and w_blocks is not -- the run would never finish.
    assign w_chk_b_done = (ND == 2) ? (chk_pkts[1] == 32'(w_blocks)) : 1'b1;
    // In the AXI4 flavour the generator finishes early -- it only feeds the
    // seed stage -- so the run is over when the CHECKER has every block,
    // which is after the drain. That is the same condition as the stream
    // flavour, so nothing special is needed here; w_pipe_busy is reported to
    // the host as stage visibility rather than used as the done term.
    assign w_all_done   = r_gen_done && w_chk_a_done && w_chk_b_done;

    // Misalignment guard. Both checkers done means every beat has been
    // delivered, and w_cmp_pop retires the two FIFOs in pairs, so a beat left
    // on exactly ONE side proves the decoders did not produce the same number
    // of beats -- or that one was dropped. Either way the mismatch counts
    // below describe two streams that are out of step, and the host must not
    // read them as a riBM-vs-Euclid disagreement. This is the check that was
    // missing when 30 of 64 random runs reported ~690 of 700 beats differing.
    logic r_cmp_misaligned;
    `ALWAYS_FF_RST(aclk, dp_rstn,
        if (`RST_ASSERTED(dp_rstn)) r_cmp_misaligned <= 1'b0;
        else if (w_clear)           r_cmp_misaligned <= 1'b0;
        else if (w_all_done && (cmp_rd_valid[0] ^ cmp_rd_valid[1])) r_cmp_misaligned <= 1'b1;
    )

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
    // Bandwidth meters on the codec's two ends
    //
    // The SAME two seams in both flavours -- the generator's handshake into the
    // codec, and the codec's handshake into the checker -- so the stream and
    // AXI4 builds produce directly comparable numbers. That is the point: the
    // question these answer is what each fabric boundary sustains end to end.
    //
    // i_freeze is !busy, so the window opens on the kick and closes the moment
    // the run finishes. Without it the host's own polling would be counted as
    // idle cycles and dilute every utilisation figure -- which is the trap the
    // block's own header warns about.
    //
    // On the stream path the two should differ by exactly n/k, since the
    // encoder emits a codeword for every k symbols it takes. So the pair is a
    // cheap self-check as well as a measurement.
    // =========================================================================
    logic [31:0] w_obs_prod [2], w_obs_bp [2], w_obs_starv [2], w_obs_idle [2];

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
        hwif_in.STATUS.chk_b_done.next   = w_chk_b_done;
        hwif_in.STATUS.data_err_a.next   = chk_data_err[0];
        hwif_in.STATUS.data_err_b.next   = chk_data_err[1];
        hwif_in.STATUS.cmp_err.next      = r_cmp_err;
        hwif_in.STATUS.crc_a_ok.next     = w_crc_a_ok;
        hwif_in.STATUS.crc_b_ok.next     = w_crc_b_ok;
        hwif_in.STATUS.cmp_misaligned.next = r_cmp_misaligned;
        hwif_in.STATUS.axi4_resp_err.next  = w_pipe_resp_err;
        hwif_in.STATUS.axi4_overflow.next  = w_axi4_overflow;
        hwif_in.STATUS.axi4_stage.next     = w_pipe_stage;
        hwif_in.PROFILE.n.next           = 16'(N);
        hwif_in.PROFILE.t.next           = 8'(T);
        hwif_in.PROFILE.m.next           = 4'(M);
        hwif_in.PROFILE.spb.next         = 4'(S);
        hwif_in.TOPOLOGY.decoders.next   = 3'(ND);
        hwif_in.TOPOLOGY.kes_a.next      = (KES_ALGO_A == "EUCLID");
        hwif_in.TOPOLOGY.kes_b.next      = (ND == 2) && (KES_ALGO_B == "EUCLID");
        hwif_in.TOPOLOGY.compare.next    = ENABLE_COMPARE;
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
        hwif_in.SYM_CORR_A.value.next    = (IFACE == "AXIS") ? r_sym_corr[0] : w_pipe_sym;
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
        hwif_in.OBS_IN_PRODUCTIVE.value.next    = w_obs_prod[0];
        hwif_in.OBS_IN_BACKPRESSURE.value.next  = w_obs_bp[0];
        hwif_in.OBS_IN_STARVATION.value.next    = w_obs_starv[0];
        hwif_in.OBS_IN_IDLE.value.next          = w_obs_idle[0];
        hwif_in.OBS_OUT_PRODUCTIVE.value.next   = w_obs_prod[1];
        hwif_in.OBS_OUT_BACKPRESSURE.value.next = w_obs_bp[1];
        hwif_in.OBS_OUT_STARVATION.value.next   = w_obs_starv[1];
        hwif_in.OBS_OUT_IDLE.value.next         = w_obs_idle[1];
    end

    // unused outputs of the shared blocks
    logic unused_h;
    assign unused_h = gen_busy ^ enc_frame_err ^ w_pipe_busy ^ w_pipe_done ^ (^gen_beats_total) ^ (^gen_beats_ch[0])
                    ^ (^chk_beats_total[0]) ^ (^chk_beats_total[1]) ^ (^chk_beats_ch[0][0]) ^ (^chk_beats_ch[1][0])
                    ^ (^w_cpuif_addr[11:RS_LOOP_REGS_MIN_ADDR_WIDTH])
                    // the unmapped-access telemetry and the tied-off windows'
                    // request signals: available to the harness, unread today
                    ^ w_unmapped_irq ^ (^w_unmapped_addr) ^ (^w_unmapped_count)
                    ^ rs_regs_apb_PSEL ^ rs_regs_apb_PENABLE ^ rs_regs_apb_PWRITE
                    ^ (^rs_regs_apb_PADDR) ^ (^rs_regs_apb_PWDATA) ^ (^rs_regs_apb_PSTRB)
                    ^ (^rs_regs_apb_PPROT)
                    ^ obs_apb_PSEL ^ obs_apb_PENABLE ^ obs_apb_PWRITE
                    ^ (^obs_apb_PADDR) ^ (^obs_apb_PWDATA) ^ (^obs_apb_PSTRB) ^ (^obs_apb_PPROT);

endmodule : rs_loop_harness
