// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: bch_encoder_axis4
// Description: Binary BCH systematic encoder with AXI4-Stream interfaces.
//
//   This is the component's integration top (TASK-006). `bch_encoder_core`
//   speaks a bare valid/ready/last handshake, which is the right interface for
//   the algorithm but the wrong one for a fabric. This wraps it in the house
//   `axis4_slave` / `axis4_master` skid wrappers so a consumer connects a
//   stream, not ten renamed wires.
//
// Parameters:
//   FIELD_DIM       GF(2^m) field dimension, m
//   PRIM_POLY       primitive polynomial of degree m, as an integer
//   T_BITS          t, correctable bit errors per block
//   N_BITS          n, codeword length in bits
//   FIRST_ROOT      b in g(x) = lcm of minimal polynomials of alpha^b ..
//                   alpha^(b+2t-1)
//   BITS_PER_BEAT   B, the AXI4-Stream beat width; also the core's in_data/
//                   out_data width
//   SKID_DEPTH      depth of the two AXIS skid buffers, 2..8
//   AXIS_*_WIDTH    tid / tdest / tuser widths, captured and held per block
//
// Notes:
//   - tstrb vs keep. The core's `keep` is PER BIT; AXI4-Stream's tstrb is
//     PER BYTE. When K_BITS and N_BITS are both byte-aligned the core's keep
//     is guaranteed byte-aligned, so tstrb carries it (one strobe bit per byte,
//     high only when all eight keep bits in that byte are high). In that mode
//     tuser is driven to zero. When either K or N is not byte-aligned the keep
//     cannot be expressed per byte, so it rides the low BITS_PER_BEAT bits of
//     tuser and tstrb is driven all-ones -- the same rule the RS wrappers use
//     for non-byte-sized symbols.
//
//     Profile keep modes:
//       (m=6, n=63, k=56, B=8)  tuser mode  (63 is not byte-aligned)
//       (m=6, n=63, k=51, B=8)  tuser mode  (63 is not byte-aligned)
//       (m=13, n=4224, k=4120, B=8)  tstrb mode
//       (m=13, n=4224, k=4120, B=32) tstrb mode (k is not a multiple of B, so
//            the encoder emits a partial data-phase beat with tlast=0; the
//            keep is still byte-aligned and is carried faithfully by tstrb)
//   - No beat packer is instantiated. The BCH encoder core already places
//     partial beats only at the end of a phase (the final data beat and the
//     final parity beat). The wrapper preserves that beat layout and carries
//     the per-bit keep through the appropriate sideband.
//   - tid and tdest are captured from the block's FIRST accepted beat and held
//     until its last output beat leaves; parity beats carry the same id/dest.
module bch_encoder_axis4
    import bch_pkg::*;
#(
    parameter int FIELD_DIM     = bch_pkg::FIELD_DIM,
    parameter int PRIM_POLY     = bch_pkg::PRIM_POLY,
    parameter int T_BITS        = bch_pkg::T_BITS,
    parameter int N_BITS        = bch_pkg::N_BITS,
    parameter int FIRST_ROOT    = bch_pkg::FIRST_ROOT,
    parameter int BITS_PER_BEAT = bch_pkg::BITS_PER_BEAT,
    // derived, exposed for the consumer's convenience
    parameter int K_BITS        = N_BITS - bch_degree_g(FIELD_DIM, PRIM_POLY, T_BITS, FIRST_ROOT),
    parameter int SKID_DEPTH    = 2,
    parameter int AXIS_ID_WIDTH = 0,
    parameter int AXIS_DEST_WIDTH = 0,
    // Default is BITS_PER_BEAT so the package default (n=63, non-byte-aligned)
    // can carry per-bit keep on tuser without an explicit override.
    parameter int AXIS_USER_WIDTH = BITS_PER_BEAT,
    // zero-width AXIS sidebands still need a 1-bit wire
    parameter int IW            = (AXIS_ID_WIDTH   > 0) ? AXIS_ID_WIDTH   : 1,
    parameter int DESTW         = (AXIS_DEST_WIDTH > 0) ? AXIS_DEST_WIDTH : 1,
    parameter int UW            = (AXIS_USER_WIDTH > 0) ? AXIS_USER_WIDTH : 1
) (
    input  logic                       aclk,
    input  logic                       aresetn,

    // data bits in
    input  logic [BITS_PER_BEAT-1:0]   s_axis_tdata,
    input  logic [BITS_PER_BEAT/8-1:0] s_axis_tstrb,
    input  logic                       s_axis_tlast,
    input  logic [IW-1:0]              s_axis_tid,
    input  logic [DESTW-1:0]           s_axis_tdest,
    input  logic [UW-1:0]              s_axis_tuser,
    input  logic                       s_axis_tvalid,
    output logic                       s_axis_tready,

    // coded bits out: k data beats then the parity beats
    output logic [BITS_PER_BEAT-1:0]   m_axis_tdata,
    output logic [BITS_PER_BEAT/8-1:0] m_axis_tstrb,
    output logic                       m_axis_tlast,
    output logic [IW-1:0]              m_axis_tid,
    output logic [DESTW-1:0]           m_axis_tdest,
    output logic [UW-1:0]              m_axis_tuser,
    output logic                       m_axis_tvalid,
    input  logic                       m_axis_tready,

    // one-cycle pulse: a block ended with other than k data bits
    output logic                       frame_err
);

    localparam int B  = BITS_PER_BEAT;
    localparam int SW = BITS_PER_BEAT / 8;

    // Byte-aligned codes can use tstrb; everything else needs per-bit keep.
    localparam bit KeepByteAligned = (K_BITS % 8 == 0) && (N_BITS % 8 == 0);

    initial begin : g_param_check
        if (B > K_BITS)
            $fatal(1, "bch_encoder_axis4: BITS_PER_BEAT %0d exceeds K_BITS %0d",
                   B, K_BITS);
        if (KeepByteAligned && (B % 8 != 0))
            $fatal(1, "bch_encoder_axis4: byte-aligned mode needs B multiple of 8 (%0d)", B);
        if (!KeepByteAligned && AXIS_USER_WIDTH < B)
            $fatal(1, "bch_encoder_axis4: tuser mode needs USER_WIDTH >= B (%0d/%0d)",
                   B, AXIS_USER_WIDTH);
    end

    // -------------------------------------------------------------------------
    // intake skid
    // -------------------------------------------------------------------------
    logic [BITS_PER_BEAT-1:0] in_tdata;
    logic [SW-1:0]            in_tstrb;
    logic                     in_tlast, in_tvalid, in_tready;
    logic [IW-1:0]            in_tid;
    logic [DESTW-1:0]         in_tdest;
    logic [UW-1:0]            in_tuser;

    /* verilator lint_off PINCONNECTEMPTY */
    axis4_slave #(
        .SKID_DEPTH(SKID_DEPTH), .AXIS_DATA_WIDTH(BITS_PER_BEAT),
        .AXIS_ID_WIDTH(AXIS_ID_WIDTH), .AXIS_DEST_WIDTH(AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH(AXIS_USER_WIDTH)
    ) u_in (
        .aclk(aclk), .aresetn(aresetn),
        .s_axis_tdata(s_axis_tdata), .s_axis_tstrb(s_axis_tstrb),
        .s_axis_tlast(s_axis_tlast), .s_axis_tid(s_axis_tid),
        .s_axis_tdest(s_axis_tdest), .s_axis_tuser(s_axis_tuser),
        .s_axis_tvalid(s_axis_tvalid), .s_axis_tready(s_axis_tready),
        .fub_axis_tdata(in_tdata), .fub_axis_tstrb(in_tstrb),
        .fub_axis_tlast(in_tlast), .fub_axis_tid(in_tid),
        .fub_axis_tdest(in_tdest), .fub_axis_tuser(in_tuser),
        .fub_axis_tvalid(in_tvalid), .fub_axis_tready(in_tready),
        .busy());
    /* verilator lint_on PINCONNECTEMPTY */

    // -------------------------------------------------------------------------
    // keep mapping: AXI4-Stream sideband -> core per-bit keep
    // -------------------------------------------------------------------------
    logic [B-1:0] w_in_keep;

    if (KeepByteAligned) begin : g_keep_in_strb
        always_comb begin
            w_in_keep = '0;
            for (int u = 0; u < SW; u++) begin
                if (in_tstrb[u])
                    w_in_keep[u*8 +: 8] = {8{1'b1}};
            end
        end
    end else begin : g_keep_in_user
        assign w_in_keep = in_tuser[B-1:0];
    end

    // -------------------------------------------------------------------------
    // the encoder core
    // -------------------------------------------------------------------------
    logic [B-1:0] core_data;
    logic [B-1:0] core_keep;
    logic         core_last, core_valid, core_ready;
    logic         core_frame_err;

    bch_encoder_core #(
        .FIELD_DIM(FIELD_DIM), .PRIM_POLY(PRIM_POLY), .T_BITS(T_BITS),
        .N_BITS(N_BITS), .BITS_PER_BEAT(BITS_PER_BEAT),
        .FIRST_ROOT(FIRST_ROOT), .K_BITS(K_BITS),
        .SKID_DEPTH(SKID_DEPTH)
    ) u_core (
        .aclk(aclk), .aresetn(aresetn),
        .in_valid(in_tvalid), .in_ready(in_tready), .in_data(in_tdata),
        .in_keep(w_in_keep), .in_last(in_tlast),
        .out_valid(core_valid), .out_ready(core_ready), .out_data(core_data),
        .out_keep(core_keep), .out_last(core_last),
        .frame_err(core_frame_err));

    assign frame_err = core_frame_err;

    // -------------------------------------------------------------------------
    // id / dest passthrough: captured on the block's first accepted beat and
    // held until its last output beat leaves. A block leaves as more beats
    // than it entered as, so these cannot ride the datapath.
    // -------------------------------------------------------------------------
    logic [IW-1:0]    r_tid;
    logic [DESTW-1:0] r_tdest;
    logic             r_have;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_tid <= '0; r_tdest <= '0; r_have <= 1'b0;
        end else begin
            if (in_tvalid && in_tready && !r_have) begin
                r_tid <= in_tid; r_tdest <= in_tdest; r_have <= 1'b1;
            end
            if (core_valid && core_ready && core_last) r_have <= 1'b0;
        end
    end

    // -------------------------------------------------------------------------
    // keep mapping: core per-bit keep -> AXI4-Stream sideband
    // -------------------------------------------------------------------------
    logic [SW-1:0] w_out_tstrb;
    logic [UW-1:0] w_out_tuser;

    if (KeepByteAligned) begin : g_keep_out_strb
        always_comb begin
            w_out_tuser = '0;
            w_out_tstrb = '0;
            for (int u = 0; u < SW; u++) begin
                w_out_tstrb[u] = &core_keep[u*8 +: 8];
            end
        end
    end else begin : g_keep_out_user
        always_comb begin
            w_out_tstrb = {SW{1'b1}};
            w_out_tuser = '0;
            w_out_tuser[B-1:0] = core_keep;
        end
    end

    // -------------------------------------------------------------------------
    // outlet skid
    // -------------------------------------------------------------------------
    /* verilator lint_off PINCONNECTEMPTY */
    axis4_master #(
        .SKID_DEPTH(SKID_DEPTH), .AXIS_DATA_WIDTH(BITS_PER_BEAT),
        .AXIS_ID_WIDTH(AXIS_ID_WIDTH), .AXIS_DEST_WIDTH(AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH(AXIS_USER_WIDTH)
    ) u_out (
        .aclk(aclk), .aresetn(aresetn),
        .fub_axis_tdata(core_data), .fub_axis_tstrb(w_out_tstrb),
        .fub_axis_tlast(core_last), .fub_axis_tid(r_tid),
        .fub_axis_tdest(r_tdest), .fub_axis_tuser(w_out_tuser),
        .fub_axis_tvalid(core_valid), .fub_axis_tready(core_ready),
        .m_axis_tdata(m_axis_tdata), .m_axis_tstrb(m_axis_tstrb),
        .m_axis_tlast(m_axis_tlast), .m_axis_tid(m_axis_tid),
        .m_axis_tdest(m_axis_tdest), .m_axis_tuser(m_axis_tuser),
        .m_axis_tvalid(m_axis_tvalid), .m_axis_tready(m_axis_tready),
        .busy());
    /* verilator lint_on PINCONNECTEMPTY */

endmodule
