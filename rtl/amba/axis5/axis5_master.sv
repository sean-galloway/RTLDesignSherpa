// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis5_master
// Purpose: AXI5-Stream Master module with AMBA5 extensions
//
// Documentation: docs/markdown/rtl-amba/axis5/axis5_master.md
// Subsystem: amba
//
// AXIS5 Extensions:
// - TWAKEUP: Wake-up signaling for power management
// - Interface parity protection (IHI 0051B ch. 5, Check_Type =
//   Odd_Parity_Byte_All), gated by ENABLE_PARITY:
//     TDATACHK  [DW/8]            carried from the FUB side through the skid
//     TSTRBCHK  [ceil(DW/64)]     carried
//     TLASTCHK  [1]               carried
//     TIDCHK    [ceil(IW/8)]      carried
//     TDESTCHK  [ceil(DESTW/8)]   carried
//     TUSERCHK  [ceil(UW/8)]      carried
//     TVALIDCHK [1]               generated here (~TVALID)
//     TWAKEUPCHK[1]               generated here (~TWAKEUP)
//     TREADYCHK [1]               input, checked here
//   ODD parity: a check bit plus the bits it covers always hold an odd number
//   of ones. Check bit [n] covers bits [8n+7:8n]; the top bit covers what is
//   left when the signal is not a whole number of bytes (IHI 0051B §5.3).
//   Every check bit is computed by rtl/common dataint_parity (odd, CHUNKS=1).
//
// Author: sean galloway
// Created: 2025-12-21

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axis5_master
#(
    parameter int SKID_DEPTH         = 4,
    parameter int AXIS_DATA_WIDTH    = 32,
    parameter int AXIS_ID_WIDTH      = 8,
    parameter int AXIS_DEST_WIDTH    = 4,
    parameter int AXIS_USER_WIDTH    = 1,
    parameter bit ENABLE_WAKEUP      = 1,       // Enable TWAKEUP signal
    parameter bit ENABLE_PARITY      = 0,       // Enable the *CHK check signals (IHI 0051B ch. 5)

    // Short and calculated params
    parameter int DW       = AXIS_DATA_WIDTH,
    parameter int IW       = AXIS_ID_WIDTH,
    parameter int DESTW    = AXIS_DEST_WIDTH,
    parameter int UW       = AXIS_USER_WIDTH,
    parameter int SW       = DW / 8,
    parameter int IW_WIDTH = (IW > 0) ? IW : 1,
    parameter int DESTW_WIDTH = (DESTW > 0) ? DESTW : 1,
    parameter int UW_WIDTH = (UW > 0) ? UW : 1,
    // Check-signal widths, IHI 0051B Table 5-1
    parameter int TDATACHK_W = SW,                     // TDATA_WIDTH/8
    parameter int TSTRBCHK_W = (SW + 7) / 8,           // ceil(TDATA_WIDTH/64)
    parameter int TIDCHK_W   = (IW_WIDTH + 7) / 8,     // ceil(TID_WIDTH/8)
    parameter int TDESTCHK_W = (DESTW_WIDTH + 7) / 8,  // ceil(TDEST_WIDTH/8)
    parameter int TUSERCHK_W = (UW_WIDTH + 7) / 8      // ceil(TUSER_WIDTH/8)
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI5-Stream Interface (Input Side - from FUB)
    input  logic [DW-1:0]              fub_axis_tdata,
    input  logic [SW-1:0]              fub_axis_tstrb,
    input  logic                       fub_axis_tlast,
    input  logic [IW_WIDTH-1:0]        fub_axis_tid,
    input  logic [DESTW_WIDTH-1:0]     fub_axis_tdest,
    input  logic [UW_WIDTH-1:0]        fub_axis_tuser,
    input  logic                       fub_axis_tvalid,
    output logic                       fub_axis_tready,
    // AXIS5 extensions
    input  logic                       fub_axis_twakeup,
    // Payload check signals from the FUB (carried end to end)
    input  logic [TDATACHK_W-1:0]      fub_axis_tdatachk,
    input  logic [TSTRBCHK_W-1:0]      fub_axis_tstrbchk,
    input  logic                       fub_axis_tlastchk,
    input  logic [TIDCHK_W-1:0]        fub_axis_tidchk,
    input  logic [TDESTCHK_W-1:0]      fub_axis_tdestchk,
    input  logic [TUSERCHK_W-1:0]      fub_axis_tuserchk,

    // Master AXI5-Stream Interface (Output Side)
    output logic [DW-1:0]              m_axis_tdata,
    output logic [SW-1:0]              m_axis_tstrb,
    output logic                       m_axis_tlast,
    output logic [IW_WIDTH-1:0]        m_axis_tid,
    output logic [DESTW_WIDTH-1:0]     m_axis_tdest,
    output logic [UW_WIDTH-1:0]        m_axis_tuser,
    output logic                       m_axis_tvalid,
    input  logic                       m_axis_tready,
    // AXIS5 extensions
    output logic                       m_axis_twakeup,
    // Check signals (IHI 0051B Table 5-1)
    output logic [TDATACHK_W-1:0]      m_axis_tdatachk,
    output logic [TSTRBCHK_W-1:0]      m_axis_tstrbchk,
    output logic                       m_axis_tlastchk,
    output logic [TIDCHK_W-1:0]        m_axis_tidchk,
    output logic [TDESTCHK_W-1:0]      m_axis_tdestchk,
    output logic [TUSERCHK_W-1:0]      m_axis_tuserchk,
    output logic                       m_axis_tvalidchk,
    input  logic                       m_axis_treadychk,
    output logic                       m_axis_twakeupchk,

    // Status outputs
    output logic                       busy,
    output logic                       parity_error      // Sticky: any check-signal mismatch seen
);

    // Payload check bits carried with the beat, low field last
    localparam int CHKW  = TDATACHK_W + TSTRBCHK_W + 1 + TIDCHK_W + TDESTCHK_W + TUSERCHK_W;
    // Total skid width: tdata+tstrb+tlast+tid+tdest+tuser+twakeup+check bits
    localparam int TSize = DW + SW + 1 + IW_WIDTH + DESTW_WIDTH + UW_WIDTH +
                           (ENABLE_WAKEUP ? 1 : 0) + (ENABLE_PARITY ? CHKW : 0);

    // SKID buffer connections
    logic [3:0]                int_t_count;
    logic [TSize-1:0]          int_t_pkt;
    logic                      int_skid_tvalid;
    logic                      int_skid_tready;

    // Busy signal indicates activity in the buffer
    assign busy = (int_t_count > 0) || fub_axis_tvalid;

    // Payload check bits from the FUB, in pack order
    logic [CHKW-1:0] w_fub_chk;
    assign w_fub_chk = {fub_axis_tdatachk, fub_axis_tstrbchk, fub_axis_tlastchk,
                        fub_axis_tidchk, fub_axis_tdestchk, fub_axis_tuserchk};

    // Build input packet based on enabled features
    logic [TSize-1:0] wr_data_packed;

    generate
        if (ENABLE_WAKEUP && ENABLE_PARITY) begin : g_pack_full
            assign wr_data_packed = {fub_axis_tdata, fub_axis_tstrb, fub_axis_tlast,
                                     fub_axis_tid, fub_axis_tdest, fub_axis_tuser,
                                     fub_axis_twakeup, w_fub_chk};
        end else if (ENABLE_WAKEUP && !ENABLE_PARITY) begin : g_pack_wakeup
            assign wr_data_packed = {fub_axis_tdata, fub_axis_tstrb, fub_axis_tlast,
                                     fub_axis_tid, fub_axis_tdest, fub_axis_tuser,
                                     fub_axis_twakeup};
        end else if (!ENABLE_WAKEUP && ENABLE_PARITY) begin : g_pack_parity
            assign wr_data_packed = {fub_axis_tdata, fub_axis_tstrb, fub_axis_tlast,
                                     fub_axis_tid, fub_axis_tdest, fub_axis_tuser,
                                     w_fub_chk};
        end else begin : g_pack_base
            assign wr_data_packed = {fub_axis_tdata, fub_axis_tstrb, fub_axis_tlast,
                                     fub_axis_tid, fub_axis_tdest, fub_axis_tuser};
        end
    endgenerate

    // Instantiate T Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH),
        .DATA_WIDTH(TSize)
    ) t_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axis_tvalid),
        .wr_ready               (fub_axis_tready),
        .wr_data                (wr_data_packed),
        .rd_valid               (int_skid_tvalid),
        .rd_ready               (int_skid_tready),
        .rd_count               (int_t_count),
        .rd_data                (int_t_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack signals from SKID buffer
    localparam int PARITY_OFFSET = ENABLE_PARITY ? CHKW : 0;

    // Unpack core signals
    assign m_axis_tdata = int_t_pkt[TSize-1 -: DW];
    assign m_axis_tstrb = int_t_pkt[TSize-DW-1 -: SW];
    assign m_axis_tlast = int_t_pkt[TSize-DW-SW-1];

    // Unpack optional signals with generate blocks
    generate
        if (IW > 0) begin : g_unpack_tid
            assign m_axis_tid = int_t_pkt[TSize-DW-SW-2 -: IW_WIDTH];
        end else begin : g_no_tid
            assign m_axis_tid = '0;
        end

        if (DESTW > 0) begin : g_unpack_tdest
            assign m_axis_tdest = int_t_pkt[TSize-DW-SW-2-IW_WIDTH -: DESTW_WIDTH];
        end else begin : g_no_tdest
            assign m_axis_tdest = '0;
        end

        if (UW > 0) begin : g_unpack_tuser
            assign m_axis_tuser = int_t_pkt[TSize-DW-SW-2-IW_WIDTH-DESTW_WIDTH -: UW_WIDTH];
        end else begin : g_no_tuser
            assign m_axis_tuser = '0;
        end

        if (ENABLE_WAKEUP) begin : g_unpack_twakeup
            assign m_axis_twakeup = int_t_pkt[PARITY_OFFSET];
        end else begin : g_no_twakeup
            assign m_axis_twakeup = 1'b0;
        end
    endgenerate

    assign m_axis_tvalid = int_skid_tvalid;
    assign int_skid_tready = m_axis_tready;

    // ------------------------------------------------------------------------
    // Interface parity (IHI 0051B ch. 5): ODD parity, check bit [n] covers
    // bits [8n+7:8n], the top bit covers the short remainder (§5.3). Every
    // check bit is one dataint_parity instance (CHUNKS=1, parity_type=0 =
    // odd) over its own piece, so the spec layout holds at any width.
    // ------------------------------------------------------------------------
    generate
        if (ENABLE_PARITY) begin : g_parity
            logic [CHKW-1:0]       w_skid_chk;    // check bits carried with the beat
            logic [TDATACHK_W-1:0] w_tdatachk_in, w_tdatachk_exp, w_tdatachk_err;
            logic [TSTRBCHK_W-1:0] w_tstrbchk_in, w_tstrbchk_exp, w_tstrbchk_err;
            logic w_tlastchk_in, w_tlastchk_exp, w_tlastchk_err;
            logic [TIDCHK_W-1:0] w_tidchk_in, w_tidchk_exp, w_tidchk_err;
            logic [TDESTCHK_W-1:0] w_tdestchk_in, w_tdestchk_exp, w_tdestchk_err;
            logic [TUSERCHK_W-1:0] w_tuserchk_in, w_tuserchk_exp, w_tuserchk_err;
            logic                  w_payload_err;
            logic                  w_ctrl_err;

            assign w_skid_chk = int_t_pkt[CHKW-1:0];
            assign w_tdatachk_in = w_skid_chk[CHKW-TDATACHK_W +: TDATACHK_W];
            for (genvar g = 0; g < TDATACHK_W; g++) begin : g_tdatachk
                localparam int LO = 8 * g;
                localparam int PIECE_W = (DW - LO < 8) ? (DW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PIECE_W)) u_par (
                    .data_in     (m_axis_tdata[LO +: PIECE_W]),
                    .parity_in   (w_tdatachk_in[g]),
                    .parity_type (1'b0),
                    .parity      (w_tdatachk_exp[g]),
                    .parity_err  (w_tdatachk_err[g])
                );
            end
            assign w_tstrbchk_in = w_skid_chk[CHKW-TDATACHK_W-TSTRBCHK_W +: TSTRBCHK_W];
            for (genvar g = 0; g < TSTRBCHK_W; g++) begin : g_tstrbchk
                localparam int LO = 8 * g;
                localparam int PIECE_W = (SW - LO < 8) ? (SW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PIECE_W)) u_par (
                    .data_in     (m_axis_tstrb[LO +: PIECE_W]),
                    .parity_in   (w_tstrbchk_in[g]),
                    .parity_type (1'b0),
                    .parity      (w_tstrbchk_exp[g]),
                    .parity_err  (w_tstrbchk_err[g])
                );
            end
            assign w_tlastchk_in = w_skid_chk[TIDCHK_W+TDESTCHK_W+TUSERCHK_W];
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_tlastchk (
                .data_in (m_axis_tlast), .parity_in (w_tlastchk_in), .parity_type (1'b0),
                .parity  (w_tlastchk_exp), .parity_err (w_tlastchk_err));
            assign w_tidchk_in = w_skid_chk[TDESTCHK_W+TUSERCHK_W +: TIDCHK_W];
            for (genvar g = 0; g < TIDCHK_W; g++) begin : g_tidchk
                localparam int LO = 8 * g;
                localparam int PIECE_W = (IW_WIDTH - LO < 8) ? (IW_WIDTH - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PIECE_W)) u_par (
                    .data_in     (m_axis_tid[LO +: PIECE_W]),
                    .parity_in   (w_tidchk_in[g]),
                    .parity_type (1'b0),
                    .parity      (w_tidchk_exp[g]),
                    .parity_err  (w_tidchk_err[g])
                );
            end
            assign w_tdestchk_in = w_skid_chk[TUSERCHK_W +: TDESTCHK_W];
            for (genvar g = 0; g < TDESTCHK_W; g++) begin : g_tdestchk
                localparam int LO = 8 * g;
                localparam int PIECE_W = (DESTW_WIDTH - LO < 8) ? (DESTW_WIDTH - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PIECE_W)) u_par (
                    .data_in     (m_axis_tdest[LO +: PIECE_W]),
                    .parity_in   (w_tdestchk_in[g]),
                    .parity_type (1'b0),
                    .parity      (w_tdestchk_exp[g]),
                    .parity_err  (w_tdestchk_err[g])
                );
            end
            assign w_tuserchk_in = w_skid_chk[0 +: TUSERCHK_W];
            for (genvar g = 0; g < TUSERCHK_W; g++) begin : g_tuserchk
                localparam int LO = 8 * g;
                localparam int PIECE_W = (UW_WIDTH - LO < 8) ? (UW_WIDTH - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PIECE_W)) u_par (
                    .data_in     (m_axis_tuser[LO +: PIECE_W]),
                    .parity_in   (w_tuserchk_in[g]),
                    .parity_type (1'b0),
                    .parity      (w_tuserchk_exp[g]),
                    .parity_err  (w_tuserchk_err[g])
                );
            end

            // Payload check bits out: carried, except where the parameters
            // remove the field (tied 0) -- then the odd parity of that 0.
            assign m_axis_tdatachk = w_tdatachk_in;
            assign m_axis_tstrbchk = w_tstrbchk_in;
            assign m_axis_tlastchk = w_tlastchk_in;
            if (IW > 0) begin : g_tidchk_carry
                assign m_axis_tidchk = w_tidchk_in;
            end else begin : g_tidchk_tie
                assign m_axis_tidchk = w_tidchk_exp;
            end
            if (DESTW > 0) begin : g_tdestchk_carry
                assign m_axis_tdestchk = w_tdestchk_in;
            end else begin : g_tdestchk_tie
                assign m_axis_tdestchk = w_tdestchk_exp;
            end
            if (UW > 0) begin : g_tuserchk_carry
                assign m_axis_tuserchk = w_tuserchk_in;
            end else begin : g_tuserchk_tie
                assign m_axis_tuserchk = w_tuserchk_exp;
            end

            // Payload checks are enabled by TVALID (Table 5-1). An absent
            // field's check is omitted (§5.3), so it is not checked.
            assign w_payload_err = m_axis_tvalid && (
                (|w_tdatachk_err) || (|w_tstrbchk_err) || w_tlastchk_err ||
                ((IW > 0)    && (|w_tidchk_err))   ||
                ((DESTW > 0) && (|w_tdestchk_err)) ||
                ((UW > 0)    && (|w_tuserchk_err)));

            // Single-bit critical controls: the check bit is the inversion
            // (§5.3). TVALIDCHK and TWAKEUPCHK are generated here; TREADYCHK
            // arrives from the receiver and is checked every cycle out of
            // reset (Check Enable = ARESETn).
            logic w_tvalidchk_err_unused, w_twakeupchk_err_unused, w_treadychk_exp_unused;
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_tvalidchk (
                .data_in (m_axis_tvalid), .parity_in (1'b0), .parity_type (1'b0),
                .parity  (m_axis_tvalidchk), .parity_err (w_tvalidchk_err_unused));
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_twakeupchk (
                .data_in (m_axis_twakeup), .parity_in (1'b0), .parity_type (1'b0),
                .parity  (m_axis_twakeupchk), .parity_err (w_twakeupchk_err_unused));
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_treadychk (
                .data_in (m_axis_tready), .parity_in (m_axis_treadychk), .parity_type (1'b0),
                .parity  (w_treadychk_exp_unused), .parity_err (w_ctrl_err));

            // Sticky parity error
            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    parity_error <= 1'b0;
                end else if (w_payload_err || w_ctrl_err) begin
                    parity_error <= 1'b1;
                end
            )

            /* verilator lint_off UNUSEDSIGNAL */
            logic unused_par;
            assign unused_par = ^{w_tdatachk_exp, w_tstrbchk_exp, w_tlastchk_exp,
                                  w_tidchk_exp, w_tdestchk_exp, w_tuserchk_exp,
                                  w_tvalidchk_err_unused, w_twakeupchk_err_unused,
                                  w_treadychk_exp_unused};
            /* verilator lint_on UNUSEDSIGNAL */
        end else begin : g_no_parity
            assign m_axis_tdatachk   = '0;
            assign m_axis_tstrbchk   = '0;
            assign m_axis_tlastchk   = 1'b0;
            assign m_axis_tidchk     = '0;
            assign m_axis_tdestchk   = '0;
            assign m_axis_tuserchk   = '0;
            assign m_axis_tvalidchk  = 1'b0;
            assign m_axis_twakeupchk = 1'b0;
            assign parity_error      = 1'b0;

            /* verilator lint_off UNUSEDSIGNAL */
            logic unused_chk_inputs;
            assign unused_chk_inputs = ^{w_fub_chk, m_axis_treadychk};
            /* verilator lint_on UNUSEDSIGNAL */
        end
    endgenerate

endmodule : axis5_master
