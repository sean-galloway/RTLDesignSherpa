// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis5_slave
// Purpose: AXI5-Stream Slave module with AMBA5 extensions
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// AXIS5 Extensions:
// - TWAKEUP: Wake-up signaling for power management
// - TPARITY: Optional parity for TDATA integrity
//
// Author: sean galloway
// Created: 2025-12-21

`timescale 1ns / 1ps

module axis5_slave
#(
    parameter int SKID_DEPTH         = 4,
    parameter int AXIS_DATA_WIDTH    = 32,
    parameter int AXIS_ID_WIDTH      = 8,
    parameter int AXIS_DEST_WIDTH    = 4,
    parameter int AXIS_USER_WIDTH    = 1,
    parameter bit ENABLE_WAKEUP      = 1,       // Enable TWAKEUP signal
    parameter bit ENABLE_PARITY      = 0,       // Enable TPARITY signal

    // Short and calculated params
    parameter int DW       = AXIS_DATA_WIDTH,
    parameter int IW       = AXIS_ID_WIDTH,
    parameter int DESTW    = AXIS_DEST_WIDTH,
    parameter int UW       = AXIS_USER_WIDTH,
    parameter int SW       = DW / 8,
    parameter int PW       = SW,                // Parity width (1 bit per byte)
    parameter int IW_WIDTH = (IW > 0) ? IW : 1,
    parameter int DESTW_WIDTH = (DESTW > 0) ? DESTW : 1,
    parameter int UW_WIDTH = (UW > 0) ? UW : 1,
    parameter int PW_WIDTH = ENABLE_PARITY ? PW : 1,
    // Total size includes: tdata+tstrb+tlast+tid+tdest+tuser+twakeup+tparity
    parameter int TSize    = DW + SW + 1 + IW_WIDTH + DESTW_WIDTH + UW_WIDTH +
                             (ENABLE_WAKEUP ? 1 : 0) + (ENABLE_PARITY ? PW : 0)
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI5-Stream Interface (Input Side)
    input  logic [DW-1:0]              s_axis_tdata,
    input  logic [SW-1:0]              s_axis_tstrb,
    input  logic                       s_axis_tlast,
    input  logic [IW_WIDTH-1:0]        s_axis_tid,
    input  logic [DESTW_WIDTH-1:0]     s_axis_tdest,
    input  logic [UW_WIDTH-1:0]        s_axis_tuser,
    input  logic                       s_axis_tvalid,
    output logic                       s_axis_tready,
    // AXIS5 extensions
    input  logic                       s_axis_twakeup,
    input  logic [PW_WIDTH-1:0]        s_axis_tparity,

    // Master AXI5-Stream Interface (Output Side to backend/FUB)
    output logic [DW-1:0]              fub_axis_tdata,
    output logic [SW-1:0]              fub_axis_tstrb,
    output logic                       fub_axis_tlast,
    output logic [IW_WIDTH-1:0]        fub_axis_tid,
    output logic [DESTW_WIDTH-1:0]     fub_axis_tdest,
    output logic [UW_WIDTH-1:0]        fub_axis_tuser,
    output logic                       fub_axis_tvalid,
    input  logic                       fub_axis_tready,
    // AXIS5 extensions
    output logic                       fub_axis_twakeup,
    output logic [PW_WIDTH-1:0]        fub_axis_tparity,

    // Status outputs
    output logic                       busy,
    output logic                       parity_error      // Parity error detected
);

    // Internal connections for skid buffer
    logic [3:0]                int_t_count;
    logic [TSize-1:0]          int_t_pkt;
    logic                      int_skid_tvalid;
    logic                      int_skid_tready;

    // Parity checking
    logic [PW-1:0]             calculated_parity;
    logic                      parity_mismatch;

    // Busy signal indicates activity in the buffer
    assign busy = (int_t_count > 0) || s_axis_tvalid;

    // Build input packet based on enabled features
    logic [TSize-1:0] wr_data_packed;

    generate
        if (ENABLE_WAKEUP && ENABLE_PARITY) begin : g_pack_full
            assign wr_data_packed = {s_axis_tdata, s_axis_tstrb, s_axis_tlast,
                                     s_axis_tid, s_axis_tdest, s_axis_tuser,
                                     s_axis_twakeup, s_axis_tparity};
        end else if (ENABLE_WAKEUP && !ENABLE_PARITY) begin : g_pack_wakeup
            assign wr_data_packed = {s_axis_tdata, s_axis_tstrb, s_axis_tlast,
                                     s_axis_tid, s_axis_tdest, s_axis_tuser,
                                     s_axis_twakeup};
        end else if (!ENABLE_WAKEUP && ENABLE_PARITY) begin : g_pack_parity
            assign wr_data_packed = {s_axis_tdata, s_axis_tstrb, s_axis_tlast,
                                     s_axis_tid, s_axis_tdest, s_axis_tuser,
                                     s_axis_tparity};
        end else begin : g_pack_base
            assign wr_data_packed = {s_axis_tdata, s_axis_tstrb, s_axis_tlast,
                                     s_axis_tid, s_axis_tdest, s_axis_tuser};
        end
    endgenerate

    // Instantiate T Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH),
        .DATA_WIDTH(TSize),
        .INSTANCE_NAME("AXIS5_T_SKID")
    ) i_t_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (s_axis_tvalid),
        .wr_ready               (s_axis_tready),
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
    // Base offset calculations
    localparam int PARITY_OFFSET = ENABLE_PARITY ? PW : 0;
    localparam int WAKEUP_OFFSET = ENABLE_WAKEUP ? 1 : 0;
    localparam int USER_OFFSET = PARITY_OFFSET + WAKEUP_OFFSET;
    localparam int DEST_OFFSET = USER_OFFSET + UW_WIDTH;
    localparam int ID_OFFSET = DEST_OFFSET + DESTW_WIDTH;
    localparam int LAST_OFFSET = ID_OFFSET + IW_WIDTH;
    localparam int STRB_OFFSET = LAST_OFFSET + 1;
    localparam int DATA_OFFSET = STRB_OFFSET + SW;

    // Unpack core signals
    assign fub_axis_tdata = int_t_pkt[TSize-1 -: DW];
    assign fub_axis_tstrb = int_t_pkt[TSize-DW-1 -: SW];
    assign fub_axis_tlast = int_t_pkt[TSize-DW-SW-1];

    // Unpack optional signals with generate blocks
    generate
        if (IW > 0) begin : g_unpack_tid
            assign fub_axis_tid = int_t_pkt[TSize-DW-SW-2 -: IW_WIDTH];
        end else begin : g_no_tid
            assign fub_axis_tid = '0;
        end

        if (DESTW > 0) begin : g_unpack_tdest
            assign fub_axis_tdest = int_t_pkt[TSize-DW-SW-2-IW_WIDTH -: DESTW_WIDTH];
        end else begin : g_no_tdest
            assign fub_axis_tdest = '0;
        end

        if (UW > 0) begin : g_unpack_tuser
            assign fub_axis_tuser = int_t_pkt[TSize-DW-SW-2-IW_WIDTH-DESTW_WIDTH -: UW_WIDTH];
        end else begin : g_no_tuser
            assign fub_axis_tuser = '0;
        end

        if (ENABLE_WAKEUP) begin : g_unpack_twakeup
            assign fub_axis_twakeup = int_t_pkt[PARITY_OFFSET];
        end else begin : g_no_twakeup
            assign fub_axis_twakeup = 1'b0;
        end

        if (ENABLE_PARITY) begin : g_unpack_tparity
            assign fub_axis_tparity = int_t_pkt[PW-1:0];
        end else begin : g_no_tparity
            assign fub_axis_tparity = '0;
        end
    endgenerate

    assign fub_axis_tvalid = int_skid_tvalid;
    assign int_skid_tready = fub_axis_tready;

    // Parity calculation and checking (if enabled)
    generate
        if (ENABLE_PARITY) begin : g_parity_check
            // Calculate parity for each byte
            genvar i;
            for (i = 0; i < SW; i = i + 1) begin : g_parity_calc
                assign calculated_parity[i] = ^s_axis_tdata[i*8 +: 8];
            end

            // Compare calculated parity with received parity on input
            assign parity_mismatch = (calculated_parity != s_axis_tparity) && s_axis_tvalid;

            // Register parity error
            always_ff @(posedge aclk or negedge aresetn) begin
                if (!aresetn) begin
                    parity_error <= 1'b0;
                end else if (parity_mismatch && s_axis_tvalid && s_axis_tready) begin
                    parity_error <= 1'b1;
                end
            end
        end else begin : g_no_parity_check
            assign calculated_parity = '0;
            assign parity_mismatch = 1'b0;
            assign parity_error = 1'b0;
        end
    endgenerate

endmodule : axis5_slave
