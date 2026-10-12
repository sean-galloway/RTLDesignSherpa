// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis5_master_cg
// Purpose: AXI5-Stream Master module with clock gating and AMBA5 extensions
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// AXIS5 Extensions:
// - TWAKEUP: Wake-up signaling for power management
// - Interface parity (IHI 0051B ch. 5): the *CHK check signals, ODD parity,
//   one check bit per 8 bits, when ENABLE_PARITY (see axis5_master)
// - Clock gating for power savings
//
// Author: sean galloway
// Created: 2025-12-21

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axis5_master_cg
#(
    parameter int SKID_DEPTH         = 4,
    parameter int AXIS_DATA_WIDTH    = 32,
    parameter int AXIS_ID_WIDTH      = 8,
    parameter int AXIS_DEST_WIDTH    = 4,
    parameter int AXIS_USER_WIDTH    = 1,
    parameter bit ENABLE_WAKEUP      = 1,
    parameter bit ENABLE_PARITY      = 0,
    parameter int CG_IDLE_COUNT_WIDTH = 4,

    // Short and calculated params
    parameter int DW       = AXIS_DATA_WIDTH,
    parameter int IW       = AXIS_ID_WIDTH,
    parameter int DESTW    = AXIS_DEST_WIDTH,
    parameter int UW       = AXIS_USER_WIDTH,
    parameter int SW       = DW / 8,
    parameter int ICW      = CG_IDLE_COUNT_WIDTH,
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

    // Clock gating configuration
    input  logic                       cfg_cg_enable,
    input  logic [ICW-1:0]             cfg_cg_idle_count,

    // Slave AXI5-Stream Interface (Input Side - from FUB)
    input  logic [DW-1:0]              fub_axis5_tdata,
    input  logic [SW-1:0]              fub_axis5_tstrb,
    input  logic                       fub_axis5_tlast,
    input  logic [IW_WIDTH-1:0]        fub_axis5_tid,
    input  logic [DESTW_WIDTH-1:0]     fub_axis5_tdest,
    input  logic [UW_WIDTH-1:0]        fub_axis5_tuser,
    input  logic                       fub_axis5_tvalid,
    output logic                       fub_axis5_tready,
    input  logic                       fub_axis5_twakeup,
    input  logic [TDATACHK_W-1:0]      fub_axis5_tdatachk,
    input  logic [TSTRBCHK_W-1:0]      fub_axis5_tstrbchk,
    input  logic                       fub_axis5_tlastchk,
    input  logic [TIDCHK_W-1:0]        fub_axis5_tidchk,
    input  logic [TDESTCHK_W-1:0]      fub_axis5_tdestchk,
    input  logic [TUSERCHK_W-1:0]      fub_axis5_tuserchk,

    // Master AXI5-Stream Interface (Output Side)
    output logic [DW-1:0]              m_axis5_tdata,
    output logic [SW-1:0]              m_axis5_tstrb,
    output logic                       m_axis5_tlast,
    output logic [IW_WIDTH-1:0]        m_axis5_tid,
    output logic [DESTW_WIDTH-1:0]     m_axis5_tdest,
    output logic [UW_WIDTH-1:0]        m_axis5_tuser,
    output logic                       m_axis5_tvalid,
    input  logic                       m_axis5_tready,
    output logic                       m_axis5_twakeup,
    output logic [TDATACHK_W-1:0]      m_axis5_tdatachk,
    output logic [TSTRBCHK_W-1:0]      m_axis5_tstrbchk,
    output logic                       m_axis5_tlastchk,
    output logic [TIDCHK_W-1:0]        m_axis5_tidchk,
    output logic [TDESTCHK_W-1:0]      m_axis5_tdestchk,
    output logic [TUSERCHK_W-1:0]      m_axis5_tuserchk,
    output logic                       m_axis5_tvalidchk,
    input  logic                       m_axis5_treadychk,
    output logic                       m_axis5_twakeupchk,

    // Status outputs
    output logic                       busy,
    output logic                       parity_error,
    output logic                       cg_gating,
    // Idle indicator: activity terms quiet (registered ~wakeup)
    output logic                       cg_idle
);

    // Internal gated clock
    logic gated_clk;
    logic r_wakeup;

    // Internal busy signal from core
    logic core_busy;

    // Wakeup logic - keep clock active when:
    // 1. Input has valid data
    // 2. Core is busy
    // 3. Output has pending data
    // 4. Downstream is ready (accepting data)
    // 5. Wakeup signal is asserted
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))
            r_wakeup <= 1'b1;
        else
            r_wakeup <= fub_axis5_tvalid || core_busy || m_axis5_tvalid || fub_axis5_twakeup;
    )

    // Instantiate clock gate controller
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH (CG_IDLE_COUNT_WIDTH)
    ) u_clock_gate_ctrl (
        .clk_in              (aclk),
        .aresetn             (aresetn),
        .cfg_cg_enable       (cfg_cg_enable),
        .cfg_cg_idle_count   (cfg_cg_idle_count),
        .user_valid          (r_wakeup),
        .axi_valid           (1'b0),
        .clk_out             (gated_clk),
        .gating              (cg_gating),
        /* verilator lint_off PINCONNECTEMPTY */
        .idle                (cg_idle)
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Core AXIS5 master instance
    logic int_fub_axis5_tready;
    // Masked with !cg_gating. This READY is driven by a register on the
    // GATED clock, so when that clock stops the register HOLDS its last
    // value -- it does not fall. A producer would see a still-asserted
    // READY, drive a beat, consider it accepted, and the gated logic would
    // never observe it. axis4_slave_cg and the axil4/axi4 families already
    // guard this; these two did not (TASK-076).
    assign fub_axis5_tready = cg_gating ? 1'b0 : int_fub_axis5_tready;

    axis5_master #(
        .SKID_DEPTH       (SKID_DEPTH),
        .AXIS_DATA_WIDTH  (AXIS_DATA_WIDTH),
        .AXIS_ID_WIDTH    (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH  (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH  (AXIS_USER_WIDTH),
        .ENABLE_WAKEUP    (ENABLE_WAKEUP),
        .ENABLE_PARITY    (ENABLE_PARITY)
    ) u_axis5_master (
        .aclk              (gated_clk),
        .aresetn           (aresetn),

        .fub_axis_tdata    (fub_axis5_tdata),
        .fub_axis_tstrb    (fub_axis5_tstrb),
        .fub_axis_tlast    (fub_axis5_tlast),
        .fub_axis_tid      (fub_axis5_tid),
        .fub_axis_tdest    (fub_axis5_tdest),
        .fub_axis_tuser    (fub_axis5_tuser),
        .fub_axis_tvalid   (fub_axis5_tvalid),
        .fub_axis_tready   (int_fub_axis5_tready),
        .fub_axis_twakeup  (fub_axis5_twakeup),
        .fub_axis_tdatachk (fub_axis5_tdatachk),
        .fub_axis_tstrbchk (fub_axis5_tstrbchk),
        .fub_axis_tlastchk (fub_axis5_tlastchk),
        .fub_axis_tidchk   (fub_axis5_tidchk),
        .fub_axis_tdestchk (fub_axis5_tdestchk),
        .fub_axis_tuserchk (fub_axis5_tuserchk),

        .m_axis_tdata      (m_axis5_tdata),
        .m_axis_tstrb      (m_axis5_tstrb),
        .m_axis_tlast      (m_axis5_tlast),
        .m_axis_tid        (m_axis5_tid),
        .m_axis_tdest      (m_axis5_tdest),
        .m_axis_tuser      (m_axis5_tuser),
        .m_axis_tvalid     (m_axis5_tvalid),
        .m_axis_tready     (m_axis5_tready),
        .m_axis_twakeup    (m_axis5_twakeup),
        .m_axis_tdatachk   (m_axis5_tdatachk),
        .m_axis_tstrbchk   (m_axis5_tstrbchk),
        .m_axis_tlastchk   (m_axis5_tlastchk),
        .m_axis_tidchk     (m_axis5_tidchk),
        .m_axis_tdestchk   (m_axis5_tdestchk),
        .m_axis_tuserchk   (m_axis5_tuserchk),
        .m_axis_tvalidchk  (m_axis5_tvalidchk),
        .m_axis_treadychk  (m_axis5_treadychk),
        .m_axis_twakeupchk (m_axis5_twakeupchk),

        .busy              (core_busy),
        .parity_error      (parity_error)
    );

    assign busy = core_busy;

endmodule : axis5_master_cg
