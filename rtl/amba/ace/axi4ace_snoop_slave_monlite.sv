// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4ace_snoop_slave_monlite
// Purpose: axi4ace_snoop_slave with the lite snoop monitor (axi4ace_snoop_monitor_lite).
//
// Documentation: docs/markdown/rtl-amba/monitor/axi_monitor_lite_wrappers.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-10-05
//
// ============================================================================
// The lite-monitor sibling of the full monitor wrapper.  Same core, same taps,
// same 128-bit packets on the same monbus with the same UNIT/AGENT ids, but
// only the lite control subset is exposed.  The monitor never stalls the snoop
// channels: events it cannot deliver are dropped and counted.
// ============================================================================
`timescale 1ns / 1ps

module axi4ace_snoop_slave_monlite
#(
    // ---- Monitor parameters ----
    parameter bit          USE_MONITOR      = 1'b1,
    parameter logic [7:0]  UNIT_ID          = 8'h01,
    parameter logic [15:0] AGENT_ID         = 16'h000A,
    parameter int          MAX_TRANSACTIONS = 8,      // maps to monitor MAX_SNOOPS
    parameter int          OUT_DEPTH        = 4,
    parameter int          ACLK_MHZ         = 100,
    parameter int          CFI_MIN_FREQ_MHZ = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ = ACLK_MHZ,
    // ---- Core parameters (passed through verbatim to axi4ace_snoop_slave) ----
    parameter int SKID_DEPTH_AC = 2,
    parameter int SKID_DEPTH_CR = 4,
    parameter int SKID_DEPTH_CD = 4,
    parameter int ADDR_WIDTH    = 32,
    parameter int DATA_WIDTH    = 32,
    // Short and calculated params
    parameter int AW            = ADDR_WIDTH,
    parameter int DW            = DATA_WIDTH,
    parameter int ACSize        = AW + 4 + 3,
    parameter int CRSize        = 5,
    parameter int CDSize        = DW + 1
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI Interface (Input Side) -- manager/CCU -> cache
    input  logic [AW-1:0]              m_axi_acaddr,
    input  logic [3:0]                 m_axi_acsnoop,
    input  logic [2:0]                 m_axi_acprot,
    input  logic                       m_axi_acvalid,
    output logic                       m_axi_acready,

    output logic [4:0]                 m_axi_crresp,
    output logic                       m_axi_crvalid,
    input  logic                       m_axi_crready,

    output logic [DW-1:0]              m_axi_cddata,
    output logic                       m_axi_cdlast,
    output logic                       m_axi_cdvalid,
    input  logic                       m_axi_cdready,

    // Fabric/Upstream Buffer Interface (Output Side) -- cache snoop FSM
    output logic [AW-1:0]              fub_acaddr,
    output logic [3:0]                 fub_acsnoop,
    output logic [2:0]                 fub_acprot,
    output logic                       fub_acvalid,
    input  logic                       fub_acready,

    input  logic [4:0]                 fub_crresp,
    input  logic                       fub_crvalid,
    output logic                       fub_crready,

    input  logic [DW-1:0]              fub_cddata,
    input  logic                       fub_cdlast,
    input  logic                       fub_cdvalid,
    output logic                       fub_cdready,

    // Status outputs for clock gating
    output logic                       busy,

    // ---- Monitor control ----
    input  logic                       clear,
    input  logic                       cfg_monitor_enable,
    input  logic                       cfg_error_enable,
    input  logic                       cfg_timeout_enable,
    input  logic                       cfg_compl_enable,
    input  logic [15:0]                cfg_timeout_cycles,  // microseconds at full width, 0 = never
    input  logic [3:0]                 cfg_freq_sel,
    input  monitor_common_pkg::monbus_timestamp_t i_mon_time,

    // ---- Monitor bus ----
    output logic                                  monbus_valid,
    input  logic                                  monbus_ready,
    output monitor_common_pkg::monitor_packet_t   monbus_packet,
    output monitor_common_pkg::monbus_timestamp_t monbus_timestamp,

    // ---- Status ----
    output logic [7:0]                            active_transactions,
    output logic [15:0]                           error_count,
    output logic [31:0]                           transaction_count,
    output logic [15:0]                           dropped_count
);

    // ------------------------------------------------------------------------
    // The core, passed through untouched (no monitor gating on any handshake)
    // ------------------------------------------------------------------------
    axi4ace_snoop_slave #(
        .SKID_DEPTH_AC (SKID_DEPTH_AC),
        .SKID_DEPTH_CR (SKID_DEPTH_CR),
        .SKID_DEPTH_CD (SKID_DEPTH_CD),
        .ADDR_WIDTH    (ADDR_WIDTH),
        .DATA_WIDTH    (DATA_WIDTH),
        .AW            (AW),
        .DW            (DW),
        .ACSize        (ACSize),
        .CRSize        (CRSize),
        .CDSize        (CDSize)
    ) u_core (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .m_axi_acaddr  (m_axi_acaddr),
        .m_axi_acsnoop (m_axi_acsnoop),
        .m_axi_acprot  (m_axi_acprot),
        .m_axi_acvalid (m_axi_acvalid),
        .m_axi_acready (m_axi_acready),
        .m_axi_crresp  (m_axi_crresp),
        .m_axi_crvalid (m_axi_crvalid),
        .m_axi_crready (m_axi_crready),
        .m_axi_cddata  (m_axi_cddata),
        .m_axi_cdlast  (m_axi_cdlast),
        .m_axi_cdvalid (m_axi_cdvalid),
        .m_axi_cdready (m_axi_cdready),
        .fub_acaddr    (fub_acaddr),
        .fub_acsnoop   (fub_acsnoop),
        .fub_acprot    (fub_acprot),
        .fub_acvalid   (fub_acvalid),
        .fub_acready   (fub_acready),
        .fub_crresp    (fub_crresp),
        .fub_crvalid   (fub_crvalid),
        .fub_crready   (fub_crready),
        .fub_cddata    (fub_cddata),
        .fub_cdlast    (fub_cdlast),
        .fub_cdvalid   (fub_cdvalid),
        .fub_cdready   (fub_cdready),
        .busy          (busy)
    );

    // ------------------------------------------------------------------------
    // Monitor taps. cfg_monitor_enable gates every tap and holds the table
    // clear; cfg_timeout_cycles is MICROSECONDS at full width, 0 = never.
    // ------------------------------------------------------------------------
    logic        w_mon_ac_valid;
    logic        w_mon_cr_valid;
    logic        w_mon_cd_valid;
    logic [15:0] w_timeout_cnt;

    assign w_mon_ac_valid = m_axi_acvalid & cfg_monitor_enable;
    assign w_mon_cr_valid = m_axi_crvalid & cfg_monitor_enable;
    assign w_mon_cd_valid = m_axi_cdvalid & cfg_monitor_enable;
    assign w_timeout_cnt  = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF
                                                        : cfg_timeout_cycles;

    if (USE_MONITOR) begin : gen_monitor_lite
        axi4ace_snoop_monitor_lite #(
            .UNIT_ID          (UNIT_ID),
            .AGENT_ID         (AGENT_ID),
            .MAX_SNOOPS       (MAX_TRANSACTIONS),
            .OUT_DEPTH        (OUT_DEPTH),
            .ACLK_MHZ         (ACLK_MHZ),
            .CFI_MIN_FREQ_MHZ (CFI_MIN_FREQ_MHZ),
            .CFI_MAX_FREQ_MHZ (CFI_MAX_FREQ_MHZ),
            .ADDR_WIDTH       (AW),
            .DATA_WIDTH       (DW)
        ) axi4ace_snoop_monitor_lite_inst (
            .aclk               (aclk),
            .aresetn            (aresetn),
            .clear              (clear | ~cfg_monitor_enable),
            .i_mon_time         (i_mon_time),
            .cfg_monitor_enable (cfg_monitor_enable),
            .cfg_error_enable   (cfg_error_enable),
            .cfg_compl_enable   (cfg_compl_enable),
            .cfg_timeout_enable (cfg_timeout_enable),
            .cfg_timeout_cycles (w_timeout_cnt),
            .cfg_freq_sel       (cfg_freq_sel),
            .monbus_valid       (monbus_valid),
            .monbus_ready       (monbus_ready),
            .monbus_packet      (monbus_packet),
            .monbus_timestamp   (monbus_timestamp),
            .active_transactions(active_transactions),
            .error_count        (error_count),
            .transaction_count  (transaction_count),
            .dropped_count      (dropped_count),
            .ac_addr            (m_axi_acaddr),
            .ac_snoop           (m_axi_acsnoop),
            .ac_valid           (w_mon_ac_valid),
            .ac_ready           (m_axi_acready),
            .cr_resp            (m_axi_crresp),
            .cr_valid           (w_mon_cr_valid),
            .cr_ready           (m_axi_crready),
            .cd_last            (m_axi_cdlast),
            .cd_valid           (w_mon_cd_valid),
            .cd_ready           (m_axi_cdready)
        );
    end else begin : gen_no_monitor
        assign monbus_valid        = 1'b0;
        assign monbus_packet       = '0;
        assign monbus_timestamp    = '0;
        assign active_transactions = 8'h0;
        assign error_count         = 16'h0;
        assign transaction_count   = 32'h0;
        assign dropped_count       = 16'h0;
    end

endmodule : axi4ace_snoop_slave_monlite
