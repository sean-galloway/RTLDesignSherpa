// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: tb_axi4ace_snoop_monitor_lite
// Purpose: Test fixture for axi4ace_snoop_monitor_lite (amba/monitor-lite).
//          The monitor only taps handshakes and a few fields; the full ACE
//          snoop signal set is exposed so both the snoop-master BFM (issue)
//          and the snoop-slave BFM (responder) can bind with prefix='m_axi_'.
//          The fixture itself contains no DUT logic beyond wiring.
`timescale 1ns / 1ps
module tb_axi4ace_snoop_monitor_lite
    import monitor_common_pkg::*;
#(
    parameter logic [7:0]  UNIT_ID          = 8'h01,
    parameter logic [15:0] AGENT_ID         = 16'h000A,
    parameter int          MAX_SNOOPS       = 8,
    parameter int          OUT_DEPTH        = 4,
    parameter int          ACLK_MHZ         = 100,
    parameter int          ADDR_WIDTH       = 32,
    parameter int          DATA_WIDTH       = 32,
    // Short params (do not override)
    parameter int          AW               = ADDR_WIDTH,
    parameter int          DW               = DATA_WIDTH
) (
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic                  clear,
    input  monbus_timestamp_t     i_mon_time,

    // Configuration
    input  logic                  cfg_monitor_enable,
    input  logic                  cfg_error_enable,
    input  logic                  cfg_compl_enable,
    input  logic                  cfg_timeout_enable,
    input  logic [15:0]           cfg_timeout_cycles,
    input  logic [3:0]            cfg_freq_sel,

    // Monitor bus
    output logic                  monbus_valid,
    input  logic                  monbus_ready,
    output monitor_packet_t       monbus_packet,
    output monbus_timestamp_t     monbus_timestamp,

    // Status
    output logic [7:0]            active_transactions,
    output logic [15:0]           error_count,
    output logic [31:0]           transaction_count,
    output logic [15:0]           dropped_count,

    // Shared ACE snoop-channel wires (both snoop BFMs bind here)
    input  logic [AW-1:0]         m_axi_acaddr,
    input  logic [3:0]            m_axi_acsnoop,
    input  logic [2:0]            m_axi_acprot,
    input  logic                  m_axi_acvalid,
    input  logic                  m_axi_acready,
    input  logic [4:0]            m_axi_crresp,
    input  logic                  m_axi_crvalid,
    input  logic                  m_axi_crready,
    input  logic [DW-1:0]         m_axi_cddata,
    input  logic                  m_axi_cdlast,
    input  logic                  m_axi_cdvalid,
    input  logic                  m_axi_cdready
);

    axi4ace_snoop_monitor_lite #(
        .UNIT_ID          (UNIT_ID),
        .AGENT_ID         (AGENT_ID),
        .MAX_SNOOPS       (MAX_SNOOPS),
        .OUT_DEPTH        (OUT_DEPTH),
        .ACLK_MHZ         (ACLK_MHZ),
        .CFI_MIN_FREQ_MHZ (ACLK_MHZ),
        .CFI_MAX_FREQ_MHZ (ACLK_MHZ),
        .ADDR_WIDTH       (ADDR_WIDTH),
        .DATA_WIDTH       (DATA_WIDTH)
    ) u_mon (
        .aclk                  (aclk),
        .aresetn               (aresetn),
        .clear                 (clear),
        .i_mon_time            (i_mon_time),
        .cfg_monitor_enable    (cfg_monitor_enable),
        .cfg_error_enable      (cfg_error_enable),
        .cfg_compl_enable      (cfg_compl_enable),
        .cfg_timeout_enable    (cfg_timeout_enable),
        .cfg_timeout_cycles    (cfg_timeout_cycles),
        .cfg_freq_sel          (cfg_freq_sel),
        .monbus_valid          (monbus_valid),
        .monbus_ready          (monbus_ready),
        .monbus_packet         (monbus_packet),
        .monbus_timestamp      (monbus_timestamp),
        .active_transactions   (active_transactions),
        .error_count           (error_count),
        .transaction_count     (transaction_count),
        .dropped_count         (dropped_count),
        .ac_addr               (m_axi_acaddr),
        .ac_snoop              (m_axi_acsnoop),
        .ac_valid              (m_axi_acvalid),
        .ac_ready              (m_axi_acready),
        .cr_resp               (m_axi_crresp),
        .cr_valid              (m_axi_crvalid),
        .cr_ready              (m_axi_crready),
        .cd_last               (m_axi_cdlast),
        .cd_valid              (m_axi_cdvalid),
        .cd_ready              (m_axi_cdready)
    );

endmodule : tb_axi4ace_snoop_monitor_lite
