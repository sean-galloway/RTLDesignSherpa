// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4ace_snoop_master
// Purpose: ACE snoop-channel initiator transport (CCU / coherency manager side).
//
// Documentation: docs/markdown/rtl-amba/ace/axi4ace_snoop_master.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-10-05

`timescale 1ns / 1ps

module axi4ace_snoop_master
#(
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

    // Slave AXI Interface (Input Side) -- upstream CCU logic
    // Snoop address channel (AC)
    input  logic [AW-1:0]              fub_acaddr,
    input  logic [3:0]                 fub_acsnoop,
    input  logic [2:0]                 fub_acprot,
    input  logic                       fub_acvalid,
    output logic                       fub_acready,

    // Snoop response channel (CR)
    output logic [4:0]                 fub_crresp,
    output logic                       fub_crvalid,
    input  logic                       fub_crready,

    // Snoop data channel (CD)
    output logic [DW-1:0]              fub_cddata,
    output logic                       fub_cdlast,
    output logic                       fub_cdvalid,
    input  logic                       fub_cdready,

    // Master AXI Interface (Output Side) -- peer cache responder
    // Snoop address channel (AC)
    output logic [AW-1:0]              m_axi_acaddr,
    output logic [3:0]                 m_axi_acsnoop,
    output logic [2:0]                 m_axi_acprot,
    output logic                       m_axi_acvalid,
    input  logic                       m_axi_acready,

    // Snoop response channel (CR)
    input  logic [4:0]                 m_axi_crresp,
    input  logic                       m_axi_crvalid,
    output logic                       m_axi_crready,

    // Snoop data channel (CD)
    input  logic [DW-1:0]              m_axi_cddata,
    input  logic                       m_axi_cdlast,
    input  logic                       m_axi_cdvalid,
    output logic                       m_axi_cdready,

    // Status outputs for clock gating
    output logic                       busy
);

    // SKID buffer connections
    logic [3:0]         int_ac_count;
    logic [ACSize-1:0]  int_ac_pkt;
    logic               int_skid_acvalid;
    logic               int_skid_acready;

    logic [3:0]         int_cr_count;
    logic [CRSize-1:0]  int_cr_pkt;
    logic               int_skid_crvalid;
    logic               int_skid_crready;

    logic [3:0]         int_cd_count;
    logic [CDSize-1:0]  int_cd_pkt;
    logic               int_skid_cdvalid;
    logic               int_skid_cdready;

    // Busy signal indicates activity in the buffers
    assign busy = (int_ac_count > 0) || (int_cr_count > 0) || (int_cd_count > 0) ||
                    fub_acvalid || m_axi_crvalid || m_axi_cdvalid;

    // Instantiate AC Skid Buffer (CCU -> peer cache)
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AC),
        .DATA_WIDTH(ACSize)
    ) ac_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_acvalid),
        .wr_ready               (fub_acready),
        .wr_data                ({fub_acaddr, fub_acsnoop, fub_acprot}),
        .rd_valid               (int_skid_acvalid),
        .rd_ready               (int_skid_acready),
        .rd_count               (int_ac_count),
        .rd_data                (int_ac_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack AC signals from SKID buffer
    assign {m_axi_acaddr, m_axi_acsnoop, m_axi_acprot} = int_ac_pkt;
    assign m_axi_acvalid = int_skid_acvalid;
    assign int_skid_acready = m_axi_acready;

    // Instantiate CR Skid Buffer (peer cache -> CCU)
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_CR),
        .DATA_WIDTH(CRSize)
    ) cr_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (m_axi_crvalid),
        .wr_ready               (m_axi_crready),
        .wr_data                ({m_axi_crresp}),
        .rd_valid               (int_skid_crvalid),
        .rd_ready               (int_skid_crready),
        .rd_count               (int_cr_count),
        .rd_data                (int_cr_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign fub_crresp  = int_cr_pkt;
    assign fub_crvalid = int_skid_crvalid;
    assign int_skid_crready = fub_crready;

    // Instantiate CD Skid Buffer (peer cache -> CCU)
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_CD),
        .DATA_WIDTH(CDSize)
    ) cd_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (m_axi_cdvalid),
        .wr_ready               (m_axi_cdready),
        .wr_data                ({m_axi_cddata, m_axi_cdlast}),
        .rd_valid               (int_skid_cdvalid),
        .rd_ready               (int_skid_cdready),
        .rd_count               (int_cd_count),
        .rd_data                (int_cd_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign {fub_cddata, fub_cdlast} = int_cd_pkt;
    assign fub_cdvalid = int_skid_cdvalid;
    assign int_skid_cdready = fub_cdready;

endmodule : axi4ace_snoop_master
