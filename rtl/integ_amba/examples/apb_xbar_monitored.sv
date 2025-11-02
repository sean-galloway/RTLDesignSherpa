// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_xbar_monitored
// Purpose: Apb Xbar Monitored module
//
// Documentation: PRD.md
// Subsystem: integ_amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module apb_xbar_monitored #(
    parameter int NUM_MASTERS = 3,
    parameter int NUM_SLAVES = 4,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH/8,

    // Monitor parameters
    parameter int MAX_TRANSACTIONS = 8,  // APB is simple, 8 is sufficient
    parameter int UNIT_ID = 0,           // Crossbar unit ID

    // Agent IDs for each monitor
    parameter logic [7:0] AGENT_ID_M0 = 8'h10,  // Master 0
    parameter logic [7:0] AGENT_ID_M1 = 8'h11,  // Master 1
    parameter logic [7:0] AGENT_ID_M2 = 8'h12,  // Master 2
    parameter logic [7:0] AGENT_ID_S0 = 8'h40,  // Slave 0
    parameter logic [7:0] AGENT_ID_S1 = 8'h41,  // Slave 1
    parameter logic [7:0] AGENT_ID_S2 = 8'h42,  // Slave 2
    parameter logic [7:0] AGENT_ID_S3 = 8'h43   // Slave 3
) (
    input  logic pclk,
    input  logic presetn,

    // =============================================================================
    // Master Interfaces (3 masters)
    // =============================================================================

    // Master 0
    input  logic                  m0_apb_psel,
    input  logic                  m0_apb_penable,
    input  logic                  m0_apb_pwrite,
    input  logic [2:0]            m0_apb_pprot,
    input  logic [ADDR_WIDTH-1:0] m0_apb_paddr,
    input  logic [DATA_WIDTH-1:0] m0_apb_pwdata,
    input  logic [STRB_WIDTH-1:0] m0_apb_pstrb,
    output logic                  m0_apb_pready,
    output logic [DATA_WIDTH-1:0] m0_apb_prdata,
    output logic                  m0_apb_pslverr,

    // Master 1
    input  logic                  m1_apb_psel,
    input  logic                  m1_apb_penable,
    input  logic                  m1_apb_pwrite,
    input  logic [2:0]            m1_apb_pprot,
    input  logic [ADDR_WIDTH-1:0] m1_apb_paddr,
    input  logic [DATA_WIDTH-1:0] m1_apb_pwdata,
    input  logic [STRB_WIDTH-1:0] m1_apb_pstrb,
    output logic                  m1_apb_pready,
    output logic [DATA_WIDTH-1:0] m1_apb_prdata,
    output logic                  m1_apb_pslverr,

    // Master 2
    input  logic                  m2_apb_psel,
    input  logic                  m2_apb_penable,
    input  logic                  m2_apb_pwrite,
    input  logic [2:0]            m2_apb_pprot,
    input  logic [ADDR_WIDTH-1:0] m2_apb_paddr,
    input  logic [DATA_WIDTH-1:0] m2_apb_pwdata,
    input  logic [STRB_WIDTH-1:0] m2_apb_pstrb,
    output logic                  m2_apb_pready,
    output logic [DATA_WIDTH-1:0] m2_apb_prdata,
    output logic                  m2_apb_pslverr,

    // =============================================================================
    // Slave Interfaces (4 slaves)
    // =============================================================================

    // Slave 0 (Memory-mapped peripheral 0x0000-0x0FFF)
    output logic                  s0_apb_psel,
    output logic                  s0_apb_penable,
    output logic                  s0_apb_pwrite,
    output logic [2:0]            s0_apb_pprot,
    output logic [ADDR_WIDTH-1:0] s0_apb_paddr,
    output logic [DATA_WIDTH-1:0] s0_apb_pwdata,
    output logic [STRB_WIDTH-1:0] s0_apb_pstrb,
    input  logic                  s0_apb_pready,
    input  logic [DATA_WIDTH-1:0] s0_apb_prdata,
    input  logic                  s0_apb_pslverr,

    // Slave 1 (Memory-mapped peripheral 0x1000-0x1FFF)
    output logic                  s1_apb_psel,
    output logic                  s1_apb_penable,
    output logic                  s1_apb_pwrite,
    output logic [2:0]            s1_apb_pprot,
    output logic [ADDR_WIDTH-1:0] s1_apb_paddr,
    output logic [DATA_WIDTH-1:0] s1_apb_pwdata,
    output logic [STRB_WIDTH-1:0] s1_apb_pstrb,
    input  logic                  s1_apb_pready,
    input  logic [DATA_WIDTH-1:0] s1_apb_prdata,
    input  logic                  s1_apb_pslverr,

    // Slave 2 (Memory-mapped peripheral 0x2000-0x2FFF)
    output logic                  s2_apb_psel,
    output logic                  s2_apb_penable,
    output logic                  s2_apb_pwrite,
    output logic [2:0]            s2_apb_pprot,
    output logic [ADDR_WIDTH-1:0] s2_apb_paddr,
    output logic [DATA_WIDTH-1:0] s2_apb_pwdata,
    output logic [STRB_WIDTH-1:0] s2_apb_pstrb,
    input  logic                  s2_apb_pready,
    input  logic [DATA_WIDTH-1:0] s2_apb_prdata,
    input  logic                  s2_apb_pslverr,

    // Slave 3 (Memory-mapped peripheral 0x3000-0x3FFF)
    output logic                  s3_apb_psel,
    output logic                  s3_apb_penable,
    output logic                  s3_apb_pwrite,
    output logic [2:0]            s3_apb_pprot,
    output logic [ADDR_WIDTH-1:0] s3_apb_paddr,
    output logic [DATA_WIDTH-1:0] s3_apb_pwdata,
    output logic [STRB_WIDTH-1:0] s3_apb_pstrb,
    input  logic                  s3_apb_pready,
    input  logic [DATA_WIDTH-1:0] s3_apb_prdata,
    input  logic                  s3_apb_pslverr,

    // =============================================================================
    // Aggregated Monitor Bus Output
    // =============================================================================
    output logic        monbus_valid,
    input  logic        monbus_ready,
    output logic [63:0] monbus_data,

    // =============================================================================
    // Configuration Inputs
    // =============================================================================
    input logic cfg_error_enable,    // Enable error packet reporting
    input logic cfg_compl_enable,    // Enable completion packet reporting
    input logic cfg_timeout_enable,  // Enable timeout detection
    input logic cfg_perf_enable      // Enable performance metrics
);

    // =============================================================================
    // Internal APB Crossbar Signals (without monitors)
    // =============================================================================

    // Master-side internal (pre-monitor)
    logic [NUM_MASTERS-1:0]                  xbar_m_psel;
    logic [NUM_MASTERS-1:0]                  xbar_m_penable;
    logic [NUM_MASTERS-1:0]                  xbar_m_pwrite;
    logic [NUM_MASTERS-1:0][2:0]             xbar_m_pprot;
    logic [NUM_MASTERS-1:0][ADDR_WIDTH-1:0]  xbar_m_paddr;
    logic [NUM_MASTERS-1:0][DATA_WIDTH-1:0]  xbar_m_pwdata;
    logic [NUM_MASTERS-1:0][STRB_WIDTH-1:0]  xbar_m_pstrb;
    logic [NUM_MASTERS-1:0]                  xbar_m_pready;
    logic [NUM_MASTERS-1:0][DATA_WIDTH-1:0]  xbar_m_prdata;
    logic [NUM_MASTERS-1:0]                  xbar_m_pslverr;

    // Slave-side internal (pre-monitor)
    logic [NUM_SLAVES-1:0]                  xbar_s_psel;
    logic [NUM_SLAVES-1:0]                  xbar_s_penable;
    logic [NUM_SLAVES-1:0]                  xbar_s_pwrite;
    logic [NUM_SLAVES-1:0][2:0]             xbar_s_pprot;
    logic [NUM_SLAVES-1:0][ADDR_WIDTH-1:0]  xbar_s_paddr;
    logic [NUM_SLAVES-1:0][DATA_WIDTH-1:0]  xbar_s_pwdata;
    logic [NUM_SLAVES-1:0][STRB_WIDTH-1:0]  xbar_s_pstrb;
    logic [NUM_SLAVES-1:0]                  xbar_s_pready;
    logic [NUM_SLAVES-1:0][DATA_WIDTH-1:0]  xbar_s_prdata;
    logic [NUM_SLAVES-1:0]                  xbar_s_pslverr;

    // Connect external master interfaces to internal crossbar inputs
    assign xbar_m_psel    = {m2_apb_psel, m1_apb_psel, m0_apb_psel};
    assign xbar_m_penable = {m2_apb_penable, m1_apb_penable, m0_apb_penable};
    assign xbar_m_pwrite  = {m2_apb_pwrite, m1_apb_pwrite, m0_apb_pwrite};
    assign xbar_m_pprot   = {m2_apb_pprot, m1_apb_pprot, m0_apb_pprot};
    assign xbar_m_paddr   = {m2_apb_paddr, m1_apb_paddr, m0_apb_paddr};
    assign xbar_m_pwdata  = {m2_apb_pwdata, m1_apb_pwdata, m0_apb_pwdata};
    assign xbar_m_pstrb   = {m2_apb_pstrb, m1_apb_pstrb, m0_apb_pstrb};

    assign {m2_apb_pready, m1_apb_pready, m0_apb_pready}   = xbar_m_pready;
    assign {m2_apb_prdata, m1_apb_prdata, m0_apb_prdata}   = xbar_m_prdata;
    assign {m2_apb_pslverr, m1_apb_pslverr, m0_apb_pslverr} = xbar_m_pslverr;

    // Connect internal crossbar outputs to external slave interfaces
    assign {s3_apb_psel, s2_apb_psel, s1_apb_psel, s0_apb_psel}       = xbar_s_psel;
    assign {s3_apb_penable, s2_apb_penable, s1_apb_penable, s0_apb_penable} = xbar_s_penable;
    assign {s3_apb_pwrite, s2_apb_pwrite, s1_apb_pwrite, s0_apb_pwrite}     = xbar_s_pwrite;
    assign {s3_apb_pprot, s2_apb_pprot, s1_apb_pprot, s0_apb_pprot}   = xbar_s_pprot;
    assign {s3_apb_paddr, s2_apb_paddr, s1_apb_paddr, s0_apb_paddr}   = xbar_s_paddr;
    assign {s3_apb_pwdata, s2_apb_pwdata, s1_apb_pwdata, s0_apb_pwdata} = xbar_s_pwdata;
    assign {s3_apb_pstrb, s2_apb_pstrb, s1_apb_pstrb, s0_apb_pstrb}   = xbar_s_pstrb;

    assign xbar_s_pready  = {s3_apb_pready, s2_apb_pready, s1_apb_pready, s0_apb_pready};
    assign xbar_s_prdata  = {s3_apb_prdata, s2_apb_prdata, s1_apb_prdata, s0_apb_prdata};
    assign xbar_s_pslverr = {s3_apb_pslverr, s2_apb_pslverr, s1_apb_pslverr, s0_apb_pslverr};

    // =============================================================================
    // APB Crossbar Instance (Thin Variant - Tested and Working)
    // =============================================================================

    apb_xbar_thin #(
        .M(NUM_MASTERS),
        .S(NUM_SLAVES),
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_apb_xbar (
        .pclk        (pclk),
        .presetn     (presetn),

        // Address map configuration
        .SLAVE_ENABLE    ({NUM_SLAVES{1'b1}}),                       // All slaves enabled
        .SLAVE_ADDR_BASE ({32'h3000, 32'h2000, 32'h1000, 32'h0000}), // 4KB regions
        .SLAVE_ADDR_LIMIT({32'h3FFF, 32'h2FFF, 32'h1FFF, 32'h0FFF}),
        .THRESHOLDS      ({NUM_SLAVES{4'h4}}),                       // Threshold = 4 cycles

        // Master interfaces
        .m_apb_psel    (xbar_m_psel),
        .m_apb_penable (xbar_m_penable),
        .m_apb_pwrite  (xbar_m_pwrite),
        .m_apb_pprot   (xbar_m_pprot),
        .m_apb_paddr   (xbar_m_paddr),
        .m_apb_pwdata  (xbar_m_pwdata),
        .m_apb_pstrb   (xbar_m_pstrb),
        .m_apb_pready  (xbar_m_pready),
        .m_apb_prdata  (xbar_m_prdata),
        .m_apb_pslverr (xbar_m_pslverr),

        // Slave interfaces
        .s_apb_psel    (xbar_s_psel),
        .s_apb_penable (xbar_s_penable),
        .s_apb_pwrite  (xbar_s_pwrite),
        .s_apb_pprot   (xbar_s_pprot),
        .s_apb_paddr   (xbar_s_paddr),
        .s_apb_pwdata  (xbar_s_pwdata),
        .s_apb_pstrb   (xbar_s_pstrb),
        .s_apb_pready  (xbar_s_pready),
        .s_apb_prdata  (xbar_s_prdata),
        .s_apb_pslverr (xbar_s_pslverr)
    );

    // =============================================================================
    // Monitor Bus Signals (7 monitors total)
    // =============================================================================
    localparam int NUM_MONITORS = NUM_MASTERS + NUM_SLAVES;  // 3 + 4 = 7

    logic [NUM_MONITORS-1:0]        mon_valid;
    logic [NUM_MONITORS-1:0]        mon_ready;
    logic [NUM_MONITORS-1:0][63:0]  mon_data;

    // =============================================================================
    // Master Monitors (3 monitors: M0, M1, M2)
    // =============================================================================

    genvar m;
    generate
        for (m = 0; m < NUM_MASTERS; m++) begin : gen_master_monitors
            apb_monitor #(
                .ADDR_WIDTH(ADDR_WIDTH),
                .DATA_WIDTH(DATA_WIDTH),
                .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
                .UNIT_ID(UNIT_ID),
                .AGENT_ID(AGENT_ID_M0 + m)  // Sequential agent IDs: 0x10, 0x11, 0x12
            ) u_master_mon (
                .pclk              (pclk),
                .presetn           (presetn),

                // APB signals from external master interface
                .psel              (xbar_m_psel[m]),
                .penable           (xbar_m_penable[m]),
                .pwrite            (xbar_m_pwrite[m]),
                .paddr             (xbar_m_paddr[m]),
                .pwdata            (xbar_m_pwdata[m]),
                .pready            (xbar_m_pready[m]),
                .prdata            (xbar_m_prdata[m]),
                .pslverr           (xbar_m_pslverr[m]),

                // Monitor bus output
                .monbus_pkt_valid  (mon_valid[m]),
                .monbus_pkt_ready  (mon_ready[m]),
                .monbus_pkt_data   (mon_data[m]),

                // Configuration
                .cfg_error_enable   (cfg_error_enable),
                .cfg_compl_enable   (cfg_compl_enable),
                .cfg_timeout_enable (cfg_timeout_enable),
                .cfg_perf_enable    (cfg_perf_enable)
            );
        end
    endgenerate

    // =============================================================================
    // Slave Monitors (4 monitors: S0, S1, S2, S3)
    // =============================================================================

    genvar s;
    generate
        for (s = 0; s < NUM_SLAVES; s++) begin : gen_slave_monitors
            apb_monitor #(
                .ADDR_WIDTH(ADDR_WIDTH),
                .DATA_WIDTH(DATA_WIDTH),
                .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
                .UNIT_ID(UNIT_ID),
                .AGENT_ID(AGENT_ID_S0 + s)  // Sequential agent IDs: 0x40, 0x41, 0x42, 0x43
            ) u_slave_mon (
                .pclk              (pclk),
                .presetn           (presetn),

                // APB signals to external slave interface
                .psel              (xbar_s_psel[s]),
                .penable           (xbar_s_penable[s]),
                .pwrite            (xbar_s_pwrite[s]),
                .paddr             (xbar_s_paddr[s]),
                .pwdata            (xbar_s_pwdata[s]),
                .pready            (xbar_s_pready[s]),
                .prdata            (xbar_s_prdata[s]),
                .pslverr           (xbar_s_pslverr[s]),

                // Monitor bus output
                .monbus_pkt_valid  (mon_valid[NUM_MASTERS + s]),
                .monbus_pkt_ready  (mon_ready[NUM_MASTERS + s]),
                .monbus_pkt_data   (mon_data[NUM_MASTERS + s]),

                // Configuration
                .cfg_error_enable   (cfg_error_enable),
                .cfg_compl_enable   (cfg_compl_enable),
                .cfg_timeout_enable (cfg_timeout_enable),
                .cfg_perf_enable    (cfg_perf_enable)
            );
        end
    endgenerate

    // =============================================================================
    // Monitor Bus Arbiter (Round-Robin)
    // =============================================================================
    // Aggregates 7 monitor packet streams into single output

    arbiter_round_robin #(
        .N(NUM_MONITORS),
        .REG_OUTPUT(1)           // Register output for timing
    ) u_mon_arbiter (
        .i_clk      (pclk),
        .i_rst_n    (presetn),
        .i_request  (mon_valid),
        .o_grant    (mon_ready),
        .o_valid    (monbus_valid)
    );

    // Data muxing based on grant
    logic [$clog2(NUM_MONITORS)-1:0] grant_id;
    always_comb begin
        grant_id = '0;
        for (int i = 0; i < NUM_MONITORS; i++) begin
            if (mon_ready[i]) grant_id = i[$clog2(NUM_MONITORS)-1:0];
        end
    end
    assign monbus_data = mon_data[grant_id];

endmodule : apb_xbar_monitored
