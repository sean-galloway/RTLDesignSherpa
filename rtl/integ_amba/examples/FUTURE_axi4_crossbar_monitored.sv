// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_crossbar_monitored
// Purpose: Future Axi4 Crossbar Monitored module
//
// Documentation: PRD.md
// Subsystem: integ_amba
//
// Author: sean galloway
// Created: 2025-10-18

module axi4_crossbar_monitored #(
    // AXI Parameters
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,

    // Monitor Parameters
    parameter int MAX_TRANSACTIONS = 16,
    parameter int UNIT_ID = 1,

    // Monitor Agent IDs
    parameter int AGENT_ID_M0_RD = 8'h10,  // Master 0 read
    parameter int AGENT_ID_M0_WR = 8'h11,  // Master 0 write
    parameter int AGENT_ID_M1_RD = 8'h12,  // Master 1 read
    parameter int AGENT_ID_M1_WR = 8'h13,  // Master 1 write
    parameter int AGENT_ID_S0_RD = 8'h20,  // Slave 0 read
    parameter int AGENT_ID_S0_WR = 8'h21,  // Slave 0 write
    parameter int AGENT_ID_S1_RD = 8'h22,  // Slave 1 read
    parameter int AGENT_ID_S1_WR = 8'h23,  // Slave 1 write
    parameter int AGENT_ID_S2_RD = 8'h24,  // Slave 2 read
    parameter int AGENT_ID_S2_WR = 8'h25   // Slave 2 write
) (
    // Global signals
    input  logic aclk,
    input  logic aresetn,

    // Master 0 Interface (e.g., CPU)
    input  logic [AXI_ID_WIDTH-1:0]    m0_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]  m0_axi_awaddr,
    input  logic [7:0]                  m0_axi_awlen,
    input  logic [2:0]                  m0_axi_awsize,
    input  logic [1:0]                  m0_axi_awburst,
    input  logic                        m0_axi_awvalid,
    output logic                        m0_axi_awready,
    input  logic [AXI_DATA_WIDTH-1:0]  m0_axi_wdata,
    input  logic [AXI_DATA_WIDTH/8-1:0] m0_axi_wstrb,
    input  logic                        m0_axi_wlast,
    input  logic                        m0_axi_wvalid,
    output logic                        m0_axi_wready,
    output logic [AXI_ID_WIDTH-1:0]    m0_axi_bid,
    output logic [1:0]                  m0_axi_bresp,
    output logic                        m0_axi_bvalid,
    input  logic                        m0_axi_bready,
    input  logic [AXI_ID_WIDTH-1:0]    m0_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]  m0_axi_araddr,
    input  logic [7:0]                  m0_axi_arlen,
    input  logic [2:0]                  m0_axi_arsize,
    input  logic [1:0]                  m0_axi_arburst,
    input  logic                        m0_axi_arvalid,
    output logic                        m0_axi_arready,
    output logic [AXI_ID_WIDTH-1:0]    m0_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]  m0_axi_rdata,
    output logic [1:0]                  m0_axi_rresp,
    output logic                        m0_axi_rlast,
    output logic                        m0_axi_rvalid,
    input  logic                        m0_axi_rready,

    // Master 1 Interface (e.g., DMA)
    input  logic [AXI_ID_WIDTH-1:0]    m1_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]  m1_axi_awaddr,
    input  logic [7:0]                  m1_axi_awlen,
    input  logic [2:0]                  m1_axi_awsize,
    input  logic [1:0]                  m1_axi_awburst,
    input  logic                        m1_axi_awvalid,
    output logic                        m1_axi_awready,
    input  logic [AXI_DATA_WIDTH-1:0]  m1_axi_wdata,
    input  logic [AXI_DATA_WIDTH/8-1:0] m1_axi_wstrb,
    input  logic                        m1_axi_wlast,
    input  logic                        m1_axi_wvalid,
    output logic                        m1_axi_wready,
    output logic [AXI_ID_WIDTH-1:0]    m1_axi_bid,
    output logic [1:0]                  m1_axi_bresp,
    output logic                        m1_axi_bvalid,
    input  logic                        m1_axi_bready,
    input  logic [AXI_ID_WIDTH-1:0]    m1_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]  m1_axi_araddr,
    input  logic [7:0]                  m1_axi_arlen,
    input  logic [2:0]                  m1_axi_arsize,
    input  logic [1:0]                  m1_axi_arburst,
    input  logic                        m1_axi_arvalid,
    output logic                        m1_axi_arready,
    output logic [AXI_ID_WIDTH-1:0]    m1_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]  m1_axi_rdata,
    output logic [1:0]                  m1_axi_rresp,
    output logic                        m1_axi_rlast,
    output logic                        m1_axi_rvalid,
    input  logic                        m1_axi_rready,

    // Slave 0 Interface (Memory)
    output logic [AXI_ID_WIDTH-1:0]    s0_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]  s0_axi_awaddr,
    output logic [7:0]                  s0_axi_awlen,
    output logic [2:0]                  s0_axi_awsize,
    output logic [1:0]                  s0_axi_awburst,
    output logic                        s0_axi_awvalid,
    input  logic                        s0_axi_awready,
    output logic [AXI_DATA_WIDTH-1:0]  s0_axi_wdata,
    output logic [AXI_DATA_WIDTH/8-1:0] s0_axi_wstrb,
    output logic                        s0_axi_wlast,
    output logic                        s0_axi_wvalid,
    input  logic                        s0_axi_wready,
    input  logic [AXI_ID_WIDTH-1:0]    s0_axi_bid,
    input  logic [1:0]                  s0_axi_bresp,
    input  logic                        s0_axi_bvalid,
    output logic                        s0_axi_bready,
    output logic [AXI_ID_WIDTH-1:0]    s0_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]  s0_axi_araddr,
    output logic [7:0]                  s0_axi_arlen,
    output logic [2:0]                  s0_axi_arsize,
    output logic [1:0]                  s0_axi_arburst,
    output logic                        s0_axi_arvalid,
    input  logic                        s0_axi_arready,
    input  logic [AXI_ID_WIDTH-1:0]    s0_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0]  s0_axi_rdata,
    input  logic [1:0]                  s0_axi_rresp,
    input  logic                        s0_axi_rlast,
    input  logic                        s0_axi_rvalid,
    output logic                        s0_axi_rready,

    // Slave 1 Interface (Peripherals)
    output logic [AXI_ID_WIDTH-1:0]    s1_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]  s1_axi_awaddr,
    output logic [7:0]                  s1_axi_awlen,
    output logic [2:0]                  s1_axi_awsize,
    output logic [1:0]                  s1_axi_awburst,
    output logic                        s1_axi_awvalid,
    input  logic                        s1_axi_awready,
    output logic [AXI_DATA_WIDTH-1:0]  s1_axi_wdata,
    output logic [AXI_DATA_WIDTH/8-1:0] s1_axi_wstrb,
    output logic                        s1_axi_wlast,
    output logic                        s1_axi_wvalid,
    input  logic                        s1_axi_wready,
    input  logic [AXI_ID_WIDTH-1:0]    s1_axi_bid,
    input  logic [1:0]                  s1_axi_bresp,
    input  logic                        s1_axi_bvalid,
    output logic                        s1_axi_bready,
    output logic [AXI_ID_WIDTH-1:0]    s1_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]  s1_axi_araddr,
    output logic [7:0]                  s1_axi_arlen,
    output logic [2:0]                  s1_axi_arsize,
    output logic [1:0]                  s1_axi_arburst,
    output logic                        s1_axi_arvalid,
    input  logic                        s1_axi_arready,
    input  logic [AXI_ID_WIDTH-1:0]    s1_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0]  s1_axi_rdata,
    input  logic [1:0]                  s1_axi_rresp,
    input  logic                        s1_axi_rlast,
    input  logic                        s1_axi_rvalid,
    output logic                        s1_axi_rready,

    // Slave 2 Interface (Debug)
    output logic [AXI_ID_WIDTH-1:0]    s2_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]  s2_axi_awaddr,
    output logic [7:0]                  s2_axi_awlen,
    output logic [2:0]                  s2_axi_awsize,
    output logic [1:0]                  s2_axi_awburst,
    output logic                        s2_axi_awvalid,
    input  logic                        s2_axi_awready,
    output logic [AXI_DATA_WIDTH-1:0]  s2_axi_wdata,
    output logic [AXI_DATA_WIDTH/8-1:0] s2_axi_wstrb,
    output logic                        s2_axi_wlast,
    output logic                        s2_axi_wvalid,
    input  logic                        s2_axi_wready,
    input  logic [AXI_ID_WIDTH-1:0]    s2_axi_bid,
    input  logic [1:0]                  s2_axi_bresp,
    input  logic                        s2_axi_bvalid,
    output logic                        s2_axi_bready,
    output logic [AXI_ID_WIDTH-1:0]    s2_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]  s2_axi_araddr,
    output logic [7:0]                  s2_axi_arlen,
    output logic [2:0]                  s2_axi_arsize,
    output logic [1:0]                  s2_axi_arburst,
    output logic                        s2_axi_arvalid,
    input  logic                        s2_axi_arready,
    input  logic [AXI_ID_WIDTH-1:0]    s2_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0]  s2_axi_rdata,
    input  logic [1:0]                  s2_axi_rresp,
    input  logic                        s2_axi_rlast,
    input  logic                        s2_axi_rvalid,
    output logic                        s2_axi_rready,

    // Aggregated Monitor Bus Output
    output logic        monbus_valid,
    input  logic        monbus_ready,
    output logic [63:0] monbus_data,

    // Monitor Configuration
    input  logic        cfg_error_enable,
    input  logic        cfg_compl_enable,
    input  logic        cfg_timeout_enable,
    input  logic        cfg_perf_enable
);

    // ========================================================================
    // Internal Signals
    // ========================================================================

    // Monitor bus signals (10 monitors total: 2 masters × 2 channels + 3 slaves × 2 channels)
    logic [9:0]        mon_valid;
    logic [9:0]        mon_ready;
    logic [9:0][63:0]  mon_data;

    // TODO: Add actual crossbar logic here
    // For this example, we focus on monitor integration
    // In a real design, you would instantiate an AXI crossbar IP or custom logic

    // Simplified routing: Connect master 0 to slave 0, master 1 to slave 1
    // (Real crossbar would do address-based routing)

    // ========================================================================
    // Master 0 Monitors (CPU)
    // ========================================================================

    axi4_master_rd_mon #(
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH   (AXI_DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID),
        .AGENT_ID         (AGENT_ID_M0_RD)
    ) u_m0_rd_mon (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .axi_arid           (m0_axi_arid),
        .axi_araddr         (m0_axi_araddr),
        .axi_arlen          (m0_axi_arlen),
        .axi_arsize         (m0_axi_arsize),
        .axi_arburst        (m0_axi_arburst),
        .axi_arvalid        (m0_axi_arvalid),
        .axi_arready        (m0_axi_arready),
        .axi_rid            (m0_axi_rid),
        .axi_rdata          (m0_axi_rdata),
        .axi_rresp          (m0_axi_rresp),
        .axi_rlast          (m0_axi_rlast),
        .axi_rvalid         (m0_axi_rvalid),
        .axi_rready         (m0_axi_rready),
        .monbus_pkt_valid   (mon_valid[0]),
        .monbus_pkt_ready   (mon_ready[0]),
        .monbus_pkt_data    (mon_data[0]),
        .cfg_error_enable   (cfg_error_enable),
        .cfg_compl_enable   (cfg_compl_enable),
        .cfg_timeout_enable (cfg_timeout_enable),
        .cfg_perf_enable    (cfg_perf_enable)
    );

    axi4_master_wr_mon #(
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH   (AXI_DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID),
        .AGENT_ID         (AGENT_ID_M0_WR)
    ) u_m0_wr_mon (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .axi_awid           (m0_axi_awid),
        .axi_awaddr         (m0_axi_awaddr),
        .axi_awlen          (m0_axi_awlen),
        .axi_awsize         (m0_axi_awsize),
        .axi_awburst        (m0_axi_awburst),
        .axi_awvalid        (m0_axi_awvalid),
        .axi_awready        (m0_axi_awready),
        .axi_wdata          (m0_axi_wdata),
        .axi_wstrb          (m0_axi_wstrb),
        .axi_wlast          (m0_axi_wlast),
        .axi_wvalid         (m0_axi_wvalid),
        .axi_wready         (m0_axi_wready),
        .axi_bid            (m0_axi_bid),
        .axi_bresp          (m0_axi_bresp),
        .axi_bvalid         (m0_axi_bvalid),
        .axi_bready         (m0_axi_bready),
        .monbus_pkt_valid   (mon_valid[1]),
        .monbus_pkt_ready   (mon_ready[1]),
        .monbus_pkt_data    (mon_data[1]),
        .cfg_error_enable   (cfg_error_enable),
        .cfg_compl_enable   (cfg_compl_enable),
        .cfg_timeout_enable (cfg_timeout_enable),
        .cfg_perf_enable    (cfg_perf_enable)
    );

    // ========================================================================
    // Master 1 Monitors (DMA) - Similar structure
    // ========================================================================

    axi4_master_rd_mon #(
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH   (AXI_DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID),
        .AGENT_ID         (AGENT_ID_M1_RD)
    ) u_m1_rd_mon (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .axi_arid           (m1_axi_arid),
        .axi_araddr         (m1_axi_araddr),
        .axi_arlen          (m1_axi_arlen),
        .axi_arsize         (m1_axi_arsize),
        .axi_arburst        (m1_axi_arburst),
        .axi_arvalid        (m1_axi_arvalid),
        .axi_arready        (m1_axi_arready),
        .axi_rid            (m1_axi_rid),
        .axi_rdata          (m1_axi_rdata),
        .axi_rresp          (m1_axi_rresp),
        .axi_rlast          (m1_axi_rlast),
        .axi_rvalid         (m1_axi_rvalid),
        .axi_rready         (m1_axi_rready),
        .monbus_pkt_valid   (mon_valid[2]),
        .monbus_pkt_ready   (mon_ready[2]),
        .monbus_pkt_data    (mon_data[2]),
        .cfg_error_enable   (cfg_error_enable),
        .cfg_compl_enable   (cfg_compl_enable),
        .cfg_timeout_enable (cfg_timeout_enable),
        .cfg_perf_enable    (cfg_perf_enable)
    );

    axi4_master_wr_mon #(
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH   (AXI_DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID),
        .AGENT_ID         (AGENT_ID_M1_WR)
    ) u_m1_wr_mon (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .axi_awid           (m1_axi_awid),
        .axi_awaddr         (m1_axi_awaddr),
        .axi_awlen          (m1_axi_awlen),
        .axi_awsize         (m1_axi_awsize),
        .axi_awburst        (m1_axi_awburst),
        .axi_awvalid        (m1_axi_awvalid),
        .axi_awready        (m1_axi_awready),
        .axi_wdata          (m1_axi_wdata),
        .axi_wstrb          (m1_axi_wstrb),
        .axi_wlast          (m1_axi_wlast),
        .axi_wvalid         (m1_axi_wvalid),
        .axi_wready         (m1_axi_wready),
        .axi_bid            (m1_axi_bid),
        .axi_bresp          (m1_axi_bresp),
        .axi_bvalid         (m1_axi_bvalid),
        .axi_bready         (m1_axi_bready),
        .monbus_pkt_valid   (mon_valid[3]),
        .monbus_pkt_ready   (mon_ready[3]),
        .monbus_pkt_data    (mon_data[3]),
        .cfg_error_enable   (cfg_error_enable),
        .cfg_compl_enable   (cfg_compl_enable),
        .cfg_timeout_enable (cfg_timeout_enable),
        .cfg_perf_enable    (cfg_perf_enable)
    );

    // ========================================================================
    // Slave Monitors (Memory, Peripherals, Debug)
    // ========================================================================

    // Slave 0 (Memory) - Read Monitor
    axi4_slave_rd_mon #(
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH   (AXI_DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID),
        .AGENT_ID         (AGENT_ID_S0_RD)
    ) u_s0_rd_mon (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .axi_arid           (s0_axi_arid),
        .axi_araddr         (s0_axi_araddr),
        .axi_arlen          (s0_axi_arlen),
        .axi_arsize         (s0_axi_arsize),
        .axi_arburst        (s0_axi_arburst),
        .axi_arvalid        (s0_axi_arvalid),
        .axi_arready        (s0_axi_arready),
        .axi_rid            (s0_axi_rid),
        .axi_rdata          (s0_axi_rdata),
        .axi_rresp          (s0_axi_rresp),
        .axi_rlast          (s0_axi_rlast),
        .axi_rvalid         (s0_axi_rvalid),
        .axi_rready         (s0_axi_rready),
        .monbus_pkt_valid   (mon_valid[4]),
        .monbus_pkt_ready   (mon_ready[4]),
        .monbus_pkt_data    (mon_data[4]),
        .cfg_error_enable   (cfg_error_enable),
        .cfg_compl_enable   (cfg_compl_enable),
        .cfg_timeout_enable (cfg_timeout_enable),
        .cfg_perf_enable    (cfg_perf_enable)
    );

    // Slave 0 (Memory) - Write Monitor
    axi4_slave_wr_mon #(
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH   (AXI_DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID),
        .AGENT_ID         (AGENT_ID_S0_WR)
    ) u_s0_wr_mon (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .axi_awid           (s0_axi_awid),
        .axi_awaddr         (s0_axi_awaddr),
        .axi_awlen          (s0_axi_awlen),
        .axi_awsize         (s0_axi_awsize),
        .axi_awburst        (s0_axi_awburst),
        .axi_awvalid        (s0_axi_awvalid),
        .axi_awready        (s0_axi_awready),
        .axi_wdata          (s0_axi_wdata),
        .axi_wstrb          (s0_axi_wstrb),
        .axi_wlast          (s0_axi_wlast),
        .axi_wvalid         (s0_axi_wvalid),
        .axi_wready         (s0_axi_wready),
        .axi_bid            (s0_axi_bid),
        .axi_bresp          (s0_axi_bresp),
        .axi_bvalid         (s0_axi_bvalid),
        .axi_bready         (s0_axi_bready),
        .monbus_pkt_valid   (mon_valid[5]),
        .monbus_pkt_ready   (mon_ready[5]),
        .monbus_pkt_data    (mon_data[5]),
        .cfg_error_enable   (cfg_error_enable),
        .cfg_compl_enable   (cfg_compl_enable),
        .cfg_timeout_enable (cfg_timeout_enable),
        .cfg_perf_enable    (cfg_perf_enable)
    );

    // Slave 1 (Peripherals) - Read + Write Monitors
    axi4_slave_rd_mon #(
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH   (AXI_DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID),
        .AGENT_ID         (AGENT_ID_S1_RD)
    ) u_s1_rd_mon (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .axi_arid           (s1_axi_arid),
        .axi_araddr         (s1_axi_araddr),
        .axi_arlen          (s1_axi_arlen),
        .axi_arsize         (s1_axi_arsize),
        .axi_arburst        (s1_axi_arburst),
        .axi_arvalid        (s1_axi_arvalid),
        .axi_arready        (s1_axi_arready),
        .axi_rid            (s1_axi_rid),
        .axi_rdata          (s1_axi_rdata),
        .axi_rresp          (s1_axi_rresp),
        .axi_rlast          (s1_axi_rlast),
        .axi_rvalid         (s1_axi_rvalid),
        .axi_rready         (s1_axi_rready),
        .monbus_pkt_valid   (mon_valid[6]),
        .monbus_pkt_ready   (mon_ready[6]),
        .monbus_pkt_data    (mon_data[6]),
        .cfg_error_enable   (cfg_error_enable),
        .cfg_compl_enable   (cfg_compl_enable),
        .cfg_timeout_enable (cfg_timeout_enable),
        .cfg_perf_enable    (cfg_perf_enable)
    );

    axi4_slave_wr_mon #(
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH   (AXI_DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID),
        .AGENT_ID         (AGENT_ID_S1_WR)
    ) u_s1_wr_mon (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .axi_awid           (s1_axi_awid),
        .axi_awaddr         (s1_axi_awaddr),
        .axi_awlen          (s1_axi_awlen),
        .axi_awsize         (s1_axi_awsize),
        .axi_awburst        (s1_axi_awburst),
        .axi_awvalid        (s1_axi_awvalid),
        .axi_awready        (s1_axi_awready),
        .axi_wdata          (s1_axi_wdata),
        .axi_wstrb          (s1_axi_wstrb),
        .axi_wlast          (s1_axi_wlast),
        .axi_wvalid         (s1_axi_wvalid),
        .axi_wready         (s1_axi_wready),
        .axi_bid            (s1_axi_bid),
        .axi_bresp          (s1_axi_bresp),
        .axi_bvalid         (s1_axi_bvalid),
        .axi_bready         (s1_axi_bready),
        .monbus_pkt_valid   (mon_valid[7]),
        .monbus_pkt_ready   (mon_ready[7]),
        .monbus_pkt_data    (mon_data[7]),
        .cfg_error_enable   (cfg_error_enable),
        .cfg_compl_enable   (cfg_compl_enable),
        .cfg_timeout_enable (cfg_timeout_enable),
        .cfg_perf_enable    (cfg_perf_enable)
    );

    // Slave 2 (Debug) - Read + Write Monitors
    axi4_slave_rd_mon #(
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH   (AXI_DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID),
        .AGENT_ID         (AGENT_ID_S2_RD)
    ) u_s2_rd_mon (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .axi_arid           (s2_axi_arid),
        .axi_araddr         (s2_axi_araddr),
        .axi_arlen          (s2_axi_arlen),
        .axi_arsize         (s2_axi_arsize),
        .axi_arburst        (s2_axi_arburst),
        .axi_arvalid        (s2_axi_arvalid),
        .axi_arready        (s2_axi_arready),
        .axi_rid            (s2_axi_rid),
        .axi_rdata          (s2_axi_rdata),
        .axi_rresp          (s2_axi_rresp),
        .axi_rlast          (s2_axi_rlast),
        .axi_rvalid         (s2_axi_rvalid),
        .axi_rready         (s2_axi_rready),
        .monbus_pkt_valid   (mon_valid[8]),
        .monbus_pkt_ready   (mon_ready[8]),
        .monbus_pkt_data    (mon_data[8]),
        .cfg_error_enable   (cfg_error_enable),
        .cfg_compl_enable   (cfg_compl_enable),
        .cfg_timeout_enable (cfg_timeout_enable),
        .cfg_perf_enable    (cfg_perf_enable)
    );

    axi4_slave_wr_mon #(
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH   (AXI_DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID),
        .AGENT_ID         (AGENT_ID_S2_WR)
    ) u_s2_wr_mon (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .axi_awid           (s2_axi_awid),
        .axi_awaddr         (s2_axi_awaddr),
        .axi_awlen          (s2_axi_awlen),
        .axi_awsize         (s2_axi_awsize),
        .axi_awburst        (s2_axi_awburst),
        .axi_awvalid        (s2_axi_awvalid),
        .axi_awready        (s2_axi_awready),
        .axi_wdata          (s2_axi_wdata),
        .axi_wstrb          (s2_axi_wstrb),
        .axi_wlast          (s2_axi_wlast),
        .axi_wvalid         (s2_axi_wvalid),
        .axi_wready         (s2_axi_wready),
        .axi_bid            (s2_axi_bid),
        .axi_bresp          (s2_axi_bresp),
        .axi_bvalid         (s2_axi_bvalid),
        .axi_bready         (s2_axi_bready),
        .monbus_pkt_valid   (mon_valid[9]),
        .monbus_pkt_ready   (mon_ready[9]),
        .monbus_pkt_data    (mon_data[9]),
        .cfg_error_enable   (cfg_error_enable),
        .cfg_compl_enable   (cfg_compl_enable),
        .cfg_timeout_enable (cfg_timeout_enable),
        .cfg_perf_enable    (cfg_perf_enable)
    );

    // ========================================================================
    // Monitor Bus Arbiter (Round-Robin)
    // ========================================================================
    // Aggregates monitor packets from 10 sources using round-robin arbitration
    // Note: In this simple example, we use a basic round-robin arbiter
    // For more complex systems with QoS requirements, use weighted arbiters
    // from rtl/common/arbiter_round_robin_weighted.sv

    arbiter_round_robin #(
        .N         (10),         // 10 monitor sources
        .REG_OUTPUT(1)           // Register output for timing
    ) u_mon_arbiter (
        .i_clk      (aclk),
        .i_rst_n    (aresetn),
        .i_request  (mon_valid),
        .o_grant    (mon_ready),
        .o_valid    (monbus_valid)
    );

    // Data muxing (select granted monitor's data)
    logic [3:0] grant_id;
    always_comb begin
        grant_id = '0;
        for (int i = 0; i < 10; i++) begin
            if (mon_ready[i]) grant_id = i[3:0];
        end
    end

    assign monbus_data = mon_data[grant_id];

    // Note: This simple implementation assumes monbus_ready is always high
    // or connect to a downstream FIFO for proper backpressure handling

    // ========================================================================
    // TODO: Add actual crossbar routing logic
    // ========================================================================
    // This example focuses on monitor integration.
    // In a real design, you would add:
    // 1. Address decoder for routing
    // 2. Arbitration logic for multiple masters accessing same slave
    // 3. Data path muxing/demuxing
    // 4. Optional pipelining for timing closure

    // For now, tie off slave interfaces (would connect to actual slaves)
    assign s0_axi_awready = 1'b0;
    assign s0_axi_wready = 1'b0;
    assign s0_axi_bid = '0;
    assign s0_axi_bresp = 2'b00;
    assign s0_axi_bvalid = 1'b0;
    assign s0_axi_arready = 1'b0;
    assign s0_axi_rid = '0;
    assign s0_axi_rdata = '0;
    assign s0_axi_rresp = 2'b00;
    assign s0_axi_rlast = 1'b0;
    assign s0_axi_rvalid = 1'b0;

    assign s1_axi_awready = 1'b0;
    assign s1_axi_wready = 1'b0;
    assign s1_axi_bid = '0;
    assign s1_axi_bresp = 2'b00;
    assign s1_axi_bvalid = 1'b0;
    assign s1_axi_arready = 1'b0;
    assign s1_axi_rid = '0;
    assign s1_axi_rdata = '0;
    assign s1_axi_rresp = 2'b00;
    assign s1_axi_rlast = 1'b0;
    assign s1_axi_rvalid = 1'b0;

    assign s2_axi_awready = 1'b0;
    assign s2_axi_wready = 1'b0;
    assign s2_axi_bid = '0;
    assign s2_axi_bresp = 2'b00;
    assign s2_axi_bvalid = 1'b0;
    assign s2_axi_arready = 1'b0;
    assign s2_axi_rid = '0;
    assign s2_axi_rdata = '0;
    assign s2_axi_rresp = 2'b00;
    assign s2_axi_rlast = 1'b0;
    assign s2_axi_rvalid = 1'b0;

    // Tie off master responses (would come from crossbar)
    assign m0_axi_awready = 1'b0;
    assign m0_axi_wready = 1'b0;
    assign m0_axi_bid = '0;
    assign m0_axi_bresp = 2'b00;
    assign m0_axi_bvalid = 1'b0;
    assign m0_axi_arready = 1'b0;
    assign m0_axi_rid = '0;
    assign m0_axi_rdata = '0;
    assign m0_axi_rresp = 2'b00;
    assign m0_axi_rlast = 1'b0;
    assign m0_axi_rvalid = 1'b0;

    assign m1_axi_awready = 1'b0;
    assign m1_axi_wready = 1'b0;
    assign m1_axi_bid = '0;
    assign m1_axi_bresp = 2'b00;
    assign m1_axi_bvalid = 1'b0;
    assign m1_axi_arready = 1'b0;
    assign m1_axi_rid = '0;
    assign m1_axi_rdata = '0;
    assign m1_axi_rresp = 2'b00;
    assign m1_axi_rlast = 1'b0;
    assign m1_axi_rvalid = 1'b0;

endmodule
