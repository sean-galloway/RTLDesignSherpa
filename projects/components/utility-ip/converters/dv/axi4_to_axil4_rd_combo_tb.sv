// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Standalone testbench for axi4_to_axil4_rd that exposes the combinational-
// response bug: when the attached AXIL slave responds in the same cycle as
// the AR handshake, the converter's r_rd_outstanding flag is set but never
// cleared, so the next AR is rejected and the converter hangs.

`timescale 1ns / 1ps

module axi4_to_axil4_rd_combo_tb (
    input  logic aclk,
    input  logic aresetn,

    output logic        s_axi_arready,
    input  logic        s_axi_arvalid,
    input  logic [31:0] s_axi_araddr,
    input  logic [7:0]  s_axi_arlen,

    output logic        s_axi_rvalid,
    input  logic        s_axi_rready,
    output logic [31:0] s_axi_rdata,
    output logic [1:0]  s_axi_rresp,
    output logic        s_axi_rlast,

    output logic        probe_rd_outstanding
);

    logic        m_axil_arvalid;
    logic        m_axil_arready;
    logic [31:0] m_axil_araddr;
    logic [2:0]  m_axil_arprot;
    logic [31:0] m_axil_rdata;
    logic [1:0]  m_axil_rresp;
    logic        m_axil_rvalid;
    logic        m_axil_rready;

    axi4_to_axil4_rd #(
        .AXI_ID_WIDTH  (1),
        .AXI_ADDR_WIDTH(32),
        .AXI_DATA_WIDTH(32),
        .AXI_USER_WIDTH(1)
    ) u_dut (
        .aclk   (aclk),
        .aresetn(aresetn),

        .s_axi_arid   (1'b0),
        .s_axi_araddr (s_axi_araddr),
        .s_axi_arlen  (s_axi_arlen),
        .s_axi_arsize (3'b010),
        .s_axi_arburst(2'b01),
        .s_axi_arlock (1'b0),
        .s_axi_arcache(4'b0),
        .s_axi_arprot (3'b0),
        .s_axi_arqos  (4'b0),
        .s_axi_arregion(4'b0),
        .s_axi_aruser (1'b0),
        .s_axi_arvalid(s_axi_arvalid),
        .s_axi_arready(s_axi_arready),

        .s_axi_rid    (),
        .s_axi_rdata  (s_axi_rdata),
        .s_axi_rresp  (s_axi_rresp),
        .s_axi_rlast  (s_axi_rlast),
        .s_axi_ruser  (),
        .s_axi_rvalid (s_axi_rvalid),
        .s_axi_rready (s_axi_rready),

        .m_axil_araddr (m_axil_araddr),
        .m_axil_arprot (m_axil_arprot),
        .m_axil_arvalid(m_axil_arvalid),
        .m_axil_arready(m_axil_arready),

        .m_axil_rdata  (m_axil_rdata),
        .m_axil_rresp  (m_axil_rresp),
        .m_axil_rvalid (m_axil_rvalid),
        .m_axil_rready (m_axil_rready)
    );

    // Combinational AXIL slave: accepts AR and returns R in the same cycle.
    assign m_axil_arready = 1'b1;
    assign m_axil_rvalid  = m_axil_arvalid;
    assign m_axil_rresp   = 2'b00;
    assign m_axil_rdata   = {m_axil_araddr[15:0], 16'hA5A5};

    assign probe_rd_outstanding = u_dut.r_rd_outstanding;

endmodule : axi4_to_axil4_rd_combo_tb
