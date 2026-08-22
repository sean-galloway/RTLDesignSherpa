`timescale 1ns / 1ps
//
// axi4_to_apb5_shim: AXI4 slave -> APB5 requester (BRIDGE-002 A5-3c).
//
// Thin wrapper over axi4_to_apb5's workhorse, axi4_to_apb4_shim: the
// protocol engine is identical (APB5 keeps the APB4 transfer protocol),
// and the APB5 additions are pure sideband on this surface --
// requester-driven PAUSER/PWUSER (tied to '0: nothing upstream sources
// them; the AXI user bits do not map onto APB user semantics) and
// completer-driven PWAKEUP/PRUSER/PBUSER (accepted and terminated).
// The port convention mirrors rtl/amba/apb5/apb5_slave.sv exactly, so
// this requester drops onto that completer pin-for-pin.

module axi4_to_apb5_shim #(
    parameter int DEPTH_AW = 2,
    parameter int DEPTH_W = 4,
    parameter int DEPTH_B = 2,
    parameter int DEPTH_AR = 2,
    parameter int DEPTH_R = 4,
    parameter int SIDE_DEPTH = 4,
    parameter int APB_CMD_DEPTH = 4,
    parameter int APB_RSP_DEPTH = 4,
    parameter int USE_JOHNSON = 0,
    parameter int AXI_ID_WIDTH = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 32,
    parameter int AXI_USER_WIDTH = 1,
    parameter int APB_ADDR_WIDTH = 32,
    parameter int APB_DATA_WIDTH = 32,
    parameter bit USE_2_PHASE_CDC = 1'b1,   // deprecated, ignored
    parameter int AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8,
    parameter int APB_WSTRB_WIDTH = APB_DATA_WIDTH / 8,
    // APB5 user-signal widths. These default to 1, NARROWER than
    // apb5_slave.sv's own default of 4 -- override them to match
    // whatever completer you attach.
    parameter int APB_AUSER_WIDTH = 1,
    parameter int APB_WUSER_WIDTH = 1,
    parameter int APB_RUSER_WIDTH = 1,
    parameter int APB_BUSER_WIDTH = 1
) (

    // Clock and Reset
    input  logic                          aclk,
    input  logic                          aresetn,
    input  logic                          pclk,
    input  logic                          presetn,

    // Write address channel (AW)
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axi_awaddr,
    input  logic [7:0]                    s_axi_awlen,
    input  logic [2:0]                    s_axi_awsize,
    input  logic [1:0]                    s_axi_awburst,
    input  logic                          s_axi_awlock,
    input  logic [3:0]                    s_axi_awcache,
    input  logic [2:0]                    s_axi_awprot,
    input  logic [3:0]                    s_axi_awqos,
    input  logic [3:0]                    s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_awuser,
    input  logic                          s_axi_awvalid,
    output logic                          s_axi_awready,

    // Write data channel (W)
    input  logic [AXI_DATA_WIDTH-1:0]     s_axi_wdata,
    input  logic [AXI_WSTRB_WIDTH-1:0]    s_axi_wstrb,
    input  logic                          s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_wuser,
    input  logic                          s_axi_wvalid,
    output logic                          s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]       s_axi_bid,
    output logic [1:0]                    s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_buser,
    output logic                          s_axi_bvalid,
    input  logic                          s_axi_bready,

    // Read address channel (AR)
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axi_araddr,
    input  logic [7:0]                    s_axi_arlen,
    input  logic [2:0]                    s_axi_arsize,
    input  logic [1:0]                    s_axi_arburst,
    input  logic                          s_axi_arlock,
    input  logic [3:0]                    s_axi_arcache,
    input  logic [2:0]                    s_axi_arprot,
    input  logic [3:0]                    s_axi_arqos,
    input  logic [3:0]                    s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_aruser,
    input  logic                          s_axi_arvalid,
    output logic                          s_axi_arready,

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]       s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]     s_axi_rdata,
    output logic [1:0]                    s_axi_rresp,
    output logic                          s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_ruser,
    output logic                          s_axi_rvalid,
    input  logic                          s_axi_rready,

    // APB Master Interface (Outputs)
    output logic                          m_apb_PSEL,
    output logic [APB_ADDR_WIDTH-1:0]     m_apb_PADDR,
    output logic                          m_apb_PENABLE,
    output logic                          m_apb_PWRITE,
    output logic [APB_DATA_WIDTH-1:0]     m_apb_PWDATA,
    output logic [APB_WSTRB_WIDTH-1:0]    m_apb_PSTRB,
    output logic [2:0]                    m_apb_PPROT,

    // APB Master Interface (Inputs)
    input  logic [APB_DATA_WIDTH-1:0]     m_apb_PRDATA,
    input  logic                          m_apb_PREADY,
    input  logic                          m_apb_PSLVERR,

    // APB5 sideband additions (requester surface)
    output logic [APB_AUSER_WIDTH-1:0]    m_apb_PAUSER,
    output logic [APB_WUSER_WIDTH-1:0]    m_apb_PWUSER,
    input  logic                          m_apb_PWAKEUP,
    input  logic [APB_RUSER_WIDTH-1:0]    m_apb_PRUSER,
    input  logic [APB_BUSER_WIDTH-1:0]    m_apb_PBUSER
);

    // Requester-driven APB5 sideband: nothing upstream sources these.
    assign m_apb_PAUSER = '0;
    assign m_apb_PWUSER = '0;

    // Completer-driven APB5 sideband is accepted and terminated:
    wire unused_apb5_sideband = &{1'b0, m_apb_PWAKEUP, m_apb_PRUSER,
                                  m_apb_PBUSER};

    axi4_to_apb4_shim #(
        .DEPTH_AW(DEPTH_AW),
        .DEPTH_W(DEPTH_W),
        .DEPTH_B(DEPTH_B),
        .DEPTH_AR(DEPTH_AR),
        .DEPTH_R(DEPTH_R),
        .SIDE_DEPTH(SIDE_DEPTH),
        .APB_CMD_DEPTH(APB_CMD_DEPTH),
        .APB_RSP_DEPTH(APB_RSP_DEPTH),
        .USE_JOHNSON(USE_JOHNSON),
        .AXI_ID_WIDTH(AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .APB_ADDR_WIDTH(APB_ADDR_WIDTH),
        .APB_DATA_WIDTH(APB_DATA_WIDTH),
        .USE_2_PHASE_CDC(USE_2_PHASE_CDC),
        .AXI_WSTRB_WIDTH(AXI_WSTRB_WIDTH),
        .APB_WSTRB_WIDTH(APB_WSTRB_WIDTH)
    ) u_axi4_to_apb4_shim (
        .aclk(aclk),
        .aresetn(aresetn),
        .pclk(pclk),
        .presetn(presetn),
        .s_axi_awid(s_axi_awid),
        .s_axi_awaddr(s_axi_awaddr),
        .s_axi_awlen(s_axi_awlen),
        .s_axi_awsize(s_axi_awsize),
        .s_axi_awburst(s_axi_awburst),
        .s_axi_awlock(s_axi_awlock),
        .s_axi_awcache(s_axi_awcache),
        .s_axi_awprot(s_axi_awprot),
        .s_axi_awqos(s_axi_awqos),
        .s_axi_awregion(s_axi_awregion),
        .s_axi_awuser(s_axi_awuser),
        .s_axi_awvalid(s_axi_awvalid),
        .s_axi_awready(s_axi_awready),
        .s_axi_wdata(s_axi_wdata),
        .s_axi_wstrb(s_axi_wstrb),
        .s_axi_wlast(s_axi_wlast),
        .s_axi_wuser(s_axi_wuser),
        .s_axi_wvalid(s_axi_wvalid),
        .s_axi_wready(s_axi_wready),
        .s_axi_bid(s_axi_bid),
        .s_axi_bresp(s_axi_bresp),
        .s_axi_buser(s_axi_buser),
        .s_axi_bvalid(s_axi_bvalid),
        .s_axi_bready(s_axi_bready),
        .s_axi_arid(s_axi_arid),
        .s_axi_araddr(s_axi_araddr),
        .s_axi_arlen(s_axi_arlen),
        .s_axi_arsize(s_axi_arsize),
        .s_axi_arburst(s_axi_arburst),
        .s_axi_arlock(s_axi_arlock),
        .s_axi_arcache(s_axi_arcache),
        .s_axi_arprot(s_axi_arprot),
        .s_axi_arqos(s_axi_arqos),
        .s_axi_arregion(s_axi_arregion),
        .s_axi_aruser(s_axi_aruser),
        .s_axi_arvalid(s_axi_arvalid),
        .s_axi_arready(s_axi_arready),
        .s_axi_rid(s_axi_rid),
        .s_axi_rdata(s_axi_rdata),
        .s_axi_rresp(s_axi_rresp),
        .s_axi_rlast(s_axi_rlast),
        .s_axi_ruser(s_axi_ruser),
        .s_axi_rvalid(s_axi_rvalid),
        .s_axi_rready(s_axi_rready),
        .m_apb_PSEL(m_apb_PSEL),
        .m_apb_PADDR(m_apb_PADDR),
        .m_apb_PENABLE(m_apb_PENABLE),
        .m_apb_PWRITE(m_apb_PWRITE),
        .m_apb_PWDATA(m_apb_PWDATA),
        .m_apb_PSTRB(m_apb_PSTRB),
        .m_apb_PPROT(m_apb_PPROT),
        .m_apb_PRDATA(m_apb_PRDATA),
        .m_apb_PREADY(m_apb_PREADY),
        .m_apb_PSLVERR(m_apb_PSLVERR)
    );

endmodule : axi4_to_apb5_shim
