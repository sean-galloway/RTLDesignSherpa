`timescale 1ns / 1ps

module apb_slave_cdc #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int STRB_WIDTH      = DATA_WIDTH / 8,
    parameter int PROT_WIDTH      = 3,
    parameter int DEPTH      = 2,
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + 1, // verilog_lint: waive line-length
    parameter int RPW = DW + 1
) (
    // Clock and Reset
    input  logic              aclk,
    input  logic              aresetn,
    input  logic              pclk,
    input  logic              presetn,

    // APB interface
    input  logic              s_apb_PSEL,
    input  logic              s_apb_PENABLE,
    output logic              s_apb_PREADY,
    input  logic [AW-1:0]     s_apb_PADDR,
    input  logic              s_apb_PWRITE,
    input  logic [DW-1:0]     s_apb_PWDATA,
    input  logic [SW-1:0]     s_apb_PSTRB,
    input  logic [PW-1:0]     s_apb_PPROT,
    output logic [DW-1:0]     s_apb_PRDATA,
    output logic              s_apb_PSLVERR,

    // Command Interface
    output logic              o_cmd_valid,
    input  logic              i_cmd_ready,
    output logic              o_cmd_pwrite,
    output logic [AW-1:0]     o_cmd_paddr,
    output logic [DW-1:0]     o_cmd_pwdata,
    output logic [SW-1:0]     o_cmd_pstrb,
    output logic [PW-1:0]     o_cmd_pprot,

    // Response Interface
    input  logic              i_rsp_valid,
    output logic              o_rsp_ready,
    input  logic [DW-1:0]     i_rsp_prdata,
    input  logic              i_rsp_pslverr
);

    // Local Parameters
    localparam int APBCmdWidth = 1 + AW + DW + SW + PW;
    localparam int APBRspWidth = 1 + DW;

    // local signal to pass between the handshake
    logic              w_cmd_valid;
    logic              w_cmd_ready;
    logic              w_cmd_pwrite;
    logic [AW-1:0]     w_cmd_paddr;
    logic [DW-1:0]     w_cmd_pwdata;
    logic [SW-1:0]     w_cmd_pstrb;
    logic [PW-1:0]     w_cmd_pprot;


    logic              w_rsp_valid;
    logic              w_rsp_ready;
    logic [DW-1:0]     w_rsp_prdata;
    logic              w_rsp_pslverr;

    apb_slave #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32),
        .STRB_WIDTH(4),
        .PROT_WIDTH(3),
        .DEPTH(2)
    ) u_apb_slave (
        // Clock and Reset
        .pclk(pclk),
        .presetn(presetn),

        // APB interface
        .s_apb_PSEL(s_apb_PSEL),
        .s_apb_PENABLE(s_apb_PENABLE),
        .s_apb_PREADY(s_apb_PREADY),
        .s_apb_PADDR(s_apb_PADDR),
        .s_apb_PWRITE(s_apb_PWRITE),
        .s_apb_PWDATA(s_apb_PWDATA),
        .s_apb_PSTRB(s_apb_PSTRB),
        .s_apb_PPROT(s_apb_PPROT),
        .s_apb_PRDATA(s_apb_PRDATA),
        .s_apb_PSLVERR(s_apb_PSLVERR),

        // Command Interface
        .o_cmd_valid(w_cmd_valid),
        .i_cmd_ready(w_cmd_ready),
        .o_cmd_pwrite(w_cmd_pwrite),
        .o_cmd_paddr(w_cmd_paddr),
        .o_cmd_pwdata(w_cmd_pwdata),
        .o_cmd_pstrb(w_cmd_pstrb),
        .o_cmd_pprot(w_cmd_pprot),

        // Response Interface
        .i_rsp_valid(w_rsp_valid),
        .o_rsp_ready(w_rsp_ready),
        .i_rsp_prdata(w_rsp_prdata),
        .i_rsp_pslverr(w_rsp_pslverr)
    );

    cdc_handshake #(
        .DATA_WIDTH(APBCmdWidth)
    ) u_cmd_cdc_handshake (
        .clk_src         (pclk),
        .rst_src_n       (presetn),
        .valid_src       (w_cmd_valid),
        .ready_src       (w_cmd_ready),
        .data_src        ({w_cmd_pwrite, w_cmd_paddr, w_cmd_pwdata, w_cmd_pstrb, w_cmd_pprot}),

        .clk_dst         (aclk),
        .rst_dst_n       (aresetn),
        .valid_dst       (o_cmd_valid),
        .ready_dst       (i_cmd_ready),
        .data_dst        (
            {o_cmd_pwrite, o_cmd_paddr, o_cmd_pwdata, o_cmd_pstrb, o_cmd_pprot})
    );

    cdc_handshake #(
        .DATA_WIDTH(APBRspWidth)
    ) u_rsp_cdc_handshake (
        .clk_src         (aclk),
        .rst_src_n       (aresetn),
        .src_valid       (i_rsp_valid),
        .src_ready       (o_rsp_ready),
        .src_data        ({i_rsp_pslverr, i_rsp_prdata}),

        .clk_dst         (pclk),
        .rst_dst_n       (presetn),
        .dst_valid       (w_rsp_valid),
        .dst_ready       (w_rsp_ready),
        .dst_data        ({w_rsp_pslverr, w_rsp_prdata})
    );

endmodule : apb_slave_cdc
