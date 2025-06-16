`timescale 1ns / 1ps

module apb_slave_cdc_cg #(
    parameter int ADDR_WIDTH         = 32,
    parameter int DATA_WIDTH         = 32,
    parameter int STRB_WIDTH         = DATA_WIDTH / 8,
    parameter int PROT_WIDTH         = 3,
    parameter int DEPTH              = 2,
    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Width of idle counter
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + 1,
    parameter int RPW = DW + 1
) (
    // Clock and Reset
    input  logic              aclk,
    input  logic              aresetn,
    input  logic              pclk,
    input  logic              presetn,

    // Clock gating configuration
    input  logic                          i_cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] i_cfg_cg_idle_count,

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
    input  logic              i_rsp_pslverr,

    // Clock gating status
    output logic              o_pclk_cg_gating,
    output logic              o_pclk_cg_idle,
    output logic              o_aclk_cg_gating,
    output logic              o_aclk_cg_idle
);

    // Local Parameters
    localparam int APBCmdWidth = 1 + AW + DW + SW + PW;
    localparam int APBRspWidth = 1 + DW;

    // Gated clock signals
    logic gated_pclk;
    logic gated_aclk;

    // Internal signals for ready signals
    logic int_cmd_ready;
    logic int_rsp_ready_aclk;  // ACLK domain response ready
    logic int_rsp_ready_pclk;  // PCLK domain response ready
    logic int_apb_PREADY;

    // Combined valid signals for clock gating control - PCLK domain
    logic pclk_user_valid;
    logic pclk_axi_valid;

    // Combined valid signals for clock gating control - ACLK domain
    logic aclk_user_valid;
    logic aclk_axi_valid;

    // Internal signals to pass between the handshake
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

    // Force PREADY to 0 when clock gating is active in PCLK domain
    assign s_apb_PREADY = o_pclk_cg_gating ? 1'b0 : int_apb_PREADY;

    // OR all PCLK domain valid signals for clock gating control
    assign pclk_user_valid = s_apb_PSEL || w_rsp_valid;
    assign pclk_axi_valid = w_cmd_valid;

    // OR all ACLK domain valid signals for clock gating control
    assign aclk_user_valid = i_rsp_valid;
    assign aclk_axi_valid = o_cmd_valid || i_cmd_ready;

    // Force ready signals to 0 when clock gating is active in their respective domains
    assign w_cmd_ready = o_pclk_cg_gating ? 1'b0 : int_cmd_ready;
    assign o_rsp_ready = o_aclk_cg_gating ? 1'b0 : int_rsp_ready_aclk;
    assign w_rsp_ready = o_pclk_cg_gating ? 1'b0 : int_rsp_ready_pclk;  // Fixed - force to 0 during gating

    // Instantiate PCLK domain clock gate controller
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)
    ) i_pclk_gate_ctrl (
        .clk_in              (pclk),
        .aresetn             (presetn),
        .i_cfg_cg_enable     (i_cfg_cg_enable),
        .i_cfg_cg_idle_count (i_cfg_cg_idle_count),
        .i_user_valid        (pclk_user_valid),
        .i_axi_valid         (pclk_axi_valid),
        .clk_out             (gated_pclk),
        .o_gating            (o_pclk_cg_gating),
        .o_idle              (o_pclk_cg_idle)
    );

    // Instantiate ACLK domain clock gate controller
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)
    ) i_aclk_gate_ctrl (
        .clk_in              (aclk),
        .aresetn             (aresetn),
        .i_cfg_cg_enable     (i_cfg_cg_enable),
        .i_cfg_cg_idle_count (i_cfg_cg_idle_count),
        .i_user_valid        (aclk_user_valid),
        .i_axi_valid         (aclk_axi_valid),
        .clk_out             (gated_aclk),
        .o_gating            (o_aclk_cg_gating),
        .o_idle              (o_aclk_cg_idle)
    );

    // Instantiate the APB slave with gated clock
    apb_slave #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .STRB_WIDTH(STRB_WIDTH),
        .PROT_WIDTH(PROT_WIDTH),
        .DEPTH(DEPTH)
    ) u_apb_slave (
        // Clock and Reset
        .pclk(gated_pclk),       // Use gated clock
        .presetn(presetn),

        // APB interface
        .s_apb_PSEL(s_apb_PSEL),
        .s_apb_PENABLE(s_apb_PENABLE),
        .s_apb_PREADY(int_apb_PREADY),  // Connect to internal signal
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
        .o_rsp_ready(int_rsp_ready_pclk),  // Fixed - connect to internal signal
        .i_rsp_prdata(w_rsp_prdata),
        .i_rsp_pslverr(w_rsp_pslverr)
    );

    // Use clock domain crossing handshake for command path
    cdc_handshake #(
        .DATA_WIDTH(APBCmdWidth)
    ) u_cmd_cdc_handshake (
        .clk_src         (gated_pclk),       // Use gated clock
        .rst_src_n       (presetn),
        .src_valid       (w_cmd_valid),
        .src_ready       (int_cmd_ready),
        .src_data        ({w_cmd_pwrite, w_cmd_paddr, w_cmd_pwdata, w_cmd_pstrb, w_cmd_pprot}),

        .clk_dst         (gated_aclk),       // Use gated clock
        .rst_dst_n       (aresetn),
        .dst_valid       (o_cmd_valid),
        .dst_ready       (i_cmd_ready),
        .dst_data        ({o_cmd_pwrite, o_cmd_paddr, o_cmd_pwdata, o_cmd_pstrb, o_cmd_pprot})
    );

    // Use clock domain crossing handshake for response path
    cdc_handshake #(
        .DATA_WIDTH(APBRspWidth)
    ) u_rsp_cdc_handshake (
        .clk_src         (gated_aclk),       // Use gated clock
        .rst_src_n       (aresetn),
        .src_valid       (i_rsp_valid),
        .src_ready       (int_rsp_ready_aclk),
        .src_data        ({i_rsp_pslverr, i_rsp_prdata}),

        .clk_dst         (gated_pclk),       // Use gated clock
        .rst_dst_n       (presetn),
        .dst_valid       (w_rsp_valid),
        .dst_ready       (w_rsp_ready),
        .dst_data        ({w_rsp_pslverr, w_rsp_prdata})
    );

endmodule : apb_slave_cdc_cg