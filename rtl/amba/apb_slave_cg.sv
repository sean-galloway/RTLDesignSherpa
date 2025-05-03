`timescale 1ns / 1ps

module apb_slave_cg #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int STRB_WIDTH      = 32 / 8,
    parameter int PPROT_WIDTH     = 3,
    parameter int DEPTH      = 2,
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Default width of idle counter
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PPROT_WIDTH,
    parameter int ICW = CG_IDLE_COUNT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + 1,
    parameter int RPW = DW + 1
) (
    // Clock and Reset
    input  logic              pclk,
    input  logic              presetn,

    // Configs
    input logic               i_cfg_cg_enable,     // Global clock gate enable
    input logic  [ICW-1:0]    i_cfg_cg_idle_count, // Idle countdown value

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
    // Clock gating indicator
    output logic              o_apb_clock_gating
);

    // local clock gating signals
    logic  r_wakeup;
    logic  gated_pclk;

    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn)
            r_wakeup <= 1'b1;
        else
            r_wakeup <= s_apb_PSEL || o_cmd_valid || i_rsp_valid || (r_apb_state == BUSY);
    end

    // Instantiate clock gate controller
    amba_clock_gate_ctrl #(
        .N(CG_IDLE_COUNT_WIDTH)
    ) i_amba_clock_gate_ctrl (
        .clk_in              (pclk),
        .aresetn             (presetn),
        .i_cfg_cg_enable     (i_cfg_cg_enable),
        .i_cfg_cg_idle_count (i_cfg_cg_idle_count),
        .i_user_valid        (r_wakeup),
        .i_axi_valid         ('b0),
        .clk_out             (gated_pclk),
        .o_gating            (o_apb_clock_gating),
        .o_idle              ()
    );

    apb_slave #(
        .ADDR_WIDTH       (ADDR_WIDTH),
        .DATA_WIDTH       (DATA_WIDTH),
        .STRB_WIDTH       (STRB_WIDTH),
        .PPROT_WIDTH      (PPROT_WIDTH),
        .DEPTH       (DEPTH)
    ) u_apb_slave (
        // Clock / Reset
        .pclk             (gated_pclk),
        .presetn          (presetn),
        // APB interface
        .s_apb_PSEL       (s_apb_PSEL),
        .s_apb_PENABLE    (s_apb_PENABLE),
        .s_apb_PREADY     (s_apb_PREADY),
        .s_apb_PADDR      (s_apb_PADDR),
        .s_apb_PWRITE     (s_apb_PWRITE),
        .s_apb_PWDATA     (s_apb_PWDATA),
        .s_apb_PSTRB      (s_apb_PSTRB),
        .s_apb_PPROT      (s_apb_PPROT),
        .s_apb_PRDATA     (s_apb_PRDATA),
        .s_apb_PSLVERR    (s_apb_PSLVERR),
        // Command interface
        .o_cmd_valid      (o_cmd_valid),
        .i_cmd_ready      (i_cmd_ready),
        .o_cmd_pwrite     (o_cmd_pwrite),
        .o_cmd_paddr      (o_cmd_paddr),
        .o_cmd_pwdata     (o_cmd_pwdata),
        .o_cmd_pstrb      (o_cmd_pstrb),
        .o_cmd_pprot      (o_cmd_pprot),
        // Response interface
        .i_rsp_valid      (i_rsp_valid),
        .o_rsp_ready      (o_rsp_ready),
        .i_rsp_prdata     (i_rsp_prdata),
        .i_rsp_pslverr    (i_rsp_pslverr)
    );

endmodule : apb_slave_cg
