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
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic              cmd_pwrite,
    output logic [AW-1:0]     cmd_paddr,
    output logic [DW-1:0]     cmd_pwdata,
    output logic [SW-1:0]     cmd_pstrb,
    output logic [PW-1:0]     cmd_pprot,

    // Response Interface
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [DW-1:0]     rsp_prdata,
    input  logic              rsp_pslverr,
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
            r_wakeup <= s_apb_PSEL || cmd_valid || rsp_valid || (r_apb_state == BUSY);
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
        .cmd_valid      (cmd_valid),
        .cmd_ready      (cmd_ready),
        .cmd_pwrite     (cmd_pwrite),
        .cmd_paddr      (cmd_paddr),
        .cmd_pwdata     (cmd_pwdata),
        .cmd_pstrb      (cmd_pstrb),
        .cmd_pprot      (cmd_pprot),
        // Response interface
        .rsp_valid      (rsp_valid),
        .rsp_ready      (rsp_ready),
        .rsp_prdata     (rsp_prdata),
        .rsp_pslverr    (rsp_pslverr)
    );

endmodule : apb_slave_cg
