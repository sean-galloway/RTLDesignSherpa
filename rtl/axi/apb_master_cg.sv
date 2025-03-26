`timescale 1ns / 1ps

module apb_master_cg #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int PROT_WIDTH      = 3,
    parameter int CMD_DEPTH       = 6,
    parameter int RSP_DEPTH       = 6,
    parameter int STRB_WIDTH      = DATA_WIDTH / 8,
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Default width of idle counter
    // Short Parameters
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int ICW = CG_IDLE_COUNT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + 1,
    parameter int RPW = DW + 1
) (
    // Clock and Reset
    input  logic              pclk,
    input  logic              presetn,

    // Configs
    input  logic              i_cfg_cg_enable,     // Global clock gate enable
    input  logic [ICW-1:0]    i_cfg_cg_idle_count, // Idle countdown value

    // APB interface
    output logic              m_apb_PSEL,
    output logic              m_apb_PENABLE,
    output logic [AW-1:0]     m_apb_PADDR,
    output logic              m_apb_PWRITE,
    output logic [DW-1:0]     m_apb_PWDATA,
    output logic [SW-1:0]     m_apb_PSTRB,
    output logic [PW-1:0]     m_apb_PPROT,
    input  logic [DW-1:0]     m_apb_PRDATA,
    input  logic              m_apb_PSLVERR,
    input  logic              m_apb_PREADY,

    // Command Packet
    input  logic              i_cmd_valid,
    output logic              o_cmd_ready,
    input  logic              i_cmd_pwrite,
    input  logic [AW-1:0]     i_cmd_paddr,
    input  logic [DW-1:0]     i_cmd_pwdata,
    input  logic [SW-1:0]     i_cmd_pstrb,
    input  logic [PW-1:0]     i_cmd_pprot,

    // Read Return interface
    output logic              o_rsp_valid,
    input  logic              i_rsp_ready,
    output logic [DW-1:0]     o_rsp_prdata,
    output logic              o_rsp_pslverr,

    // Clock gating indicator
    output logic              o_apb_clock_gating
);

    // Local clock gating signals
    logic  r_wakeup;
    logic  gated_pclk;

    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn)
            r_wakeup <= 1'b1;
        else
            // Wake up when there's a command, a response pending,
            // or when the master is in the middle of a transaction
            r_wakeup <= i_cmd_valid || o_rsp_valid || m_apb_PSEL || m_apb_PENABLE;
    end

    // Instantiate clock gate controller
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)
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

    // Instantiate the APB master
    apb_master #(
        .ADDR_WIDTH      (ADDR_WIDTH),
        .DATA_WIDTH      (DATA_WIDTH),
        .PROT_WIDTH      (PROT_WIDTH),
        .CMD_DEPTH       (CMD_DEPTH),
        .RSP_DEPTH       (RSP_DEPTH),
        .STRB_WIDTH      (STRB_WIDTH)
    ) u_apb_master (
        // Clock / Reset
        .pclk              (gated_pclk),
        .presetn           (presetn),
        // APB interface
        .m_apb_PSEL        (m_apb_PSEL),
        .m_apb_PENABLE     (m_apb_PENABLE),
        .m_apb_PADDR       (m_apb_PADDR),
        .m_apb_PWRITE      (m_apb_PWRITE),
        .m_apb_PWDATA      (m_apb_PWDATA),
        .m_apb_PSTRB       (m_apb_PSTRB),
        .m_apb_PPROT       (m_apb_PPROT),
        .m_apb_PRDATA      (m_apb_PRDATA),
        .m_apb_PSLVERR     (m_apb_PSLVERR),
        .m_apb_PREADY      (m_apb_PREADY),
        // Command interface
        .i_cmd_valid       (i_cmd_valid),
        .o_cmd_ready       (o_cmd_ready),
        .i_cmd_pwrite      (i_cmd_pwrite),
        .i_cmd_paddr       (i_cmd_paddr),
        .i_cmd_pwdata      (i_cmd_pwdata),
        .i_cmd_pstrb       (i_cmd_pstrb),
        .i_cmd_pprot       (i_cmd_pprot),
        // Response interface
        .o_rsp_valid       (o_rsp_valid),
        .i_rsp_ready       (i_rsp_ready),
        .o_rsp_prdata      (o_rsp_prdata),
        .o_rsp_pslverr     (o_rsp_pslverr)
    );

endmodule : apb_master_cg
