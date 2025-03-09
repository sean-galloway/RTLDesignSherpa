`timescale 1ns / 1ps

module apb_master #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int PPROT_WIDTH     = 3,
    parameter int CMD_DEPTH       = 6,
    parameter int RSP_DEPTH       = 6,
    parameter int STRB_WIDTH      = DATA_WIDTH / 8,
    parameter int IDLE_CNTR_WIDTH = 4,  // Default width of idle counter
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PPROT_WIDTH,
    parameter int ICW = IDLE_CNTR_WIDTH,
    parameter int CAW = $clog2(CMD_DEPTH),
    parameter int CPW = AW + DW + SW + PW + 1, // verilog_lint: waive line-length
    parameter int RPW = DW + 1
) (
    // Clock and Reset
    input  logic              pclk,
    input  logic              presetn,

    // Configs
    input logic               i_cfg_cg_enable,     // Global clock gate enable
    input logic  [ICW-1:0]    i_cfg_cg_idle_count, // Idle countdown value

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

    // local clock gating signals
    logic  r_wakeup;
    logic  cg_pclk;

    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn)
            r_wakeup <= 1'b1;
        else
            r_wakeup <= s_apb_PSEL || o_cmd_valid || i_rsp_valid || (r_apb_state == BUSY);
    end

    // Load command packet signals
    logic                r_cmd_valid;
    logic                w_cmd_ready;
    logic [CPW-1:0]      r_cmd_data_in;
    logic [CPW-1:0]      r_cmd_data_zeroes;
    logic [CAW-1:0]      w_cmd_count;

    logic [DW-1:0]       r_cmd_pwdata;
    logic [AW-1:0]       r_cmd_paddr;
    logic [SW-1:0]       r_cmd_pstrb;
    logic [2:0]          r_cmd_pprot;
    logic                r_cmd_pwrite;
    logic                r_cmd_first;
    logic                r_cmd_last;

    assign r_cmd_data_zeroes = 'b0;
    assign {r_cmd_last, r_cmd_first, r_cmd_pwrite, r_cmd_pprot, r_cmd_pstrb, r_cmd_paddr,
            r_cmd_pwdata} = r_cmd_valid ? r_cmd_data : r_cmd_data_zeroes;

    axi_skid_buffer #(
        .DATA_WIDTH(CPW),
        .DEPTH(CMD_DEPTH)
    ) cmd_fifo_inst (
        .i_axi_pclk     (pclk),
        .i_axi_presetn  (presetn),
        .i_wr_valid     (i_cmd_valid),
        .o_wr_ready     (o_cmd_ready),
        .i_wr_data      (i_cmd_data),
        .ow_count       (w_cmd_count),
        .o_rd_valid     (r_cmd_valid),
        .i_rd_ready     (w_cmd_ready),
        .o_rd_data      (r_cmd_data)
    );

    // Extract response packet signals
    logic                w_rsp_valid;
    logic                r_rsp_ready;
    logic [RPW-1:0]      r_rsp_data;
    logic [DW-1:0]       w_rsp_prdata;
    logic                w_rsp_pslverr;

    assign r_rsp_data = {r_cmd_last, r_cmd_first, w_rsp_pslverr, w_rsp_prdata};

    axi_skid_buffer #(
        .DATA_WIDTH(RPW),
        .DEPTH(RSP_DEPTH)
    ) resp_fifo_inst (
        .i_axi_pclk     (pclk),
        .i_axi_presetn  (presetn),
        .i_wr_valid     (w_rsp_valid),
        .o_wr_ready     (r_rsp_ready),
        .i_wr_data      (r_rsp_data),
        .o_rd_valid     (o_rsp_valid),
        .i_rd_ready     (i_rsp_ready),
        .o_rd_data      (o_rsp_data)
    );

    // APB FSM
    typedef enum logic [1:0] {
        IDLE   = 2'b01,
        BUSY = 2'b10
    } apb_state_t;

    apb_state_t r_apb_state, w_apb_next_state;

    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            r_apb_state     <= IDLE;
        end else begin
            r_apb_state     <= w_apb_next_state;
        end
    end

    always_comb begin
        w_apb_next_state   = r_apb_state;
        m_apb_PSEL         = 1'b0;
        m_apb_PENABLE      = 1'b0;
        m_apb_PADDR        = r_cmd_paddr;
        m_apb_PWRITE       = r_cmd_pwrite;
        m_apb_PWDATA       = r_cmd_pwrite ? r_cmd_pwdata : 'b0;
        m_apb_PSTRB        = r_cmd_pstrb;
        m_apb_PPROT        = r_cmd_pprot;
        w_cmd_ready        = 1'b0;
        w_rsp_valid        = 1'b0;
        w_rsp_prdata       = m_apb_PRDATA;
        w_rsp_pslverr      = m_apb_PSLVERR;

        case (r_apb_state)
            IDLE: begin
                if (r_cmd_valid) begin
                    m_apb_PSEL       = 1'b1;
                    w_apb_next_state = BUSY;
                end
            end

            BUSY: begin
                m_apb_PSEL = 1'b1;
                if (r_rsp_ready) begin
                    m_apb_PENABLE = 1'b1;
                    if (m_apb_PREADY) begin
                        w_cmd_ready   = 1'b1;
                        w_rsp_valid   = 1'b1;
                        if (w_cmd_count > 1)
                            w_apb_next_state = BUSY;
                        else
                            w_apb_next_state = IDLE;
                    end
                end
            end

            default: w_apb_next_state = r_apb_state;
        endcase
    end


    clock_gate_ctrl #(
        .IDLE_CNTR_WIDTH(ICW)
    ) u_clock_gate_ctrl (
        .clk_in              (pclk),
        .aresetn             (presetn),
        .i_cfg_cg_enable     (i_cfg_cg_enable),
        .i_cfg_cg_idle_count (i_cfg_cg_idle_count),
        .i_wakeup            (r_wakeup),
        .clk_out             (cg_pclk),
        .o_gating            (o_apb_clock_gating)
    );



endmodule : apb_master
