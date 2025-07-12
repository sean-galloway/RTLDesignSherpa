`timescale 1ns / 1ps

module apb_slave #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int STRB_WIDTH      = 32 / 8,
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
    input  logic              rsp_pslverr
);

    // Load command packet signals
    logic                r_cmd_valid;
    logic                r_cmd_ready;
    logic                r_cmd_ready_pre;
    logic [CPW-1:0]      r_cmd_data_in;
    logic [CPW-1:0]      r_cmd_data_out;
    logic [3:0]          r_cmd_count;

    assign r_cmd_data_in = { s_apb_PWRITE, s_apb_PPROT, s_apb_PSTRB, s_apb_PADDR, s_apb_PWDATA};
    assign {cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata} = r_cmd_data_out;

    gaxi_skid_buffer #(
        .DEPTH(DEPTH),
        .DATA_WIDTH(CPW)
    ) cmd_skid_buffer_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (r_cmd_valid),
        .wr_ready     (r_cmd_ready),
        .wr_data      (r_cmd_data_in),
        .rd_valid     (cmd_valid),
        .rd_ready     (cmd_ready),
        .rd_data      (r_cmd_data_out),
        .count       (r_cmd_count),
        .rd_count     ()
    );

    // Extract response packet signals
    logic                r_rsp_valid;
    logic                r_rsp_ready;
    logic [RPW-1:0]      r_rsp_data_in;
    logic [DW-1:0]       r_rsp_prdata;
    logic                r_rsp_pslverr;
    logic [RPW-1:0]      r_rsp_data_out;
    logic [3:0]          r_rsp_count;

    assign {r_rsp_pslverr, r_rsp_prdata} = r_rsp_data_out;
    assign r_rsp_data_in = {rsp_pslverr, rsp_prdata};

    gaxi_skid_buffer #(
        .DEPTH(DEPTH),
        .DATA_WIDTH(RPW)
    ) resp_skid_buffer_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (rsp_valid),
        .wr_ready     (rsp_ready),
        .wr_data      (r_rsp_data_in),
        .rd_valid     (r_rsp_valid),
        .rd_ready     (r_rsp_ready),
        .rd_data      (r_rsp_data_out),
        .count       (r_rsp_count),
        .rd_count     ()
    );

    // APB FSM
    typedef enum logic [2:0] {
        IDLE = 3'b001,
        BUSY = 3'b010,
        WAIT = 3'b100
    } apb_state_t;

    apb_state_t r_apb_state;

    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            r_apb_state   <= IDLE;
            s_apb_PREADY  <= 'b0;
            s_apb_PSLVERR <= 'b0;
            s_apb_PRDATA  <= 'b0;
            r_cmd_valid   <= 1'b0;
            r_rsp_ready   <= 1'b0;
        end else begin
            // default states
            r_apb_state <= r_apb_state;
            s_apb_PREADY  <= 'b0;
            s_apb_PSLVERR <= 'b0;
            s_apb_PRDATA  <= 'b0;
            r_cmd_valid   <= 1'b0;
            r_rsp_ready   <= 1'b0;

            casez (r_apb_state)

                IDLE: begin
                    if (s_apb_PSEL && s_apb_PENABLE && r_cmd_ready) begin
                        r_cmd_valid <= 1'b1;
                        r_apb_state <= BUSY;
                    end
                end

                BUSY: begin
                    if (r_rsp_valid) begin
                        s_apb_PREADY   <= 1'b1;
                        s_apb_PRDATA   <= r_rsp_prdata;
                        s_apb_PSLVERR  <= r_rsp_pslverr;
                        r_rsp_ready    <= 1'b1;
                        r_apb_state    <= WAIT;
                    end
                end
                WAIT: r_apb_state <= IDLE;

                default: r_apb_state <= IDLE;

            endcase
        end
    end

endmodule : apb_slave
