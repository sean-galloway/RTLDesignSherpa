`timescale 1ns / 1ps

module apb_master_stub #(
    parameter int CMD_DEPTH         = 6,
    parameter int RSP_DEPTH         = 6,
    parameter int DATA_WIDTH        = 32,
    parameter int ADDR_WIDTH        = 32,
    parameter int STRB_WIDTH        = DATA_WIDTH / 8,
    parameter int CMD_PACKET_WIDTH  = ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + 3 + 1 + 1 + 1,
                                        // addr, data, strb, prot, pwrite, first, last
    parameter int RESP_PACKET_WIDTH = DATA_WIDTH + 1 + 1 +  1, // data, pslverr, first, last
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int CPW = CMD_PACKET_WIDTH,
    parameter int RPW = RESP_PACKET_WIDTH,
    parameter int CAW = $clog2(CMD_DEPTH)
) (
    // Clock and Reset
    input  logic                         pclk,
    input  logic                         presetn,

    // APB interface
    output logic                         m_apb_PSEL,
    output logic                         m_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0]        m_apb_PADDR,
    output logic                         m_apb_PWRITE,
    output logic [DATA_WIDTH-1:0]        m_apb_PWDATA,
    output logic [STRB_WIDTH-1:0]        m_apb_PSTRB,
    output logic [2:0]                   m_apb_PPROT,
    input  logic [DATA_WIDTH-1:0]        m_apb_PRDATA,
    input  logic                         m_apb_PSLVERR,
    input  logic                         m_apb_PREADY,

    // Command Packet
    input  logic                         cmd_valid,
    output logic                         cmd_ready,
    input  logic [CMD_PACKET_WIDTH-1:0]  cmd_data,

    // Read Return interface
    output logic                         rsp_valid,
    input  logic                         rsp_ready,
    output logic [RESP_PACKET_WIDTH-1:0] rsp_data
);

    // Load command packet signals
    logic                r_cmd_valid;
    logic                w_cmd_ready;
    logic [CPW-1:0]      r_cmd_data;
    logic [CPW-1:0]      r_cmd_data_zeroes;
    logic [3:0]          w_cmd_count;

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

    gaxi_skid_buffer #(
        .DATA_WIDTH   (CPW),
        .DEPTH        (CMD_DEPTH)
    ) cmd_fifo_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (cmd_valid),
        .wr_ready     (cmd_ready),
        .wr_data      (cmd_data),
        .count        (w_cmd_count),
        .rd_valid     (r_cmd_valid),
        .rd_ready     (w_cmd_ready),
        .rd_data      (r_cmd_data),
        .rd_count     ()
    );

    // Extract response packet signals
    logic                w_rsp_valid;
    logic                r_rsp_ready;
    logic [RPW-1:0]      r_rsp_data;
    logic [DW-1:0]       w_rsp_prdata;
    logic                w_rsp_pslverr;

    assign r_rsp_data = {r_cmd_last, r_cmd_first, w_rsp_pslverr, w_rsp_prdata};

    gaxi_skid_buffer #(
        .DATA_WIDTH   (RPW),
        .DEPTH        (RSP_DEPTH)
    ) resp_fifo_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (w_rsp_valid),
        .wr_ready     (r_rsp_ready),
        .wr_data      (r_rsp_data),
        .rd_valid     (rsp_valid),
        .rd_ready     (rsp_ready),
        .rd_data      (rsp_data),
        .count        (),
        .rd_count     ()
    );

    // APB FSM
    typedef enum logic [1:0] {
        IDLE   = 2'b01,
        ACTIVE = 2'b10
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
                    w_apb_next_state = ACTIVE;
                end
            end

            ACTIVE: begin
                m_apb_PSEL = 1'b1;
                if (r_rsp_ready) begin
                    m_apb_PENABLE = 1'b1;
                    if (m_apb_PREADY) begin
                        w_cmd_ready   = 1'b1;
                        w_rsp_valid   = 1'b1;
                        if (w_cmd_count > 1)
                            w_apb_next_state = ACTIVE;
                        else
                            w_apb_next_state = IDLE;
                    end
                end
            end

            default: w_apb_next_state = r_apb_state;
        endcase
    end

endmodule : apb_master_stub
