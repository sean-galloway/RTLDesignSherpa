`timescale 1ns / 1ps

module apb_master_stub #(
    parameter int DATA_WIDTH    = 32,
    parameter int ADDR_WIDTH    = 32,
    parameter int STRB_WIDTH    = DATA_WIDTH / 8,
    parameter int CMD_PACKET_WIDTH = ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + 4, // addr, data, strb, prot, pwrite
    parameter int RESP_PACKET_WIDTH = DATA_WIDTH + 2 // data, resp
) (
    // Clock and Reset
    input  logic                         aclk,
    input  logic                         aresetn,

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
    input  logic                         i_cmd_valid,
    output logic                         o_cmd_ready,
    input  logic [CMD_PACKET_WIDTH-1:0]  i_cmd_data,

    // Read Return interface
    output logic                         o_rsp_valid,
    input  logic                         i_rsp_ready,
    output logic [RESP_PACKET_WIDTH-1:0] o_rsp_data
);

    localparam int DW  = DATA_WIDTH;
    localparam int AW  = ADDR_WIDTH;
    localparam int SW  = STRB_WIDTH;
    localparam int CPW = CMD_PACKET_WIDTH;
    localparam int RPW = RESP_PACKET_WIDTH;

    // Load command packet signals
    logic                r_cmd_valid;
    logic                r_cmd_ready;
    logic [CPW-1:0]      r_cmd_data;
    // Register to store current command packet
    logic [CPW-1:0]      r_curr_cmd_pkt;
    logic                r_curr_cmd_valid;

    logic [DW-1:0]       r_cmd_pwdata;
    logic [AW-1:0]       r_cmd_paddr;
    logic [SW-1:0]       r_cmd_pstrb;
    logic [2:0]          r_cmd_pprot;
    logic                r_cmd_pwrite;

    logic [DW-1:0]       re_cmd_pwdata;
    logic [AW-1:0]       re_cmd_paddr;
    logic [SW-1:0]       re_cmd_pstrb;
    logic [2:0]          re_cmd_pprot;
    logic                re_cmd_pwrite;

    assign {re_cmd_pwrite, re_cmd_pprot, re_cmd_pstrb, re_cmd_paddr, re_cmd_pwdata} = r_cmd_data;
    assign {r_cmd_pwrite, r_cmd_pprot, r_cmd_pstrb, r_cmd_paddr, r_cmd_pwdata} = (r_apb_state == IDLE) ?
                                    r_cmd_data : r_curr_cmd_pkt;

    axi_skid_buffer #(
        .DATA_WIDTH(CPW)
    ) cmd_skid_buffer_inst (
        .i_axi_aclk     (aclk),
        .i_axi_aresetn  (aresetn),
        .i_wr_valid     (i_cmd_valid),
        .o_wr_ready     (o_cmd_ready),
        .i_wr_data      (i_cmd_data),
        .o_rd_valid     (r_cmd_valid),
        .i_rd_ready     (r_cmd_ready),
        .o_rd_data      (r_cmd_data)
    );

    // Extract response packet signals
    logic                r_rsp_valid;
    logic                r_rsp_ready;
    logic [RPW-1:0]      r_rsp_data;
    logic [DW-1:0]       r_rsp_prdata;
    logic [1:0]          r_rsp_pslverr;

    assign r_rsp_data = {r_rsp_pslverr, r_rsp_prdata};

    axi_skid_buffer #(
        .DATA_WIDTH(RPW)
    ) resp_skid_buffer_inst (
        .i_axi_aclk     (aclk),
        .i_axi_aresetn  (aresetn),
        .i_wr_valid     (r_rsp_valid),
        .o_wr_ready     (r_rsp_ready),
        .i_wr_data      (r_rsp_data),
        .o_rd_valid     (o_rsp_valid),
        .i_rd_ready     (i_rsp_ready),
        .o_rd_data      (o_rsp_data)
    );

    // APB FSM
    typedef enum logic [2:0] {
        IDLE  = 3'b001,
        READ  = 3'b010,
        WRITE = 3'b100
    } apb_state_t;

    apb_state_t r_apb_state, w_apb_next_state;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_apb_state     <= IDLE;
            r_curr_cmd_valid <= 1'b0;
        end else begin
            r_apb_state     <= w_apb_next_state;
            if (r_cmd_ready && r_cmd_valid) begin
                r_curr_cmd_pkt <= r_cmd_data;
            end
        end
    end

    always_comb begin
        w_apb_next_state   = r_apb_state;
        m_apb_PSEL         = 1'b0;
        m_apb_PENABLE      = 1'b0;
        m_apb_PADDR        = r_cmd_paddr;
        m_apb_PWRITE       = r_cmd_pwrite;
        m_apb_PWDATA       = r_cmd_pwdata;
        m_apb_PSTRB        = r_cmd_pstrb;
        m_apb_PPROT        = r_cmd_pprot;
        r_cmd_ready        = 1'b0;
        r_rsp_valid        = 1'b0;
        r_rsp_prdata       = m_apb_PRDATA;
        r_rsp_pslverr      = m_apb_PSLVERR;

        case (r_apb_state)
            IDLE: begin
                if (r_cmd_valid) begin
                    m_apb_PSEL   = 1'b1;
                    r_cmd_ready  = 1'b1;
                    if (r_cmd_pwrite) begin
                        w_apb_next_state = WRITE;
                    end else begin
                        w_apb_next_state = READ;
                    end
                end
            end

            READ: begin
                m_apb_PSEL    = 1'b1;
                m_apb_PENABLE = 1'b1;
                if (m_apb_PREADY) begin
                    r_rsp_valid = 1'b1;
                    if (r_cmd_valid) begin
                        r_cmd_ready = 1'b1;
                        if (re_cmd_pwrite) begin
                            w_apb_next_state = WRITE;
                        end else begin
                            w_apb_next_state = READ;
                        end
                    end else begin
                        w_apb_next_state = IDLE;
                    end
                end
            end

            WRITE: begin
                m_apb_PSEL    = 1'b1;
                m_apb_PENABLE = 1'b1;
                if (m_apb_PREADY) begin
                    if (r_cmd_valid) begin
                        r_cmd_ready = 1'b1;
                        if (re_cmd_pwrite) begin
                            w_apb_next_state = WRITE;
                        end else begin
                            w_apb_next_state = READ;
                        end
                    end else begin
                        w_apb_next_state = IDLE;
                    end
                end
            end

            default: w_apb_next_state = r_apb_state;
        endcase
    end

endmodule : apb_master_stub
