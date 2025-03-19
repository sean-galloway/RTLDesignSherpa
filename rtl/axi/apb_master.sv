`timescale 1ns / 1ps

module apb_master #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int PROT_WIDTH      = 3,
    parameter int CMD_DEPTH       = 6,
    parameter int RSP_DEPTH       = 6,
    parameter int STRB_WIDTH      = DATA_WIDTH / 8,
    // Short Parameters
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + 1, // verilog_lint: waive line-length
    parameter int RPW = DW + 1
) (
    // Clock and Reset
    input  logic              pclk,
    input  logic              presetn,

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
    output logic              o_rsp_pslverr
);

    // Command FIFO signals
    logic                r_cmd_valid;
    logic                w_cmd_ready;
    logic [CPW-1:0]      r_cmd_data_in;
    logic [CPW-1:0]      r_cmd_data_out;
    logic [3:0]          w_cmd_count;

    // Unpacked command signals
    logic [DW-1:0]       r_cmd_pwdata;
    logic [AW-1:0]       r_cmd_paddr;
    logic [SW-1:0]       r_cmd_pstrb;
    logic [2:0]          r_cmd_pprot;
    logic                r_cmd_pwrite;

    // Pack command inputs into a single data word
    assign r_cmd_data_in = {i_cmd_pwrite, i_cmd_pprot, i_cmd_pstrb, i_cmd_paddr, i_cmd_pwdata};

    // Unpack command data for use in the APB interface
    assign {r_cmd_pwrite, r_cmd_pprot, r_cmd_pstrb, r_cmd_paddr, r_cmd_pwdata} = r_cmd_data_out;

    // Command FIFO instance
    gaxi_skid_buffer #(
        .DATA_WIDTH(CPW),
        .DEPTH(CMD_DEPTH)
    ) cmd_fifo_inst (
        .i_axi_aclk     (pclk),
        .i_axi_aresetn  (presetn),
        .i_wr_valid     (i_cmd_valid),
        .o_wr_ready     (o_cmd_ready),
        .i_wr_data      (r_cmd_data_in),
        .ow_count       (w_cmd_count),
        .o_rd_valid     (r_cmd_valid),
        .i_rd_ready     (w_cmd_ready),
        .o_rd_data      (r_cmd_data_out)
    );

    // Response FIFO signals
    logic                w_rsp_valid;
    logic                r_rsp_ready;
    logic [RPW-1:0]      r_rsp_data_in;

    // Pack response data for the FIFO
    assign r_rsp_data_in = {m_apb_PSLVERR, m_apb_PRDATA};

    // Response FIFO instance
    gaxi_skid_buffer #(
        .DATA_WIDTH(RPW),
        .DEPTH(RSP_DEPTH)
    ) resp_fifo_inst (
        .i_axi_aclk     (pclk),
        .i_axi_aresetn  (presetn),
        .i_wr_valid     (w_rsp_valid),
        .o_wr_ready     (r_rsp_ready),
        .i_wr_data      (r_rsp_data_in),
        .o_rd_valid     (o_rsp_valid),
        .i_rd_ready     (i_rsp_ready),
        .o_rd_data      ({o_rsp_pslverr, o_rsp_prdata})
    );

    // APB FSM
    typedef enum logic [2:0] {
        IDLE = 3'b001,
        SETUP = 3'b010,
        ACCESS = 3'b100
    } apb_state_t;

    apb_state_t r_apb_state, w_apb_next_state;

    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            r_apb_state <= IDLE;
        end else begin
            r_apb_state <= w_apb_next_state;
        end
    end

    always_comb begin
        // Default assignments
        w_apb_next_state = r_apb_state;
        m_apb_PSEL = 1'b0;
        m_apb_PENABLE = 1'b0;
        m_apb_PADDR = r_cmd_paddr;
        m_apb_PWRITE = r_cmd_pwrite;
        m_apb_PWDATA = r_cmd_pwdata;
        m_apb_PSTRB = r_cmd_pstrb;
        m_apb_PPROT = r_cmd_pprot;
        w_cmd_ready = 1'b0;
        w_rsp_valid = 1'b0;

        casez (r_apb_state)
            IDLE: begin
                // Start transaction if there's a valid command
                if (r_cmd_valid) begin
                    m_apb_PSEL = 1'b1;
                    w_apb_next_state = SETUP;
                end
            end

            SETUP: begin
                // Setup phase - assert PSEL without PENABLE
                m_apb_PSEL = 1'b1;

                // Always move to ACCESS phase
                w_apb_next_state = ACCESS;
            end

            ACCESS: begin
                // Access phase - assert both PSEL and PENABLE
                m_apb_PSEL = 1'b1;
                m_apb_PENABLE = 1'b1;

                // Wait for slave to respond with PREADY
                if (m_apb_PREADY) begin
                    // For read operations, store the response
                    if (!r_cmd_pwrite) begin
                        // Only write to response FIFO if it's ready
                        if (r_rsp_ready) begin
                            w_rsp_valid = 1'b1;
                            w_cmd_ready = 1'b1;

                            // Go back to IDLE or directly start a new transaction
                            if (w_cmd_count > 1 && r_cmd_valid)
                                w_apb_next_state = SETUP;
                            else
                                w_apb_next_state = IDLE;
                        end
                    else
                        // Response FIFO not ready, stay in ACCESS state
                        w_apb_next_state = ACCESS;
                    end
                    else begin
                        // For write operations, just complete the transaction
                        w_cmd_ready = 1'b1;

                        // Go back to IDLE or directly start a new transaction
                        if (w_cmd_count > 1 && r_cmd_valid)
                            w_apb_next_state = SETUP;
                        else
                            w_apb_next_state = IDLE;
                    end
                end
            end

            default: w_apb_next_state = IDLE;
        endcase
    end

endmodule : apb_master
