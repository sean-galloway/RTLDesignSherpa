`timescale 1ns / 1ps

// Generic Slave module to prove out maximal performance
module axi_skid_buffer_async #(
    parameter int DATA_WIDTH          = 32,
    parameter int DEPTH               = 2,
    parameter int ENABLE_EMPTY_BYPASS = 0 // go combinatorially around the fifo if empty
) (
    // Global Clock and Reset
    input  logic            i_axi_wr_aclk,
                            i_axi_wr_aresetn,
                            i_axi_rd_aclk,
                            i_axi_rd_aresetn,

    // input side
    input  logic          i_wr_valid,
    output logic          o_wr_ready,
    input  logic [DW-1:0] i_wr_data,

    // output side
    output logic          o_rd_valid,
    input  logic          i_rd_ready,
    output logic [DW-1:0] o_rd_data
);

    localparam int DW = DATA_WIDTH;

    logic            w_wr_valid;
    logic            w_wr_ready;   // not full
    logic [DW-1:0]   w_wr_data;
    logic            w_rd_ready;
    logic            w_rd_valid;   // not empty
    logic [DW-1:0]   w_rd_data;
    logic            w_bypass_taken;

    always_comb begin
        w_bypass_taken = 0;
        if ((ENABLE_EMPTY_BYPASS) &&
            (~w_rd_valid && i_rd_ready)) begin // fifo empty and ready to receive, go around it
                w_wr_valid     = 'b0;
                o_wr_ready     = 'b1;
                w_wr_data      = 'b0;
                w_rd_ready     = 'b0;
                o_rd_valid     = i_wr_valid;
                o_rd_data      = i_wr_data;
                w_bypass_taken = 'b1;

        end else begin  // not enabled at all, just connect up the queue
            w_wr_valid = i_wr_valid;
            w_wr_data  = i_wr_data;
            o_wr_ready = w_wr_ready;

            o_rd_valid = w_rd_valid;
            w_rd_ready = i_rd_ready;
            o_rd_data  = w_rd_data;
        end
    end

    fifo_axi_async #(.DEL(1), .DATA_WIDTH(DW), .DEPTH(DEPTH)) skid_fifo_inst (
        .i_axi_wr_aclk    (i_axi_wr_aclk),
        .i_axi_wr_aresetn (i_axi_wr_aresetn),
        .i_axi_rd_aclk    (i_axi_rd_aclk),
        .i_axi_rd_aresetn (i_axi_rd_aresetn),
        .i_wr_valid       (w_wr_valid),
        .o_wr_ready       (w_wr_ready),   // not full
        .i_wr_data        (w_wr_data),
        .i_rd_ready       (w_rd_ready),
        .o_rd_valid       (w_rd_valid),   // not empty
        .ow_rd_data       (w_rd_data),
        .o_rd_data        ()
    );

endmodule : axi_skid_buffer_async
