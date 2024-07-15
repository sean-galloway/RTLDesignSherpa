`timescale 1ns / 1ps

module axi_skid_buffer #(
    parameter int DATA_WIDTH = 32,
    parameter int SKID_DEPTH = 2, // Must be one of {2, 4, 6, 8}
    parameter int DW = DATA_WIDTH,
    parameter int BUF_WIDTH = DATA_WIDTH * SKID_DEPTH,
    parameter int BW = BUF_WIDTH
) (
    // Global Clock and Reset
    input  logic          i_axi_aclk,
    input  logic          i_axi_aresetn,

    // input side
    input  logic          i_wr_valid,
    output logic          o_wr_ready,
    input  logic [DW-1:0] i_wr_data,

    // output side
    output logic          o_rd_valid,
    input  logic          i_rd_ready,
    output logic [3:0]    o_rd_count,
    output logic [3:0]    o_rd_count,
    output logic [DW-1:0] o_rd_data
);

    logic [BW-1:0]        r_data;
    logic [3:0]           r_data_count;
    logic                 w_wr_xfer;
    logic                 w_rd_xfer;

    assign w_wr_xfer = i_wr_valid & o_wr_ready;
    assign w_rd_xfer = o_rd_valid & i_rd_ready;

    always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
        if (~i_axi_aresetn) begin
            r_data <= 'b0;
            r_data_count <= 'b0;
        end else begin
            if (w_wr_xfer & ~w_rd_xfer) begin
                // Shift in new data at the highest available position
                r_data[(DW * r_data_count) +: DW] <= i_wr_data;
                r_data_count <= r_data_count + 1;
            end else if (~w_wr_xfer & w_rd_xfer) begin
                // Shift out old data
                r_data <= {'b0, r_data[BUF_WIDTH-1:DW]};
                r_data_count <= r_data_count - 1;
            end else if (w_wr_xfer & w_rd_xfer) begin
                // Shift in new data and shift out old data
                r_data <= {'b0, r_data[BUF_WIDTH-1:DW]};
                r_data[(DW * (r_data_count - 1)) +: DW] <= i_wr_data;
            end
        end
    end

    always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
        if (~i_axi_aresetn) begin
            o_wr_ready <= 1'b0;
            o_rd_valid <= 1'b0;
        end else begin
            o_wr_ready <= (r_data_count <= SKID_DEPTH-2) || 
                            (r_data_count == SKID_DEPTH-1 && (~w_wr_xfer || w_rd_xfer)) ||
                            (r_data_count == SKID_DEPTH && w_rd_xfer);

            o_rd_valid <= (r_data_count >= 2) || 
                            (r_data_count == 4'b0001 && (~w_rd_xfer || w_wr_xfer)) ||
                            (r_data_count == 4'b0000 && w_wr_xfer);
        end
    end

    assign o_rd_data = r_data[DW-1:0]; // Output the lowest DW bits
    assign o_rd_count = r_data_count;

endmodule : axi_skid_buffer
