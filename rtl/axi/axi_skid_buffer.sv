`timescale 1ns / 1ps

// AXI Skid buffer where all ports are driven or received by a flop
module axi_skid_buffer #(
    parameter int DATA_WIDTH = 32
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
    output logic [DW-1:0] o_rd_data
);

    localparam int DW = DATA_WIDTH;

    logic           r_wr_ready;
    logic           r_rd_valid;
    logic           w_wr_xfer;
    logic           w_rd_xfer;
    logic [1:0]     r_data_count;
    logic [DW-1:0]  r_data, r_skid_data;

    assign w_wr_xfer = i_wr_valid & o_wr_ready;
    assign w_rd_xfer = o_rd_valid & i_rd_ready;

    always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
        if (~i_axi_aresetn) begin
            r_wr_ready <= 'b0;
            r_rd_valid <= 'b0;
        end else begin
            r_wr_ready <= (r_data_count == 2'b00) ? 1'b1:
                            (r_data_count == 2'b01) ? ~w_wr_xfer : r_wr_ready;

            case (r_data_count)
                2'b00: r_rd_valid <= w_wr_xfer;
                2'b01: begin
                    if (w_wr_xfer)
                        r_rd_valid <= 1'b1;
                    else if (~w_wr_xfer & w_rd_xfer)
                        r_rd_valid <= 1'b0;
                    else
                        r_rd_valid <= r_rd_valid;
                end
                2'b10: r_rd_valid <= 1'b1;
                default: r_rd_valid <= r_rd_valid;
            endcase
        end
    end

    always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
        if (~i_axi_aresetn) begin
            r_data_count <= 'b0;
        end else begin
            if (w_wr_xfer & w_rd_xfer)
                r_data_count <= r_data_count;
            else if (w_wr_xfer)
                r_data_count <= r_data_count + 2'b01;
            else if (w_rd_xfer)
                r_data_count <= r_data_count - 2'b01;
        end
    end

    always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
        if (~i_axi_aresetn) begin
            r_data <= 'b0;
        end else begin
            case (r_data_count)
                2'b00: r_data <= i_wr_data;
                2'b01: r_data <= (w_rd_xfer) ? i_wr_data   : r_skid_data;
                2'b10: r_data <= (w_rd_xfer) ? r_skid_data : r_data;
                default: r_data <= r_data;
            endcase
        end
    end

    always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
        if (~i_axi_aresetn) begin
            r_skid_data <= 'b0;
        end else begin
            if (w_wr_xfer) begin
                r_skid_data  <= i_wr_data;
            end
        end
    end

    assign o_wr_ready = r_wr_ready;
    assign o_rd_valid = r_rd_valid;
    assign o_rd_data  = r_data;

endmodule : axi_skid_buffer
