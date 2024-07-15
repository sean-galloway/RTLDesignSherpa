`timescale 1ns / 1ps

// AXI Skid buffer where all ports are driven or received by a flop
module axi_skid_buffer #(
    parameter int DATA_WIDTH = 32,
    parameter int SKID4 = 0,
    parameter int SKID6 = 0,
    parameter int SKID8 = 0,
    parameter int DW = DATA_WIDTH
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
    output logic [DW-1:0] o_rd_data
);
    logic           r_wr_ready;
    logic           r_rd_valid;
    logic           w_wr_xfer;
    logic           w_rd_xfer;
    logic           w_no_xfer;
    logic [3:0]     r_data_count;
    logic [DW-1:0]  r_data;
    logic [DW-1:0]  r_skid_data1, r_skid_data2, r_skid_data3, r_skid_data4, r_skid_data5, r_skid_data6, r_skid_data7;

    assign w_wr_xfer = i_wr_valid & o_wr_ready;
    assign w_rd_xfer = o_rd_valid & i_rd_ready;
    assign w_no_xfer = ~w_wr_xfer && ~w_rd_xfer;

    generate
        if (SKID8) begin : gen_skid8_buffer
            // Eight-deep skid buffer
            always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
                if (~i_axi_aresetn) begin
                    r_wr_ready <= 'b0;
                    r_rd_valid <= 'b0;
                    r_data_count <= 'b0;
                    r_data <= 'b0;
                    r_skid_data1 <= 'b0;
                    r_skid_data2 <= 'b0;
                    r_skid_data3 <= 'b0;
                    r_skid_data4 <= 'b0;
                    r_skid_data5 <= 'b0;
                    r_skid_data6 <= 'b0;
                    r_skid_data7 <= 'b0;
                end else begin
                    r_wr_ready <= (r_data_count == 4'b0000) ||
                                  (r_data_count == 4'b0001) ||
                                  (r_data_count == 4'b0010) ||
                                  (r_data_count == 4'b0011) ||
                                  (r_data_count == 4'b0100) ||
                                  (r_data_count == 4'b0101) ||
                                  (r_data_count == 4'b0110) ||
                                  (r_data_count == 4'b0111 && (~w_wr_xfer || w_rd_xfer)) ||
                                  (r_data_count == 4'b1000 && w_rd_xfer);

                    r_rd_valid <= (r_data_count == 4'b1000) ||
                                  (r_data_count == 4'b0111) ||
                                  (r_data_count == 4'b0110) ||
                                  (r_data_count == 4'b0101) ||
                                  (r_data_count == 4'b0100) ||
                                  (r_data_count == 4'b0011) ||
                                  (r_data_count == 4'b0010) ||
                                  (r_data_count == 4'b0001 && (~w_rd_xfer || w_wr_xfer)) ||
                                  (r_data_count == 4'b0000 && w_wr_xfer);

                    if (w_wr_xfer & ~w_rd_xfer) begin
                        r_data_count <= r_data_count + 4'b0001;
                    end else if (~w_wr_xfer & w_rd_xfer) begin
                        r_data_count <= r_data_count - 4'b0001;
                    end

                    case (r_data_count)
                        4'b0000:  r_data <= (w_wr_xfer) ? i_wr_data    : r_data;
                        4'b0001:  r_data <= (w_rd_xfer) ? i_wr_data    : r_data;
                        4'b0010:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        4'b0011:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        4'b0100:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        4'b0101:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        4'b0110:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        4'b0111:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        4'b1000:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        default:  r_data <= r_data;
                    endcase

                    case (r_data_count)
                        4'b0000:  r_skid_data1 <= (w_wr_xfer) ? i_wr_data    : r_skid_data1;
                        4'b0001:  r_skid_data1 <= (w_no_xfer) ? r_skid_data1 : i_wr_data;
                        4'b0010:  begin
                                    if (w_wr_xfer && w_rd_xfer)
                                        r_skid_data1 <= i_wr_data;
                                    else
                                        r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                                  end
                        4'b0011:  r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                        4'b0100:  r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                        4'b0101:  r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                        4'b0110:  r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                        4'b0111:  r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                        4'b1000:  r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                        default:  r_skid_data1 <= r_skid_data1;
                    endcase

                    case (r_data_count)
                        4'b0000:  r_skid_data2 <= (w_wr_xfer) ? i_wr_data    : r_skid_data2;
                        4'b0001:  r_skid_data2 <= (w_no_xfer) ? r_skid_data2 : i_wr_data;
                        4'b0010:  r_skid_data2 <= (w_wr_xfer) ? i_wr_data    : r_skid_data2;
                        4'b0011:  r_skid_data2 <= (w_rd_xfer) ? i_wr_data    : r_skid_data2;
                        4'b0100:  r_skid_data2 <= (w_rd_xfer) ? r_skid_data3 : r_skid_data2;
                        4'b0101:  r_skid_data2 <= (w_rd_xfer) ? r_skid_data3 : r_skid_data2;
                        4'b0110:  r_skid_data2 <= (w_rd_xfer) ? r_skid_data3 : r_skid_data2;
                        4'b0111:  r_skid_data2 <= (w_rd_xfer) ? r_skid_data3 : r_skid_data2;
                        4'b1000:  r_skid_data2 <= (w_rd_xfer) ? r_skid_data3 : r_skid_data2;
                        default:  r_skid_data2 <= r_skid_data2;
                    endcase

                    case (r_data_count)
                        4'b0000:  r_skid_data3 <= (w_wr_xfer) ? i_wr_data    : r_skid_data3;
                        4'b0001:  r_skid_data3 <= (w_no_xfer) ? r_skid_data3 : i_wr_data;
                        4'b0010:  r_skid_data3 <= (w_wr_xfer) ? i_wr_data    : r_skid_data3;
                        4'b0011:  r_skid_data3 <= (w_rd_xfer) ? i_wr_data    : r_skid_data3;
                        4'b0100:  r_skid_data3 <= (w_rd_xfer) ? r_skid_data4 : r_skid_data3;
                        4'b0101:  r_skid_data3 <= (w_rd_xfer) ? r_skid_data4 : r_skid_data3;
                        4'b0110:  r_skid_data3 <= (w_rd_xfer) ? r_skid_data4 : r_skid_data3;
                        4'b0111:  r_skid_data3 <= (w_rd_xfer) ? r_skid_data4 : r_skid_data3;
                        4'b1000:  r_skid_data3 <= (w_rd_xfer) ? r_skid_data4 : r_skid_data3;
                        default:  r_skid_data3 <= r_skid_data3;
                    endcase

                    case (r_data_count)
                        4'b0000:  r_skid_data4 <= (w_wr_xfer) ? i_wr_data    : r_skid_data4;
                        4'b0001:  r_skid_data4 <= (w_no_xfer) ? r_skid_data4 : i_wr_data;
                        4'b0010:  r_skid_data4 <= (w_wr_xfer) ? i_wr_data    : r_skid_data4;
                        4'b0011:  r_skid_data4 <= (w_rd_xfer) ? i_wr_data    : r_skid_data4;
                        4'b0100:  r_skid_data4 <= (w_rd_xfer) ? r_skid_data5 : r_skid_data4;
                        4'b0101:  r_skid_data4 <= (w_rd_xfer) ? r_skid_data5 : r_skid_data4;
                        4'b0110:  r_skid_data4 <= (w_rd_xfer) ? r_skid_data5 : r_skid_data4;
                        4'b0111:  r_skid_data4 <= (w_rd_xfer) ? r_skid_data5 : r_skid_data4;
                        4'b1000:  r_skid_data4 <= (w_rd_xfer) ? r_skid_data5 : r_skid_data4;
                        default:  r_skid_data4 <= r_skid_data4;
                    endcase

                    case (r_data_count)
                        4'b0000:  r_skid_data5 <= (w_wr_xfer) ? i_wr_data    : r_skid_data5;
                        4'b0001:  r_skid_data5 <= (w_no_xfer) ? r_skid_data5 : i_wr_data;
                        4'b0010:  r_skid_data5 <= (w_wr_xfer) ? i_wr_data    : r_skid_data5;
                        4'b0011:  r_skid_data5 <= (w_rd_xfer) ? i_wr_data    : r_skid_data5;
                        4'b0100:  r_skid_data5 <= (w_rd_xfer) ? r_skid_data6 : r_skid_data5;
                        4'b0101:  r_skid_data5 <= (w_rd_xfer) ? r_skid_data6 : r_skid_data5;
                        4'b0110:  r_skid_data5 <= (w_rd_xfer) ? r_skid_data6 : r_skid_data5;
                        4'b0111:  r_skid_data5 <= (w_rd_xfer) ? r_skid_data6 : r_skid_data5;
                        4'b1000:  r_skid_data5 <= (w_rd_xfer) ? r_skid_data6 : r_skid_data5;
                        default:  r_skid_data5 <= r_skid_data5;
                    endcase

                    case (r_data_count)
                        4'b0000:  r_skid_data6 <= (w_wr_xfer) ? i_wr_data    : r_skid_data6;
                        4'b0001:  r_skid_data6 <= (w_no_xfer) ? r_skid_data6 : i_wr_data;
                        4'b0010:  r_skid_data6 <= (w_wr_xfer) ? i_wr_data    : r_skid_data6;
                        4'b0011:  r_skid_data6 <= (w_rd_xfer) ? i_wr_data    : r_skid_data6;
                        4'b0100:  r_skid_data6 <= (w_rd_xfer) ? r_skid_data7 : r_skid_data6;
                        4'b0101:  r_skid_data6 <= (w_rd_xfer) ? r_skid_data7 : r_skid_data6;
                        4'b0110:  r_skid_data6 <= (w_rd_xfer) ? r_skid_data7 : r_skid_data6;
                        4'b0111:  r_skid_data6 <= (w_rd_xfer) ? r_skid_data7 : r_skid_data6;
                        4'b1000:  r_skid_data6 <= (w_rd_xfer) ? r_skid_data7 : r_skid_data6;
                        default:  r_skid_data6 <= r_skid_data6;
                    endcase

                    if (w_wr_xfer)
                        r_skid_data7 <= i_wr_data;
                end
            end
        end else if (SKID6) begin : gen_skid6_buffer
            // Six-deep skid buffer
            always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
                if (~i_axi_aresetn) begin
                    r_wr_ready <= 'b0;
                    r_rd_valid <= 'b0;
                    r_data_count <= 'b0;
                    r_data <= 'b0;
                    r_skid_data1 <= 'b0;
                    r_skid_data2 <= 'b0;
                    r_skid_data3 <= 'b0;
                    r_skid_data4 <= 'b0;
                    r_skid_data5 <= 'b0;
                end else begin
                    r_wr_ready <= (r_data_count == 3'b000) ||
                                  (r_data_count == 3'b001) ||
                                  (r_data_count == 3'b010) ||
                                  (r_data_count == 3'b011) ||
                                  (r_data_count == 3'b100) ||
                                  (r_data_count == 3'b101 && (~w_wr_xfer || w_rd_xfer)) ||
                                  (r_data_count == 3'b110 && w_rd_xfer);

                    r_rd_valid <= (r_data_count == 3'b110) ||
                                  (r_data_count == 3'b101) ||
                                  (r_data_count == 3'b100) ||
                                  (r_data_count == 3'b011) ||
                                  (r_data_count == 3'b010) ||
                                  (r_data_count == 3'b001 && (~w_rd_xfer || w_wr_xfer)) ||
                                  (r_data_count == 3'b000 && w_wr_xfer);

                    if (w_wr_xfer & ~w_rd_xfer) begin
                        r_data_count <= r_data_count + 3'b001;
                    end else if (~w_wr_xfer & w_rd_xfer) begin
                        r_data_count <= r_data_count - 3'b001;
                    end

                    case (r_data_count)
                        3'b000:  r_data <= (w_wr_xfer) ? i_wr_data    : r_data;
                        3'b001:  r_data <= (w_rd_xfer) ? i_wr_data    : r_data;
                        3'b010:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        3'b011:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        3'b100:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        3'b101:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        3'b110:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        default: r_data <= r_data;
                    endcase

                    case (r_data_count)
                        3'b000:  r_skid_data1 <= (w_wr_xfer) ? i_wr_data    : r_skid_data1;
                        3'b001:  r_skid_data1 <= (w_no_xfer) ? r_skid_data1 : i_wr_data;
                        3'b010:  begin
                                    if (w_wr_xfer && w_rd_xfer)
                                        r_skid_data1 <= i_wr_data;
                                    else
                                        r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                                  end
                        3'b011:  r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                        3'b100:  r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                        3'b101:  r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                        3'b110:  r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                        default: r_skid_data1 <= r_skid_data1;
                    endcase

                    case (r_data_count)
                         3'b000:  r_skid_data2 <= (w_wr_xfer) ? i_wr_data    : r_skid_data2;
                         3'b001:  r_skid_data2 <= (w_no_xfer) ? r_skid_data2 : i_wr_data;
                         3'b010:  r_skid_data2 <= (w_wr_xfer) ? i_wr_data    : r_skid_data2;
                         3'b011:  r_skid_data2 <= (w_rd_xfer) ? i_wr_data    : r_skid_data2;
                         3'b100:  r_skid_data2 <= (w_rd_xfer) ? r_skid_data3 : r_skid_data2;
                         3'b101:  r_skid_data2 <= (w_rd_xfer) ? r_skid_data3 : r_skid_data2;
                         3'b110:  r_skid_data2 <= (w_rd_xfer) ? r_skid_data3 : r_skid_data2;
                         default: r_skid_data2 <= r_skid_data2;
                    endcase

                    case (r_data_count)
                         3'b000:  r_skid_data3 <= (w_wr_xfer) ? i_wr_data    : r_skid_data3;
                         3'b001:  r_skid_data3 <= (w_no_xfer) ? r_skid_data3 : i_wr_data;
                         3'b010:  r_skid_data3 <= (w_wr_xfer) ? i_wr_data    : r_skid_data3;
                         3'b011:  r_skid_data3 <= (w_rd_xfer) ? i_wr_data    : r_skid_data3;
                         3'b100:  r_skid_data3 <= (w_rd_xfer) ? r_skid_data4 : r_skid_data3;
                         3'b101:  r_skid_data3 <= (w_rd_xfer) ? r_skid_data4 : r_skid_data3;
                         3'b110:  r_skid_data3 <= (w_rd_xfer) ? r_skid_data4 : r_skid_data3;
                         default: r_skid_data3 <= r_skid_data3;
                    endcase

                    case (r_data_count)
                         3'b000:  r_skid_data4 <= (w_wr_xfer) ? i_wr_data    : r_skid_data4;
                         3'b001:  r_skid_data4 <= (w_no_xfer) ? r_skid_data4 : i_wr_data;
                         3'b010:  r_skid_data4 <= (w_wr_xfer) ? i_wr_data    : r_skid_data4;
                         3'b011:  r_skid_data4 <= (w_rd_xfer) ? i_wr_data    : r_skid_data4;
                         3'b100:  r_skid_data4 <= (w_rd_xfer) ? r_skid_data5 : r_skid_data4;
                         3'b101:  r_skid_data4 <= (w_rd_xfer) ? r_skid_data5 : r_skid_data4;
                         3'b110:  r_skid_data4 <= (w_rd_xfer) ? r_skid_data5 : r_skid_data4;
                         default: r_skid_data4 <= r_skid_data4;
                    endcase

                    if (w_wr_xfer)
                        r_skid_data5 <= i_wr_data;
                end
            end
        end else if (SKID4) begin : gen_skid4_buffer
            // Four-deep skid buffer
            always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
                if (~i_axi_aresetn) begin
                    r_wr_ready <= 'b0;
                    r_rd_valid <= 'b0;
                    r_data_count <= 'b0;
                    r_data <= 'b0;
                    r_skid_data1 <= 'b0;
                    r_skid_data2 <= 'b0;
                    r_skid_data3 <= 'b0;
                end else begin
                    r_wr_ready <= (r_data_count == 3'b000) ||
                                    (r_data_count == 3'b001) ||
                                    (r_data_count == 3'b010) ||
                                    (r_data_count == 3'b011 && (~w_wr_xfer || w_rd_xfer)) ||
                                    (r_data_count == 3'b100 && w_rd_xfer);

                    r_rd_valid <= (r_data_count == 3'b100) ||
                                    (r_data_count == 3'b011) ||
                                    (r_data_count == 3'b010) ||
                                    (r_data_count == 3'b001 && (~w_rd_xfer || w_wr_xfer)) ||
                                    (r_data_count == 3'b000 && w_wr_xfer);

                    if (w_wr_xfer & ~w_rd_xfer) begin
                        r_data_count <= r_data_count + 3'b001;
                    end else if (~w_wr_xfer & w_rd_xfer) begin
                        r_data_count <= r_data_count - 3'b001;
                    end

                    case (r_data_count)
                        3'b000:  r_data <= (w_wr_xfer) ? i_wr_data    : r_data;
                        3'b001:  r_data <= (w_rd_xfer) ? i_wr_data    : r_data;
                        3'b010:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        3'b011:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        3'b100:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        default: r_data <= r_data;
                    endcase

                    case (r_data_count)
                        3'b000:  r_skid_data1 <= (w_wr_xfer) ? i_wr_data    : r_skid_data1;
                        3'b001:  r_skid_data1 <= (w_no_xfer) ? r_skid_data1 : i_wr_data;
                        3'b010:  begin
                                    if (w_wr_xfer && w_rd_xfer)
                                        r_skid_data1 <= i_wr_data;
                                    else
                                        r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                                end
                        3'b011:  r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                        3'b100:  r_skid_data1 <= (w_rd_xfer) ? r_skid_data2 : r_skid_data1;
                        default: r_skid_data1 <= r_skid_data1;
                    endcase

                    case (r_data_count)
                        3'b000:  r_skid_data2 <= (w_wr_xfer) ? i_wr_data    : r_skid_data2;
                        3'b001:  r_skid_data2 <= (w_no_xfer) ? r_skid_data2 : i_wr_data;
                        3'b010:  r_skid_data2 <= (w_wr_xfer) ? i_wr_data    : r_skid_data2;
                        3'b011:  r_skid_data2 <= (w_rd_xfer) ? i_wr_data    : r_skid_data2;
                        3'b100:  r_skid_data2 <= (w_rd_xfer) ? r_skid_data3 : r_skid_data2;
                        default: r_skid_data2 <= r_skid_data2;
                    endcase

                    if (w_wr_xfer)
                        r_skid_data3 <= i_wr_data;
                end
            end
        end else begin : gen_skid2_buffer
            // Two-deep skid buffer
            always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
                if (~i_axi_aresetn) begin
                    r_wr_ready <= 'b0;
                    r_rd_valid <= 'b0;
                    r_data_count <= 'b0;
                    r_data <= 'b0;
                    r_skid_data1 <= 'b0;
                end else begin
                    r_wr_ready <= (r_data_count == 3'b000) ||
                                    (r_data_count == 3'b001 && (~w_wr_xfer || w_rd_xfer)) ||
                                    (r_data_count == 3'b010 && w_rd_xfer);

                    r_rd_valid <= (r_data_count == 3'b010) ||
                                    (r_data_count == 3'b001 && (~w_rd_xfer || w_wr_xfer)) ||
                                    (r_data_count == 3'b000 && w_wr_xfer);

                    if (w_wr_xfer & ~w_rd_xfer) begin
                        r_data_count <= r_data_count + 3'b001;
                    end else if (~w_wr_xfer & w_rd_xfer) begin
                        r_data_count <= r_data_count - 3'b001;
                    end

                    case (r_data_count)
                        3'b000:  r_data <= i_wr_data;
                        3'b001:  r_data <= (w_rd_xfer) ? i_wr_data    : r_skid_data1;
                        3'b010:  r_data <= (w_rd_xfer) ? r_skid_data1 : r_data;
                        default: r_data <= r_data;
                    endcase

                    if (w_wr_xfer)
                        r_skid_data1 <= i_wr_data;
                end
            end
        end
    endgenerate

    assign o_wr_ready = r_wr_ready;
    assign o_rd_valid = r_rd_valid;
    assign o_rd_data  = r_data;
    assign o_rd_count = r_data_count;

endmodule : axi_skid_buffer
