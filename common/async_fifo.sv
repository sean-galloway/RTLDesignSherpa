`timescale 1ns / 1ps

// An async fifo that works for any even number of entries; not simply powers of 2
module async_fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16,
    parameter N_FLOP_CROSS = 2,
    parameter ALMOST_WR_MARGIN = 1,
    parameter ALMOST_RD_MARGIN = 1,
    parameter INSTANCE_NAME = "DEADF1F0"
)(
    // clocks and resets
    input wire wr_clk, wr_rst_n, rd_clk, rd_rst_n,
    // wr_clk domain
    input wire write,
    input wire [DATA_WIDTH-1:0] wr_data,
    output reg wr_full,
    output reg wr_almost_full,
    // rd_clk domain
    input wire read,
    output wire [DATA_WIDTH-1:0] rd_data,
    output reg rd_empty,
    output reg rd_almost_empty
);

    localparam DW = DATA_WIDTH;
    localparam D = DEPTH;
    localparam AW = $clog2(DEPTH);
    localparam N = N_FLOP_CROSS;
    localparam AFULL = ALMOST_WR_MARGIN;
    localparam AEMPTY = ALMOST_RD_MARGIN;
    localparam AFT = D - AFULL;
    localparam AET = AEMPTY;
    localparam ZERO = {AW-1{1'b0}};

    // local wires
    logic [AW-1:0] wr_addr, rd_addr;

    logic [AW:0] wr_ptr_gray, wdom_rd_ptr_gray, rd_ptr_gray, rdom_wr_ptr_gray;
    logic [AW:0] wr_ptr_bin, wdom_rd_ptr_bin, rd_ptr_bin, rdom_wr_ptr_bin;

    // The flop storage
    logic [DW-1:0] mem [0:((1<<AW)-1)];

    // Instantiate the gray counters for write and read pointers
    counter_gray #(.WIDTH(AW+1)) wr_ptr_counter_gray (
        .clk(wr_clk), .rst_n(wr_rst_n), .enable(write && !wr_full), .counter_out_gray(wr_ptr_gray)
    );

    counter_gray #(.WIDTH(AW+1)) rd_ptr_counter_gray (
        .clk(rd_clk), .rst_n(rd_rst_n), .enable(read && !rd_empty), .counter_out_gray(rd_ptr_gray)
    );

    // Instantiate the binary counters for write and read pointers
    counter_bin #(.WIDTH(AW)) wr_ptr_counter_bin (
        .clk(wr_clk), .rst_n(wr_rst_n), .enable(write && !wr_full), .counter_out_bin(wr_ptr_bin)
    );

    counter_bin #(.WIDTH(AW)) rd_ptr_counter_bin (
        .clk(rd_clk), .rst_n(rd_rst_n), .enable(read && !rd_empty), .counter_out_bin(rd_ptr_bin)
    );

    assign wr_addr = wr_ptr_bin[AW-1:0];
    assign rd_addr = rd_ptr_bin[AW-1:0];

    // Memory Flops
    always_ff @(posedge wr_clk) begin
        if (write && !wr_full)
            mem[wr_addr] <= wr_data;
    end

    // Read Port
    assign rd_data = mem[rd_addr];

    // Full and Empty signals
    assign wr_full = (wr_ptr_gray == {~wdom_rd_ptr_gray[AW:AW-1], wdom_rd_ptr_gray[AW-2:0]});
    assign rd_empty = (rd_ptr_gray == rdom_wr_ptr_gray);

    // Almost Full and Almost Empty signals
    wire [1:0] almost_full_select = {wr_ptr_bin[AW], wdom_rd_ptr_bin[AW]};
    wire [AW-1:0] almost_full_count = (almost_full_select == 2'b00) ? {wr_ptr_bin[AW-1:0] - wdom_rd_ptr_bin[AW-1:0]} :
                                        (almost_full_select == 2'b10) ? {(D - wdom_rd_ptr_bin[AW-1:0]) - wr_ptr_bin[AW-1:0]} :
                                        (almost_full_select == 2'b01) ? {(D - wdom_rd_ptr_bin[AW-1:0]) - wr_ptr_bin[AW-1:0]} :
                                        {wr_ptr_bin[AW-1:0] - wdom_rd_ptr_bin[AW-1:0]};
    assign wr_almost_full = almost_full_count >= AFT;

    wire [1:0] almost_empty_select = {rdom_wr_ptr_bin[AW], rd_ptr_bin[AW]};
    wire [AW:0] almost_empty_count = (almost_empty_select == 2'b00) ? {rdom_wr_ptr_bin - rd_ptr_bin} :
                                        (almost_empty_select == 2'b10) ? {rdom_wr_ptr_bin - rd_ptr_bin} :
                                        (almost_empty_select == 2'b01) ? {(D - rd_ptr_bin - rdom_wr_ptr_bin)} :
                                        {rdom_wr_ptr_bin - rd_ptr_bin};
    assign rd_almost_empty = (almost_empty_count > 0) ? almost_empty_count <= AET : 'b0;

    // Error checking and debug stuff
    // synopsys translate_off
    always @(posedge wr_clk) begin
        if (!wr_rst_n && (write && wr_full) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10); $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always @(posedge rd_clk) begin
        if (!wr_rst_n && (read && rd_empty) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10); $display("Error: %s read while fifo empty, %t", INSTANCE_NAME, $time);
        end
    end

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, async_fifo);
    end
    // synopsys translate_on

endmodule : async_fifo