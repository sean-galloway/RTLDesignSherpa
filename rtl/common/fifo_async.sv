`timescale 1ns / 1ps

// Paramerized Asynchronous FIFO -- This only works for power of two depths
module fifo_async #(
    parameter int REGISTERED = 0,  // 0 = mux mode, 1 = flop mode
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 16,
    parameter int N_FLOP_CROSS = 2,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter     INSTANCE_NAME = "DEADF1F0"  // verilog_lint: waive explicit-parameter-storage-type
) (
    // clocks and resets
    input  logic                    wr_clk,
                                    wr_rst_n,
                                    rd_clk,
                                    rd_rst_n,
    // wr_clk domain
    input  logic                    write,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    output logic                    wr_full,
    output logic                    wr_almost_full,
    // rd_clk domain
    input  logic                    read,
    output logic [DATA_WIDTH-1:0]   rd_data,
    output logic                    rd_empty,
    output logic                    rd_almost_empty
);

    localparam int DW = DATA_WIDTH;
    localparam int D = DEPTH;
    localparam int AW = $clog2(DEPTH);
    localparam int N = N_FLOP_CROSS;

    /////////////////////////////////////////////////////////////////////////
    // local logics
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    logic [AW:0] r_wr_ptr_gray, r_wdom_rd_ptr_gray, r_rd_ptr_gray, r_rdom_wr_ptr_gray;
    logic [AW:0] r_wr_ptr_bin, w_wdom_rd_ptr_bin, r_rd_ptr_bin, w_rdom_wr_ptr_bin;
    logic [AW:0] w_wr_ptr_bin_next, w_rd_ptr_bin_next;

    // The flop storage logicisters
    logic [DW-1:0] r_mem[0:((1<<AW)-1)];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DW-1:0] w_rd_data;

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the bin and gray counters for write and read pointers
    counter_bingray #(
        .WIDTH(AW + 1)
    ) wr_ptr_counter_gray (
        .clk(wr_clk),
        .rst_n(wr_rst_n),
        .enable(write && !wr_full),
        .counter_bin(r_wr_ptr_bin),
        .counter_bin_next(w_wr_ptr_bin_next),
        .counter_gray(r_wr_ptr_gray)
    );

    counter_bingray #(
        .WIDTH(AW + 1)
    ) rd_ptr_counter_gray (
        .clk(rd_clk),
        .rst_n(rd_rst_n),
        .enable(read && !rd_empty),
        .counter_bin(r_rd_ptr_bin),
        .counter_bin_next(w_rd_ptr_bin_next),
        .counter_gray(r_rd_ptr_gray)
    );

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the clock crossing modules
    glitch_free_n_dff_arn #(
        .FLOP_COUNT(N_FLOP_CROSS),
        .WIDTH(AW + 1)
    ) rd_ptr_gray_cross_inst (
        .q(r_wdom_rd_ptr_gray),
        .d(r_rd_ptr_gray),
        .clk(wr_clk),
        .rst_n(wr_rst_n)
    );

    // convert the gray rd ptr to binary
    gray2bin #(
        .WIDTH(AW + 1)
    ) rd_ptr_gray2bin_inst (
        .binary(w_wdom_rd_ptr_bin),
        .gray(r_wdom_rd_ptr_gray)
    );

    glitch_free_n_dff_arn #(
        .FLOP_COUNT(N_FLOP_CROSS),
        .WIDTH(AW + 1)
    ) wr_ptr_gray_cross_inst (
        .q(r_rdom_wr_ptr_gray),
        .d(r_wr_ptr_gray),
        .clk(rd_clk),
        .rst_n(rd_rst_n)
    );

    // convert the gray wr ptr to binary
    gray2bin #(
        .WIDTH(AW + 1)
    ) wr_ptr_gray2bin_inst (
        .binary(w_rdom_wr_ptr_bin),
        .gray(r_rdom_wr_ptr_gray)
    );

    /////////////////////////////////////////////////////////////////////////
    // assign read/write addresses
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

    /////////////////////////////////////////////////////////////////////////
    // Memory Flops
    always_ff @(posedge wr_clk) begin
        if (write) begin
            r_mem[r_wr_addr] <= wr_data;
        end
    end

    assign w_rd_data = r_mem[r_rd_addr];

    /////////////////////////////////////////////////////////////////////////
    // Read Port
    generate
        if (REGISTERED != 0) begin : gen_flop_mode
            // Flop mode - registered output
            always_ff @(posedge rd_clk or negedge rd_rst_n) begin
                if (!rd_rst_n)
                    rd_data <= 'b0;
                else
                    rd_data <= w_rd_data;
            end
        end else begin : gen_mux_mode
            // Mux mode - non-registered output
            assign rd_data = w_rd_data;
        end
    endgenerate


    /////////////////////////////////////////////////////////////////////////
    // Generate the Full/Empty signals
    fifo_control #(
        .DEPTH              (D),
        .ADDR_WIDTH         (AW),
        .ALMOST_RD_MARGIN   (ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN   (ALMOST_WR_MARGIN),
        .REGISTERED         (REGISTERED)
    ) fifo_control_inst (
        .wr_clk           (wr_clk),
        .wr_rst_n         (wr_rst_n),
        .rd_clk           (rd_clk),
        .rd_rst_n         (rd_rst_n),
        .wr_ptr_bin      (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin (w_wdom_rd_ptr_bin),
        .rd_ptr_bin      (w_rd_ptr_bin_next),
        .rdom_wr_ptr_bin (w_rdom_wr_ptr_bin),
        .count           (),
        .wr_full          (wr_full),
        .wr_almost_full   (wr_almost_full),
        .rd_empty         (rd_empty),
        .rd_almost_empty  (rd_almost_empty)
    );

    /////////////////////////////////////////////////////////////////////////
    // Error checking and debug stuff
    // synopsys translate_off
    logic [(DW*DEPTH)-1:0] flat_r_mem;
    genvar i;
    generate
        for (i = 0; i < DEPTH; i++) begin : gen_flatten_memory
            assign flat_r_mem[i*DW+:DW] = r_mem[i];
        end
    endgenerate

    always_ff @(posedge wr_clk) begin
        if (!wr_rst_n && (write && wr_full) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always_ff @(posedge rd_clk) begin
        if (!wr_rst_n && (read && rd_empty) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s read while fifo empty, %t", INSTANCE_NAME, $time);
        end
    end
    // synopsys translate_on

endmodule : fifo_async
