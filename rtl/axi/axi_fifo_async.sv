`timescale 1ns / 1ps

// Paramerized Asynchronous FIFO -- This works for any even depth
module axi_fifo_async #(
    parameter int DEL = 1,
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 10,
    parameter int N_FLOP_CROSS = 2,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter INSTANCE_NAME = "DEADF1F0"  // verilog_lint: waive explicit-parameter-storage-type
) (
    // clocks and resets
    input  logic            i_axi_wr_aclk,
                            i_axi_wr_aresetn,
                            i_axi_rd_aclk,
                            i_axi_rd_aresetn,
    input  logic            i_wr_valid,
    output logic            o_wr_ready,   // not full
    input  logic [DW-1:0]   i_wr_data,
    input  logic            i_rd_ready,
    output logic            o_rd_valid,   // not empty
    output logic [DW-1:0]   ow_rd_data,
    output logic [DW-1:0]   o_rd_data
    );

    localparam int DW = DATA_WIDTH;
    localparam int D = DEPTH;
    localparam int AW = $clog2(DEPTH);
    localparam int JCW = D;  // Johnson Counter Width
    localparam int N = N_FLOP_CROSS;

    /////////////////////////////////////////////////////////////////////////
    // local wires
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    // these are all based on the Johnson Counter
    logic [JCW-1:0] r_wr_ptr_gray, r_wdom_rd_ptr_gray, r_rd_ptr_gray, r_rdom_wr_ptr_gray;
    logic [AW:0] r_wr_ptr_bin, w_wdom_rd_ptr_bin, r_rd_ptr_bin, w_rdom_wr_ptr_bin;
    logic [AW:0] w_wr_ptr_bin_next, w_rd_ptr_bin_next;
    logic        r_wr_full, r_wr_almost_full, r_rd_empty, r_rd_almost_empty;

    // The flop storage registers
    logic [DW-1:0] r_mem[0:((1<<AW)-1)];  // verilog_lint: waive unpacked-dimensions-range-ordering

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the binary counters for write and read pointers
    assign w_write = i_wr_valid && o_wr_ready;
    counter_bin #(
        .MAX  (D),
        .WIDTH(AW + 1)
    ) wr_ptr_counter_bin (
        .i_clk(i_axi_wr_aclk),
        .i_rst_n(i_axi_wr_aresetn),
        .i_enable(w_write && !r_wr_full),
        .ow_counter_bin_next(w_wr_ptr_bin_next),
        .o_counter_bin(r_wr_ptr_bin)
    );

    assign w_read = o_rd_valid && i_rd_ready;
    counter_bin #(
        .MAX  (D),
        .WIDTH(AW + 1)
    ) rd_ptr_counter_bin (
        .i_clk(i_axi_rd_aclk),
        .i_rst_n(i_axi_rd_aresetn),
        .i_enable(w_read && !r_rd_empty),
        .ow_counter_bin_next(w_rd_ptr_bin_next),
        .o_counter_bin(r_rd_ptr_bin)
    );

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the gray counters for write and read pointers
    counter_johnson #(
        .WIDTH(JCW)
    ) wr_ptr_counter_gray (
        .i_clk(i_axi_wr_aclk),
        .i_rst_n(i_axi_wr_aresetn),
        .i_enable(w_write && !r_wr_full),
        .o_counter_gray(r_wr_ptr_gray)
    );

    counter_johnson #(
        .WIDTH(JCW)
    ) rd_ptr_counter_gray (
        .i_clk(i_axi_rd_aclk),
        .i_rst_n(i_axi_rd_aresetn),
        .i_enable(w_read && !r_rd_empty),
        .o_counter_gray(r_rd_ptr_gray)
    );

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the clock crossing modules
    glitch_free_n_dff_arn #(
        .FLOP_COUNT(N_FLOP_CROSS),
        .WIDTH(JCW)
    ) rd_ptr_gray_cross_inst (
        .o_q(r_wdom_rd_ptr_gray),
        .i_d(r_rd_ptr_gray),
        .i_clk(i_axi_wr_aclk),
        .i_rst_n(i_axi_wr_aresetn)
    );

    // convert the gray rd ptr to binary
    grayj2bin #(
        .JCW(JCW),
        .WIDTH(AW + 1),
        .INSTANCE_NAME("rd_ptr_johnson2bin_inst")
    ) rd_ptr_gray2bin_inst (
        .ow_binary(w_wdom_rd_ptr_bin),
        .i_gray(r_wdom_rd_ptr_gray),
        .i_clk(i_axi_wr_aclk),
        .i_rst_n(i_axi_wr_aresetn)
    );

    glitch_free_n_dff_arn #(
        .FLOP_COUNT(N_FLOP_CROSS),
        .WIDTH(JCW)
    ) wr_ptr_gray_cross_inst (
        .o_q(r_rdom_wr_ptr_gray),
        .i_d(r_wr_ptr_gray),
        .i_clk(i_axi_rd_aclk),
        .i_rst_n(i_axi_rd_aresetn)
    );

    // convert the gray wr ptr to binary
    grayj2bin #(
        .JCW(JCW),
        .WIDTH(AW + 1),
        .INSTANCE_NAME("wr_ptr_gray2bin_inst")
    ) wr_ptr_gray2bin_inst (
        .ow_binary(w_rdom_wr_ptr_bin),
        .i_gray(r_rdom_wr_ptr_gray),
        .i_clk(i_axi_rd_aclk),
        .i_rst_n(i_axi_rd_aresetn)
    );

    /////////////////////////////////////////////////////////////////////////
    // assign read/write addresses
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

    /////////////////////////////////////////////////////////////////////////
    // Memory Flops
    always_ff @(posedge i_axi_wr_aclk) begin
        if (w_write && !r_wr_full) r_mem[r_wr_addr] <= i_wr_data;
    end

    // Flop stage for the flopped data
    always_ff @(posedge i_axi_rd_aclk or negedge i_axi_rd_aresetn) begin
        if (!i_axi_rd_aresetn) o_rd_data <= 'b0;
        else o_rd_data <= r_mem[r_rd_addr];
    end

    /////////////////////////////////////////////////////////////////////////
    // Read Port
    assign ow_rd_data = r_mem[r_rd_addr];

    /////////////////////////////////////////////////////////////////////////
    // Generate the Full/Empty signals
    fifo_control #(
        .DEL(DEL),
        .DEPTH(D),
        .ADDR_WIDTH(AW),
        .ALMOST_RD_MARGIN(ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN(ALMOST_WR_MARGIN)
    ) fifo_control_inst (
        .i_wr_clk          (i_axi_wr_aclk),
        .i_wr_rst_n        (i_axi_wr_aresetn),
        .i_rd_clk          (i_axi_rd_aclk),
        .i_rd_rst_n        (i_axi_rd_aresetn),
        .iw_wr_ptr_bin     (w_wr_ptr_bin_next),
        .iw_wdom_rd_ptr_bin(w_wdom_rd_ptr_bin),
        .iw_rd_ptr_bin     (w_rd_ptr_bin_next),
        .iw_rdom_wr_ptr_bin(w_rdom_wr_ptr_bin),
        .o_wr_full         (r_wr_full),
        .o_wr_almost_full  (r_wr_almost_full),
        .o_rd_empty        (r_rd_empty),
        .o_rd_almost_empty (r_rd_almost_empty)
    );

    assign o_wr_ready = !r_wr_full;
    assign o_rd_valid = !r_rd_empty;

    /////////////////////////////////////////////////////////////////////////
    // Error checking and debug stuff
    // synopsys translate_off
    wire [(DW*DEPTH)-1:0] flat_r_mem;
    genvar i;
    generate
        for (i = 0; i < DEPTH; i++) begin : gen_flatten_memory
            assign flat_r_mem[i*DW+:DW] = r_mem[i];
        end
    endgenerate

    always @(posedge i_axi_wr_aclk) begin
        if (!i_axi_wr_aresetn && (w_write && r_wr_full) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always @(posedge i_axi_rd_aclk) begin
        if (!i_axi_wr_aresetn && (w_read && r_rd_empty) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s read while fifo empty, %t", INSTANCE_NAME, $time);
        end
    end
    // synopsys translate_on

endmodule : axi_fifo_async
