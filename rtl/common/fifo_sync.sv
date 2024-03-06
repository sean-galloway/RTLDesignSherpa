`timescale 1ns / 1ps

// Parameterized Synchronous FIFO -- This works with any depth
module fifo_sync #(
    parameter int DEL = 1,
    parameter int DATA_WIDTH = 4,
    parameter int DEPTH = 4,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter INSTANCE_NAME = "DEADF1F0"  // verilog_lint: waive explicit-parameter-storage-type
) (
    input  logic                  i_clk,
    i_rst_n,
    input  logic                  i_write,
    input  logic [DATA_WIDTH-1:0] i_wr_data,
    output logic                  o_wr_full,
    output logic                  o_wr_almost_full,
    input  logic                  i_read,
    output logic [DATA_WIDTH-1:0] ow_rd_data,
    output logic [DATA_WIDTH-1:0] o_rd_data,
    output logic                  o_rd_empty,
    output logic                  o_rd_almost_empty
);

    localparam int DW = DATA_WIDTH;
    localparam int D = DEPTH;
    localparam int AW = $clog2(DEPTH);

    /////////////////////////////////////////////////////////////////////////
    // local logics/register signals
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    logic [AW:0] r_wr_ptr_bin, r_rd_ptr_bin;
    logic [AW:0] w_wr_ptr_bin_next, w_rd_ptr_bin_next;

    // The flop storage
    logic [DW-1:0] r_mem[0:((1<<AW)-1)];  // verilog_lint: waive unpacked-dimensions-range-ordering

    /////////////////////////////////////////////////////////////////////////
    // Write counter
    counter_bin #(
        .WIDTH(AW + 1),
        .MAX  (D)
    ) write_pointer_inst (
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .i_enable(i_write && !o_wr_full),
        .o_counter_bin(r_wr_ptr_bin),
        .ow_counter_bin_next(w_wr_ptr_bin_next)
    );

    /////////////////////////////////////////////////////////////////////////
    // Read counter
    counter_bin #(
        .WIDTH(AW + 1),
        .MAX  (D)
    ) read_pointer_inst (
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .i_enable(i_read && !o_rd_empty),
        .o_counter_bin(r_rd_ptr_bin),
        .ow_counter_bin_next(w_rd_ptr_bin_next)
    );

    /////////////////////////////////////////////////////////////////////////
    // Generate the Full/Empty signals
    fifo_control #(
        .DEL(DEL),
        .DEPTH(D),
        .ADDR_WIDTH(AW),
        .ALMOST_RD_MARGIN(ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN(ALMOST_WR_MARGIN)
    ) fifo_control_inst (
        .i_wr_clk          (i_clk),
        .i_wr_rst_n        (i_rst_n),
        .i_rd_clk          (i_clk),
        .i_rd_rst_n        (i_rst_n),
        .iw_wr_ptr_bin     (w_wr_ptr_bin_next),
        .iw_wdom_rd_ptr_bin(w_rd_ptr_bin_next),
        .iw_rd_ptr_bin     (w_rd_ptr_bin_next),
        .iw_rdom_wr_ptr_bin(w_wr_ptr_bin_next),
        .o_wr_full         (o_wr_full),
        .o_wr_almost_full  (o_wr_almost_full),
        .o_rd_empty        (o_rd_empty),
        .o_rd_almost_empty (o_rd_almost_empty)
    );

    /////////////////////////////////////////////////////////////////////////
    // Get the write/read address to the memory
    // Memory operations using the extracted addresses
    assign r_wr_addr  = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr  = r_rd_ptr_bin[AW-1:0];
    assign ow_rd_data = r_mem[r_rd_addr];

    always_ff @(posedge i_clk) begin
        if (i_write && !o_wr_full) begin
            r_mem[r_wr_addr] <= i_wr_data;
        end
    end

    // Flop stage for the flopped data
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) o_rd_data <= 'b0;
        else o_rd_data <= r_mem[r_rd_addr];
    end

    /////////////////////////////////////////////////////////////////////////
    // error checking
    // synopsys translate_off
    // Generate a version of the memory for waveforms
    logic [(DW*DEPTH)-1:0] flat_r_mem;
    genvar i;
    generate
        for (i = 0; i < DEPTH; i++) begin : gen_flatten_memory
            assign flat_r_mem[i*DW+:DW] = r_mem[i];
        end
    endgenerate

    always @(posedge i_clk) begin
        if ((i_write && o_wr_full) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always @(posedge i_clk) begin
        if ((i_read && o_rd_empty) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s read while fifo empty, %t", INSTANCE_NAME, $time);
        end
    end
    // synopsys translate_on

endmodule : fifo_sync
