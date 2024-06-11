`timescale 1ns / 1ps

// Parameterized Synchronous FIFO -- This works with any depth
module axi_fifo_sync #(
    parameter int DEL = 1,
    parameter int DATA_WIDTH = 4,
    parameter int DEPTH = 4,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter INSTANCE_NAME = "DEADF1F0"  // verilog_lint: waive explicit-parameter-storage-type
) (
    input  logic            i_axi_aclk,
    input  logic            i_axi_aresetn,
    input  logic            i_wr_valid,
    output logic            o_wr_ready,   // not full
    input  logic [DW-1:0]   i_wr_data,
    input  logic            i_rd_ready,
    output logic [AW-1:0]   ow_count,
    output logic            o_rd_valid,   // not empty
    output logic [DW-1:0]   ow_rd_data,
    output logic [DW-1:0]   o_rd_data
);

    localparam int DW = DATA_WIDTH;
    localparam int D = DEPTH;
    localparam int AW = $clog2(DEPTH);

    /////////////////////////////////////////////////////////////////////////
    // local logics/register signals
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    logic [AW:0] r_wr_ptr_bin, r_rd_ptr_bin;
    logic [AW:0] w_wr_ptr_bin_next, w_rd_ptr_bin_next;
    logic        r_wr_full, r_wr_almost_full, r_rd_empty, r_rd_almost_empty;

    // The flop storage
    logic [DW-1:0] r_mem[0:((1<<AW)-1)];  // verilog_lint: waive unpacked-dimensions-range-ordering

    /////////////////////////////////////////////////////////////////////////
    // Write counter
    assign w_write = i_wr_valid && o_wr_ready;

    counter_bin #(
        .WIDTH(AW + 1),
        .MAX  (D)
    ) write_pointer_inst (
        .i_clk(i_axi_aclk),
        .i_rst_n(i_axi_aresetn),
        .i_enable(w_write && !r_wr_full),
        .o_counter_bin(r_wr_ptr_bin),
        .ow_counter_bin_next(w_wr_ptr_bin_next)
    );

    /////////////////////////////////////////////////////////////////////////
    // Read counter
    assign w_read = o_rd_valid && i_rd_ready;
    counter_bin #(
        .WIDTH(AW + 1),
        .MAX  (D)
    ) read_pointer_inst (
        .i_clk(i_axi_aclk),
        .i_rst_n(i_axi_aresetn),
        .i_enable(w_read && !r_rd_empty),
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
        .i_wr_clk          (i_axi_aclk),
        .i_wr_rst_n        (i_axi_aresetn),
        .i_rd_clk          (i_axi_aclk),
        .i_rd_rst_n        (i_axi_aresetn),
        .iw_wr_ptr_bin     (w_wr_ptr_bin_next),
        .iw_wdom_rd_ptr_bin(w_rd_ptr_bin_next),
        .iw_rd_ptr_bin     (w_rd_ptr_bin_next),
        .iw_rdom_wr_ptr_bin(w_wr_ptr_bin_next),
        .ow_count          (ow_count),
        .o_wr_full         (r_wr_full),
        .o_wr_almost_full  (r_wr_almost_full),
        .o_rd_empty        (r_rd_empty),
        .o_rd_almost_empty (r_rd_almost_empty)
    );

    assign o_wr_ready = !r_wr_full;
    assign o_rd_valid = !r_rd_empty;

    /////////////////////////////////////////////////////////////////////////
    // Get the write/read address to the memory
    // Memory operations using the extracted addresses
    assign r_wr_addr  = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr  = r_rd_ptr_bin[AW-1:0];
    assign ow_rd_data = r_mem[r_rd_addr];

    always_ff @(posedge i_axi_aclk) begin
        if (w_write && !r_wr_full) begin
            r_mem[r_wr_addr] <= i_wr_data;
        end
    end

    // Flop stage for the flopped data
    always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
        if (!i_axi_aresetn) o_rd_data <= 'b0;
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

    always @(posedge i_axi_aclk) begin
        if ((w_write && r_wr_full) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always @(posedge i_axi_aclk) begin
        if ((w_read && r_rd_empty) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s read while fifo empty, %t", INSTANCE_NAME, $time);
        end
    end
    // synopsys translate_on

endmodule : axi_fifo_sync
