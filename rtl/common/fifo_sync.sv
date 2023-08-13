`timescale 1ns / 1ps

// Parameterized Synchronous FIFO -- This works with any depth
module fifo_sync #(
        parameter DATA_WIDTH = 4,
        parameter DEPTH = 4,
        parameter ALMOST_WR_MARGIN = 1,
        parameter ALMOST_RD_MARGIN = 1,
        parameter INSTANCE_NAME = "DEADF1F0"
    ) (
    input  logic                  i_clk, i_rst_n,
    input  logic                  i_write,
    input  logic [DATA_WIDTH-1:0] i_wr_data,
    output logic                  ow_wr_full,
    output logic                  ow_wr_almost_full,
    input  logic                  i_read,
    output logic [DATA_WIDTH-1:0] ow_rd_data,
    output logic                  ow_rd_empty,
    output logic                  ow_rd_almost_empty
);

    localparam DW = DATA_WIDTH;
    localparam D = DEPTH;
    localparam AW = $clog2(DEPTH);
    localparam AFULL = ALMOST_WR_MARGIN;
    localparam AEMPTY = ALMOST_RD_MARGIN;
    localparam AFT = D - AFULL;
    localparam AET = AEMPTY;

	/////////////////////////////////////////////////////////////////////////
    // local logics/register signals
    logic [AW-1:0] r_wr_addr, r_rd_addr, r_pre_wr_addr;
    logic [AW:0]   r_wr_ptr_bin, r_rd_ptr_bin;
    logic          w_ptr_xor;
    logic [AW-1:0] w_almost_full_count, w_almost_empty_count;

    // The flop storage
    logic [DW-1:0] r_mem [0:((1<<AW)-1)];

	/////////////////////////////////////////////////////////////////////////
    // Write counter
    counter_bin #(.WIDTH(AW+1), .MAX(D)) write_counter (
        .i_clk(i_clk), .i_rst_n(i_rst_n), .i_enable(i_write && !ow_wr_full), .o_counter_bin(r_wr_ptr_bin)
    );

	/////////////////////////////////////////////////////////////////////////
    // Read counter
    counter_bin #(.WIDTH(AW+1), .MAX(D)) read_counter (
        .i_clk(i_clk), .i_rst_n(i_rst_n), .i_enable(i_read && !ow_rd_empty), .o_counter_bin(r_rd_ptr_bin)
    );

	/////////////////////////////////////////////////////////////////////////
    // XOR the two upper bits of the pointers to for use in the full/empty equations
    assign w_ptr_xor = r_wr_ptr_bin[AW] ^ r_rd_ptr_bin[AW];

	/////////////////////////////////////////////////////////////////////////
    // Get the write/read address to the memory
    // Memory operations using the extracted addresses
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];
    assign ow_rd_data = r_mem[r_rd_addr];

    always_ff @(posedge i_clk)
    begin
        if (i_write && !ow_wr_full) begin
            r_mem[r_wr_addr] <= i_wr_data;
        end
    end

	/////////////////////////////////////////////////////////////////////////
    // Full and Empty signals
    assign ow_wr_full = (w_ptr_xor && (r_wr_ptr_bin[AW-1:0] == r_rd_ptr_bin[AW-1:0]));
    assign ow_rd_empty = (!w_ptr_xor && (r_rd_ptr_bin[AW-1:0] == r_wr_ptr_bin[AW-1:0]));

	/////////////////////////////////////////////////////////////////////////
    // Almost Full/Empty logic
    assign w_almost_full_count = (w_ptr_xor) ?  {(D - r_rd_ptr_bin[AW-1:0]) - r_wr_ptr_bin[AW-1:0]} : 
                                                {r_wr_ptr_bin[AW-1:0] - r_rd_ptr_bin[AW-1:0]};
    assign ow_wr_almost_full = w_almost_full_count >= AFT;

    assign w_almost_empty_count = (w_ptr_xor) ? {(D - r_rd_ptr_bin[AW-1:0]) - r_wr_ptr_bin[AW-1:0]} : 
                                                {r_wr_ptr_bin[AW-1:0] - r_rd_ptr_bin[AW-1:0]};
    assign ow_rd_almost_empty = (w_almost_empty_count > 0) ? w_almost_empty_count <= AET : 'b0;

	/////////////////////////////////////////////////////////////////////////
    // error checking
    // synopsys translate_off
    // Generate a version of the memory for waveforms
    logic [(DW*DEPTH)-1:0] flat_r_mem;
    genvar i;
    generate
        for (i = 0; i < DEPTH; i = i+1)
            begin : flatten_memory
                assign flat_r_mem[i*DW +: DW] = r_mem[i];
            end
    endgenerate

    always @(posedge i_clk)
    begin
        if ((i_write && ow_wr_full) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10); $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always @(posedge i_clk)
    begin
        if ((i_read && ow_rd_empty) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10); $display("Error: %s read while fifo empty, %t", INSTANCE_NAME, $time);
        end
    end

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, fifo_sync);
    end
    // synopsys translate_on

endmodule : fifo_sync
