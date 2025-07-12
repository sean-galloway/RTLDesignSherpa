`timescale 1ns / 1ps

// Parameterized Synchronous FIFO -- This works with any depth
module fifo_sync #(
    parameter int REGISTERED = 0,  // 0 = mux mode, 1 = flop mode
    parameter int DATA_WIDTH = 4,
    parameter int DEPTH = 4,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter     INSTANCE_NAME = "DEADF1F0",  // verilog_lint: waive explicit-parameter-storage-type
    parameter int DW = DATA_WIDTH,
    parameter int D = DEPTH,
    parameter int AW = $clog2(DEPTH)
) (
    input  logic                    clk,
                                    rst_n,
    input  logic                    write,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    output logic                    wr_full,
    output logic                    wr_almost_full,
    input  logic                    read,
    output logic [DATA_WIDTH-1:0]   rd_data,
    output logic                    rd_empty,
    output logic                    rd_almost_empty
);

    /////////////////////////////////////////////////////////////////////////
    // local logics/register signals
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    logic [AW:0] r_wr_ptr_bin, r_rd_ptr_bin;
    logic [AW:0] w_wr_ptr_bin_next, w_rd_ptr_bin_next;

    // The flop storage
    logic [DW-1:0] r_mem[0:((1<<AW)-1)];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DW-1:0] w_rd_data;

    /////////////////////////////////////////////////////////////////////////
    // Write counter
    counter_bin #(
        .WIDTH  (AW + 1),
        .MAX    (D)
    ) write_pointer_inst (
        .clk                  (clk),
        .rst_n                (rst_n),
        .enable               (write && !wr_full),
        .counter_bin_curr     (r_wr_ptr_bin),
        .counter_bin_next     (w_wr_ptr_bin_next)
    );

    /////////////////////////////////////////////////////////////////////////
    // Read counter
    counter_bin #(
        .WIDTH                (AW + 1),
        .MAX                  (D)
    ) read_pointer_inst(
        .clk                  (clk),
        .rst_n                (rst_n),
        .enable               (read && !rd_empty),
        .counter_bin_curr     (r_rd_ptr_bin),
        .counter_bin_next     (w_rd_ptr_bin_next)
    );

    /////////////////////////////////////////////////////////////////////////
    // Generate the Full/Empty signals
    fifo_control #(
        .DEPTH                (D),
        .ADDR_WIDTH           (AW),
        .ALMOST_RD_MARGIN     (ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN     (ALMOST_WR_MARGIN),
        .REGISTERED           (REGISTERED)
    ) fifo_control_inst (
        .wr_clk               (clk),
        .wr_rst_n             (rst_n),
        .rd_clk               (clk),
        .rd_rst_n             (rst_n),
        .wr_ptr_bin           (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin      (w_rd_ptr_bin_next),
        .rd_ptr_bin           (w_rd_ptr_bin_next),
        .rdom_wr_ptr_bin      (w_wr_ptr_bin_next),
        .count                (),
        .wr_full              (wr_full),
        .wr_almost_full       (wr_almost_full),
        .rd_empty             (rd_empty),
        .rd_almost_empty      (rd_almost_empty)
    );

    /////////////////////////////////////////////////////////////////////////
    // Get the write/read address to the memory
    // Memory operations using the extracted addresses
    assign r_wr_addr  = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr  = r_rd_ptr_bin[AW-1:0];

    /////////////////////////////////////////////////////////////////////////
    // Memory Flops
    always_ff @(posedge clk) begin
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
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n)
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

    always_ff @(posedge clk) begin
        if ((write && wr_full) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always_ff @(posedge clk) begin
        if ((read && rd_empty) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            if (REGISTERED == 1) begin
                $display("Error: %s read while fifo empty (flop mode), %t", INSTANCE_NAME, $time);
            end else begin
                $display("Error: %s read while fifo empty (mux mode), %t", INSTANCE_NAME, $time);
            end
        end
    end
    // synopsys translate_on

endmodule : fifo_sync
