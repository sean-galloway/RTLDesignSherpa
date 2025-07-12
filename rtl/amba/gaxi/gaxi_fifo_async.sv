`timescale 1ns / 1ps

// Paramerized Asynchronous FIFO -- This works for any even depth
module gaxi_fifo_async #(
    parameter int REGISTERED = 0,  // 0 = mux mode, 1 = flop mode
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 10,
    parameter int N_FLOP_CROSS = 2,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter     INSTANCE_NAME = "DEADF1F0",  // verilog_lint: waive explicit-parameter-storage-type
    parameter int DW = DATA_WIDTH,
    parameter int D = DEPTH,
    parameter int AW = $clog2(DEPTH),
    parameter int JCW = D,  // Johnson Counter Width
    parameter int N = N_FLOP_CROSS
) (
    // clocks and resets
    input  logic            axi_wr_aclk,
                            axi_wr_aresetn,
                            axi_rd_aclk,
                            axi_rd_aresetn,
    input  logic            wr_valid,
    output logic            wr_ready,   // not full
    input  logic [DW-1:0]   wr_data,
    input  logic            rd_ready,
    output logic            rd_valid,   // not empty
    output logic [DW-1:0]   rd_data
    );

    /////////////////////////////////////////////////////////////////////////
    // local wires
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    // these are all based on the Johnson Counter
    logic [JCW-1:0] r_wr_ptr_gray, r_wdom_rd_ptr_gray, r_rd_ptr_gray, r_rdom_wr_ptr_gray;
    logic [AW:0] r_wr_ptr_bin, w_wdom_rd_ptr_bin, r_rd_ptr_bin, w_rdom_wr_ptr_bin;
    logic [AW:0] w_wr_ptr_bin_next, w_rd_ptr_bin_next;
    logic        r_wr_full, r_wr_almost_full, r_rd_empty, r_rd_almost_empty;
    logic        w_write, w_read;
    logic [AW:0] w_count;

    // The flop storage registers
    logic [DW-1:0] r_mem[0:((1<<AW)-1)];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DW-1:0] w_rd_data;

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the binary counters for write and read pointers
    assign w_write = wr_valid && wr_ready;
    counter_bin #(
        .MAX                (D),
        .WIDTH              (AW + 1)
    ) wr_ptr_counter_bin(
        .clk              (axi_wr_aclk),
        .rst_n            (axi_wr_aresetn),
        .enable           (w_write && !r_wr_full),
        .counter_bin_next(w_wr_ptr_bin_next),
        .counter_bin      (r_wr_ptr_bin)
    );

    assign w_read = rd_valid && rd_ready;
    counter_bin #(
        .MAX                (D),
        .WIDTH              (AW + 1)
    ) rd_ptr_counter_bin(
        .clk              (axi_rd_aclk),
        .rst_n            (axi_rd_aresetn),
        .enable           (w_read && !r_rd_empty),
        .counter_bin_next(w_rd_ptr_bin_next),
        .counter_bin      (r_rd_ptr_bin)
    );

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the gray counters for write and read pointers
    counter_johnson #(
        .WIDTH            (JCW)
    ) wr_ptr_counter_gray(
        .clk            (axi_wr_aclk),
        .rst_n          (axi_wr_aresetn),
        .enable         (w_write && !r_wr_full),
        .counter_gray   (r_wr_ptr_gray)
    );

    counter_johnson #(
        .WIDTH            (JCW)
    ) rd_ptr_counter_gray(
        .clk            (axi_rd_aclk),
        .rst_n          (axi_rd_aresetn),
        .enable         (w_read && !r_rd_empty),
        .counter_gray   (r_rd_ptr_gray)
    );

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the clock crossing modules
    glitch_free_n_dff_arn #(
        .FLOP_COUNT          (N_FLOP_CROSS),
        .WIDTH               (JCW)
    ) rd_ptr_gray_cross_inst(
        .q                 (r_wdom_rd_ptr_gray),
        .d                 (r_rd_ptr_gray),
        .clk               (axi_wr_aclk),
        .rst_n             (axi_wr_aresetn)
    );

    // convert the gray rd ptr to binary
    grayj2bin #(
        .JCW               (JCW),
        .WIDTH             (AW + 1),
        .INSTANCE_NAME     ("rd_ptr_johnson2bin_inst")
    ) rd_ptr_gray2bin_inst(
        .binary         (w_wdom_rd_ptr_bin),
        .gray            (r_wdom_rd_ptr_gray),
        .clk             (axi_wr_aclk),
        .rst_n           (axi_wr_aresetn)
    );

    glitch_free_n_dff_arn #(
        .FLOP_COUNT          (N_FLOP_CROSS),
        .WIDTH               (JCW)
    ) wr_ptr_gray_cross_inst(
        .q                 (r_rdom_wr_ptr_gray),
        .d                 (r_wr_ptr_gray),
        .clk               (axi_rd_aclk),
        .rst_n             (axi_rd_aresetn)
    );

    // convert the gray wr ptr to binary
    grayj2bin #(
        .JCW               (JCW),
        .WIDTH             (AW + 1),
        .INSTANCE_NAME     ("wr_ptr_gray2bin_inst")
    ) wr_ptr_gray2bin_inst(
        .binary         (w_rdom_wr_ptr_bin),
        .gray            (r_rdom_wr_ptr_gray),
        .clk             (axi_rd_aclk),
        .rst_n           (axi_rd_aresetn)
    );

    /////////////////////////////////////////////////////////////////////////
    // assign read/write addresses
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

    /////////////////////////////////////////////////////////////////////////
    // Memory Flops
    always_ff @(posedge axi_wr_aclk) begin
        if (w_write && !r_wr_full) r_mem[r_wr_addr] <= wr_data;
    end

    assign w_rd_data = r_mem[r_rd_addr];

    /////////////////////////////////////////////////////////////////////////
    // Read Port
    generate
        if (REGISTERED != 0) begin : gen_flop_mode
            // Flop mode - registered output
            always_ff @(posedge axi_rd_aclk or negedge axi_rd_aresetn) begin
                if (!axi_rd_aresetn)
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
        .wr_clk           (axi_wr_aclk),
        .wr_rst_n         (axi_wr_aresetn),
        .rd_clk           (axi_rd_aclk),
        .rd_rst_n         (axi_rd_aresetn),
        .wr_ptr_bin      (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin (w_wdom_rd_ptr_bin),
        .rd_ptr_bin      (w_rd_ptr_bin_next),
        .rdom_wr_ptr_bin (w_rdom_wr_ptr_bin),
        .wr_full          (r_wr_full),
        .wr_almost_full   (r_wr_almost_full),
        .rd_empty         (r_rd_empty),
        .rd_almost_empty  (r_rd_almost_empty),
        .count           (w_count)
    );

    assign wr_ready = !r_wr_full;
    assign rd_valid = !r_rd_empty;

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

    always @(posedge axi_wr_aclk) begin
        if (!axi_wr_aresetn && (w_write && r_wr_full) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always @(posedge axi_rd_aclk) begin
        if (!axi_wr_aresetn && (w_read && r_rd_empty) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s read while fifo empty, %t", INSTANCE_NAME, $time);
        end
    end
    // synopsys translate_on

endmodule : gaxi_fifo_async
