// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for gaxi_fifo_sync (yosys-compatible)
// Run with: sby gaxi_fifo_sync.sby

module formal_gaxi_fifo_sync #(
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 4
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    wr_valid,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    input  logic                    rd_ready
);

    localparam int AW = $clog2(DEPTH);

    // DUT outputs
    logic            wr_ready;
    logic [AW:0]     count;
    logic            rd_valid;
    logic [DATA_WIDTH-1:0] rd_data;

    // Instantiate DUT
    gaxi_fifo_sync #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH),
        .REGISTERED(0),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1)
    ) dut (
        .axi_aclk     (clk),
        .axi_aresetn  (rst_n),
        .wr_valid     (wr_valid),
        .wr_ready     (wr_ready),
        .wr_data      (wr_data),
        .rd_ready     (rd_ready),
        .count        (count),
        .rd_valid     (rd_valid),
        .rd_data      (rd_data)
    );

    // Derive full/empty from valid/ready interface
    wire wr_full  = !wr_ready;
    wire rd_empty = !rd_valid;

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // Well-behaved environment
    always @(posedge clk) begin
        if (rst_n) begin
            assume (!(wr_valid && wr_full));
            assume (!(rd_ready && rd_empty));
        end
    end

    // =========================================================================
    // Ghost counter
    // =========================================================================
    wire f_do_write = wr_valid && wr_ready;
    wire f_do_read  = rd_valid && rd_ready;

    reg [$clog2(DEPTH+1):0] f_count = 0;

    always @(posedge clk) begin
        if (!rst_n)
            f_count <= 0;
        else case ({f_do_write, f_do_read})
            2'b10:   f_count <= f_count + 1;
            2'b01:   f_count <= f_count - 1;
            default: f_count <= f_count;
        endcase
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Empty flag matches ghost count
    always @(posedge clk) begin
        if (rst_n)
            ap_empty: assert (rd_empty == (f_count == 0));
    end

    // Full flag matches ghost count
    always @(posedge clk) begin
        if (rst_n)
            ap_full: assert (wr_full == (f_count == DEPTH));
    end

    // Count in range
    always @(posedge clk) begin
        if (rst_n)
            ap_range: assert (f_count <= DEPTH);
    end

    // Reset produces empty
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_empty: assert (rd_empty);
    end

    // Reset produces not-full
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_not_full: assert (!wr_full);
    end

    // Mutual exclusion
    always @(posedge clk) begin
        if (rst_n)
            ap_mutex: assert (!(wr_full && rd_empty));
    end

    // Write increments
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(f_do_write && !f_do_read))
                ap_write_inc: assert (f_count == $past(f_count) + 1);
    end

    // Read decrements
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(f_do_read && !f_do_write))
                ap_read_dec: assert (f_count == $past(f_count) - 1);
    end

    // Simultaneous preserves
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(f_do_write && f_do_read))
                ap_rw: assert (f_count == $past(f_count));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    always @(posedge clk) begin
        if (rst_n) cp_full: cover (wr_full);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n)
            cp_drain: cover (rd_empty && $past(!rd_empty));
    end

    always @(posedge clk) begin
        if (rst_n) cp_rw: cover (f_do_write && f_do_read);
    end

    always @(posedge clk) begin
        if (rst_n) cp_half: cover (f_count == DEPTH / 2);
    end

endmodule
