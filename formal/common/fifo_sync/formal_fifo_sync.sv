// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for fifo_sync (yosys-compatible)
// Run with: sby fifo_sync.sby

module formal_fifo_sync #(
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 4
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    write,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    input  logic                    read
);

    // DUT outputs
    logic                    wr_full;
    logic                    wr_almost_full;
    logic [DATA_WIDTH-1:0]   rd_data;
    logic                    rd_empty;
    logic                    rd_almost_empty;

    // Instantiate DUT
    fifo_sync #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH),
        .REGISTERED(0),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1)
    ) dut (
        .clk              (clk),
        .rst_n            (rst_n),
        .write            (write),
        .wr_data          (wr_data),
        .wr_full          (wr_full),
        .wr_almost_full   (wr_almost_full),
        .read             (read),
        .rd_data          (rd_data),
        .rd_empty         (rd_empty),
        .rd_almost_empty  (rd_almost_empty)
    );

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
            assume (!(write && wr_full));
            assume (!(read && rd_empty));
        end
    end

    // =========================================================================
    // Ghost counter
    // =========================================================================
    reg [$clog2(DEPTH+1):0] f_count = 0;

    always @(posedge clk) begin
        if (!rst_n)
            f_count <= 0;
        else case ({write && !wr_full, read && !rd_empty})
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
            if ($past(write && !wr_full && !(read && !rd_empty)))
                ap_write_inc: assert (f_count == $past(f_count) + 1);
    end

    // Read decrements
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(read && !rd_empty && !(write && !wr_full)))
                ap_read_dec: assert (f_count == $past(f_count) - 1);
    end

    // Simultaneous preserves
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(write && !wr_full && read && !rd_empty))
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
        if (rst_n) cp_rw: cover (write && read && !wr_full && !rd_empty);
    end

    always @(posedge clk) begin
        if (rst_n) cp_half: cover (f_count == DEPTH / 2);
    end

endmodule
