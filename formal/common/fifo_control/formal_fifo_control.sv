// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for fifo_control (yosys-compatible)
// Models single-clock operation for formal verification.
// Uses the same pointer-feeding pattern as fifo_sync (next pointers).
// Run with: sby fifo_control.sby

module formal_fifo_control #(
    parameter int ADDR_WIDTH       = 3,
    parameter int DEPTH            = 8,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter int REGISTERED       = 0
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    write,
    input  logic                    read
);

    localparam int AW = ADDR_WIDTH;
    localparam int D  = DEPTH;

    // DUT outputs
    logic [AW:0] count;
    logic        wr_full;
    logic        wr_almost_full;
    logic        rd_empty;
    logic        rd_almost_empty;

    // =========================================================================
    // Pointer generation using counter_bin-like wraparound
    // We replicate the fifo_sync pattern: feed NEXT (combinational) pointers
    // to fifo_control, which is how fifo_sync uses it.
    // =========================================================================
    reg [AW:0] r_wr_ptr = 0;
    reg [AW:0] r_rd_ptr = 0;

    // Compute next pointer values (combinational, same as counter_bin)
    wire [AW:0] w_wr_ptr_next;
    wire [AW:0] w_rd_ptr_next;

    // Write pointer next
    wire w_do_write = write && !wr_full;
    assign w_wr_ptr_next = !w_do_write ? r_wr_ptr :
        (r_wr_ptr[AW-1:0] == AW'(D - 1)) ?
            {~r_wr_ptr[AW], {AW{1'b0}}} :
            r_wr_ptr + 1;

    // Read pointer next
    wire w_do_read = read && !rd_empty;
    assign w_rd_ptr_next = !w_do_read ? r_rd_ptr :
        (r_rd_ptr[AW-1:0] == AW'(D - 1)) ?
            {~r_rd_ptr[AW], {AW{1'b0}}} :
            r_rd_ptr + 1;

    // Register the pointers
    always @(posedge clk) begin
        if (!rst_n) begin
            r_wr_ptr <= 0;
            r_rd_ptr <= 0;
        end else begin
            r_wr_ptr <= w_wr_ptr_next;
            r_rd_ptr <= w_rd_ptr_next;
        end
    end

    // Instantiate DUT with single clock, feeding NEXT pointers
    fifo_control #(
        .ADDR_WIDTH       (ADDR_WIDTH),
        .DEPTH            (DEPTH),
        .ALMOST_WR_MARGIN (ALMOST_WR_MARGIN),
        .ALMOST_RD_MARGIN (ALMOST_RD_MARGIN),
        .REGISTERED       (REGISTERED)
    ) dut (
        .wr_clk           (clk),
        .wr_rst_n         (rst_n),
        .rd_clk           (clk),
        .rd_rst_n         (rst_n),
        .wr_ptr_bin       (w_wr_ptr_next),
        .wdom_rd_ptr_bin  (w_rd_ptr_next),
        .rd_ptr_bin       (w_rd_ptr_next),
        .rdom_wr_ptr_bin  (w_wr_ptr_next),
        .count            (count),
        .wr_full          (wr_full),
        .wr_almost_full   (wr_almost_full),
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
        else case ({w_do_write, w_do_read})
            2'b10:   f_count <= f_count + 1;
            2'b01:   f_count <= f_count - 1;
            default: f_count <= f_count;
        endcase
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset, empty is asserted
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_empty: assert (rd_empty);
    end

    // After reset, full is deasserted
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_not_full: assert (!wr_full);
    end

    // Full and empty mutually exclusive
    always @(posedge clk) begin
        if (rst_n)
            ap_mutex: assert (!(wr_full && rd_empty));
    end

    // Ghost count in valid range
    always @(posedge clk) begin
        if (rst_n)
            ap_count_range: assert (f_count <= D);
    end

    // Empty matches ghost count
    always @(posedge clk) begin
        if (rst_n)
            ap_empty_def: assert (rd_empty == (f_count == 0));
    end

    // Full matches ghost count
    always @(posedge clk) begin
        if (rst_n)
            ap_full_def: assert (wr_full == (f_count == D));
    end

    // Write increments ghost count
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(w_do_write) && !$past(w_do_read))
                ap_write_inc: assert (f_count == $past(f_count) + 1);
    end

    // Read decrements ghost count
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(w_do_read) && !$past(w_do_write))
                ap_read_dec: assert (f_count == $past(f_count) - 1);
    end

    // Simultaneous read/write preserves count
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(w_do_write) && $past(w_do_read))
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
            cp_empty: cover (rd_empty && $past(!rd_empty));
    end

    always @(posedge clk) begin
        if (rst_n) cp_almost_full: cover (wr_almost_full && !wr_full);
    end

    always @(posedge clk) begin
        if (rst_n) cp_almost_empty: cover (rd_almost_empty && !rd_empty);
    end

endmodule
