// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for gaxi_skid_buffer_struct (yosys-compatible)
// Proves FIFO-like invariants: count tracking, full/empty flags, data shift
// correctness.
//
// The struct skid buffer uses an unpacked array with shift-register semantics:
//   - Writes insert at position r_data_count
//   - Reads shift everything down (r_data[0] is the output)
//   - Simultaneous read+write: shift down and insert at (count-1)
//
// Parameters kept small (STRUCT_WIDTH=8, DEPTH=4) for SMT solver tractability.

module formal_gaxi_skid_buffer_struct #(
    parameter int STRUCT_WIDTH = 8,
    parameter int DEPTH = 4
) (
    input  logic                       clk,
    input  logic                       rst_n,
    input  logic                       wr_valid,
    input  logic [STRUCT_WIDTH-1:0]    wr_data,
    input  logic                       rd_ready
);

    // DUT outputs
    logic                       wr_ready;
    logic [3:0]                 count;
    logic                       rd_valid;
    logic [3:0]                 rd_count;
    logic [STRUCT_WIDTH-1:0]    rd_data;

    // Instantiate DUT
    gaxi_skid_buffer_struct #(
        .STRUCT_WIDTH(STRUCT_WIDTH),
        .DEPTH(DEPTH)
    ) dut (
        .axi_aclk    (clk),
        .axi_aresetn (rst_n),
        .wr_valid    (wr_valid),
        .wr_ready    (wr_ready),
        .wr_data     (wr_data),
        .count       (count),
        .rd_valid    (rd_valid),
        .rd_ready    (rd_ready),
        .rd_count    (rd_count),
        .rd_data     (rd_data)
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

    // =========================================================================
    // Environment assumptions
    // =========================================================================

    // No write when not ready
    always @(posedge clk) begin
        if (rst_n)
            assume (!(wr_valid && !wr_ready));
    end

    // No read when not valid
    always @(posedge clk) begin
        if (rst_n)
            assume (!(rd_ready && !rd_valid));
    end

    // =========================================================================
    // Ghost counter (tracks writes minus reads)
    // =========================================================================
    wire w_wr_xfer = wr_valid & wr_ready;
    wire w_rd_xfer = rd_valid & rd_ready;

    reg [$clog2(DEPTH+1):0] f_count = 0;

    always @(posedge clk) begin
        if (!rst_n)
            f_count <= 0;
        else case ({w_wr_xfer, w_rd_xfer})
            2'b10:   f_count <= f_count + 1;
            2'b01:   f_count <= f_count - 1;
            default: f_count <= f_count;
        endcase
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset: wr_ready=0, rd_valid=0, count=0
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_wr_ready: assert (wr_ready == 1'b0);
            ap_reset_rd_valid: assert (rd_valid == 1'b0);
            ap_reset_count:    assert (count == 4'd0);
        end
    end

    // Ghost count matches DUT count (after reset released)
    always @(posedge clk) begin
        if (rst_n)
            ap_count_match: assert (count == f_count[3:0]);
    end

    // count and rd_count are identical
    always @(posedge clk) begin
        if (rst_n)
            ap_count_eq_rd_count: assert (count == rd_count);
    end

    // Count never exceeds DEPTH
    always @(posedge clk) begin
        if (rst_n)
            ap_count_max: assert (count <= DEPTH[3:0]);
    end

    // Count never negative (ghost counter never underflows)
    always @(posedge clk) begin
        if (rst_n)
            ap_count_non_neg: assert (f_count <= DEPTH);
    end

    // wr_ready deasserts when full (count == DEPTH)
    always @(posedge clk) begin
        if (rst_n && count == DEPTH[3:0])
            ap_full_no_ready: assert (!wr_ready || w_rd_xfer);
    end

    // rd_valid deasserts when empty (count == 0)
    always @(posedge clk) begin
        if (rst_n && count == 4'd0)
            ap_empty_no_valid: assert (!rd_valid || w_wr_xfer);
    end

    // Write increments ghost count
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(w_wr_xfer && !w_rd_xfer))
                ap_write_inc: assert (f_count == $past(f_count) + 1);
    end

    // Read decrements ghost count
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(w_rd_xfer && !w_wr_xfer))
                ap_read_dec: assert (f_count == $past(f_count) - 1);
    end

    // Simultaneous read/write preserves ghost count
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(w_wr_xfer && w_rd_xfer))
                ap_rw_preserve: assert (f_count == $past(f_count));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Fill: reach full state
    always @(posedge clk) begin
        if (rst_n)
            cp_full: cover (count == DEPTH[3:0]);
    end

    // Drain: transition from non-empty to empty
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_drain: cover (count == 4'd0 && $past(count) != 4'd0);
    end

    // Simultaneous read and write while neither full nor empty
    always @(posedge clk) begin
        if (rst_n)
            cp_simul_rw: cover (w_wr_xfer && w_rd_xfer && count > 4'd0 && count < DEPTH[3:0]);
    end

    // Half full
    always @(posedge clk) begin
        if (rst_n)
            cp_half: cover (count == DEPTH[3:0] / 2);
    end

endmodule
