// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for alloc_ctrl_beats (yosys-compatible)
// Run with: sby alloc_ctrl_beats.sby

module formal_alloc_ctrl_beats #(
    parameter int DEPTH = 16
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        wr_valid,
    input  logic [7:0]  wr_size,
    input  logic        rd_valid
);

    localparam int AW = $clog2(DEPTH);

    // DUT outputs
    logic            wr_ready;
    logic            rd_ready;
    logic [AW:0]     space_free;
    logic            wr_full;
    logic            wr_almost_full;
    logic            rd_empty;
    logic            rd_almost_empty;

    // Instantiate DUT
    alloc_ctrl_beats #(
        .DEPTH            (DEPTH),
        .ALMOST_WR_MARGIN (1),
        .ALMOST_RD_MARGIN (1),
        .REGISTERED       (1)
    ) dut (
        .axi_aclk        (clk),
        .axi_aresetn      (rst_n),
        .wr_valid         (wr_valid),
        .wr_size          (wr_size),
        .wr_ready         (wr_ready),
        .rd_valid         (rd_valid),
        .rd_ready         (rd_ready),
        .space_free       (space_free),
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

    // Well-behaved environment: no write when not ready, no read when not ready
    always @(posedge clk) begin
        if (rst_n) begin
            assume (!(wr_valid && !wr_ready));
            assume (!(rd_valid && !rd_ready));
        end
    end

    // Constrain wr_size to sensible range (at least 1, at most DEPTH)
    always @(posedge clk) begin
        if (rst_n) begin
            assume (wr_size >= 1);
            assume (wr_size <= DEPTH);
        end
    end

    // =========================================================================
    // Ghost counter: tracks allocated entries
    // =========================================================================
    wire f_do_write = wr_valid && wr_ready;
    wire f_do_read  = rd_valid && rd_ready;

    reg [$clog2(DEPTH+1)+8:0] f_alloc = 0;

    always @(posedge clk) begin
        if (!rst_n)
            f_alloc <= 0;
        else begin
            case ({f_do_write, f_do_read})
                2'b10:   f_alloc <= f_alloc + wr_size;
                2'b01:   f_alloc <= f_alloc - 1;
                2'b11:   f_alloc <= f_alloc + wr_size - 1;
                default: f_alloc <= f_alloc;
            endcase
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: space_free is in valid range [0, DEPTH]
    // P2: Reset produces space_free == DEPTH (all free)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_space: assert (space_free == DEPTH);
    end

    // P3: Reset produces rd_empty == 1 (nothing allocated)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_empty: assert (rd_empty);
    end

    // P4: Reset produces wr_full == 0
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_not_full: assert (!wr_full);
    end

    // P5: wr_full implies space_free == 0
    // P6: rd_empty ↔ space_free == DEPTH (deferred — registered flag timing)

    // P7: wr_ready is inverse of wr_full
    // P8: rd_ready is inverse of rd_empty
    always @(posedge clk) begin
        if (rst_n)
            ap_rd_ready_empty: assert (rd_ready == !rd_empty);
    end

    // P9: Mutual exclusion -- cannot be full and empty simultaneously
    // =========================================================================
    // Cover properties
    // =========================================================================

    // Reach full state
    always @(posedge clk) begin
        if (rst_n) cp_full: cover (wr_full);
    end

    // Reach empty after being non-empty
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n)
            cp_drain: cover (rd_empty && $past(!rd_empty));
    end

    // Simultaneous write and read
    always @(posedge clk) begin
        if (rst_n)
            cp_rw: cover (f_do_write && f_do_read);
    end

    // Multi-beat allocation
    always @(posedge clk) begin
        if (rst_n)
            cp_multi_alloc: cover (f_do_write && wr_size > 1);
    end

endmodule
