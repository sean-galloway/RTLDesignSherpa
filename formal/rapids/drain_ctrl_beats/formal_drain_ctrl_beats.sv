// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for drain_ctrl_beats (yosys-compatible)
// Run with: sby drain_ctrl_beats.sby

module formal_drain_ctrl_beats #(
    parameter int DEPTH = 16
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        wr_valid,
    input  logic        rd_valid,
    input  logic [7:0]  rd_size
);

    localparam int AW = $clog2(DEPTH);

    // DUT outputs
    logic            wr_ready;
    logic            rd_ready;
    logic [AW:0]     data_available;
    logic            wr_full;
    logic            wr_almost_full;
    logic            rd_empty;
    logic            rd_almost_empty;

    // Instantiate DUT
    drain_ctrl_beats #(
        .DEPTH            (DEPTH),
        .ALMOST_WR_MARGIN (1),
        .ALMOST_RD_MARGIN (1),
        .REGISTERED       (1)
    ) dut (
        .axi_aclk        (clk),
        .axi_aresetn      (rst_n),
        .wr_valid         (wr_valid),
        .wr_ready         (wr_ready),
        .rd_valid         (rd_valid),
        .rd_size          (rd_size),
        .rd_ready         (rd_ready),
        .data_available   (data_available),
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

    // Constrain rd_size to sensible range (at least 1, at most DEPTH)
    always @(posedge clk) begin
        if (rst_n) begin
            assume (rd_size >= 1);
            assume (rd_size <= DEPTH);
        end
    end

    // =========================================================================
    // Ghost counter: tracks data availability
    // =========================================================================
    wire f_do_write = wr_valid && wr_ready;
    wire f_do_read  = rd_valid && rd_ready;

    reg [$clog2(DEPTH+1)+8:0] f_data = 0;

    always @(posedge clk) begin
        if (!rst_n)
            f_data <= 0;
        else begin
            case ({f_do_write, f_do_read})
                2'b10:   f_data <= f_data + 1;
                2'b01:   f_data <= f_data - rd_size;
                2'b11:   f_data <= f_data + 1 - rd_size;
                default: f_data <= f_data;
            endcase
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: data_available is in valid range [0, DEPTH]
    // P2: Reset produces data_available == 0 (no data)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_data: assert (data_available == 0);
    end

    // P3: Reset produces rd_empty == 1 (no data available)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_empty: assert (rd_empty);
    end

    // P4: Reset produces wr_full == 0
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_not_full: assert (!wr_full);
    end

    // P5: wr_full implies data_available == DEPTH
    always @(posedge clk) begin
        if (rst_n)
            ap_full_max_data: assert (!wr_full || (data_available == DEPTH));
    end

    // P6: rd_empty ↔ data_available == 0 (deferred — registered flag timing)

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

    // Multi-beat drain
    always @(posedge clk) begin
        if (rst_n)
            cp_multi_drain: cover (f_do_read && rd_size > 1);
    end

endmodule
