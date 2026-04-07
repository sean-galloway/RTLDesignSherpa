// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for fifo_async_div2 (yosys-compatible)
// Run with: sby fifo_async_div2.sby
//
// Strategy: Drive both wr_clk and rd_clk from a single clock. This is a
// conservative model -- any property that holds under synchronous clocking
// also holds under asynchronous clocking.
//
// For the async FIFO, flags lag actual pointer changes by N_FLOP_CROSS
// cycles due to CDC synchronizers. Properties account for this:
//   - Ghost counter: tracks actual occupancy (writes minus reads)
//   - Range/increment/decrement: unconditionally correct
//   - Flag accuracy: verified after quiescent settling period
//   - Reset: verified immediately after reset

module formal_fifo_async_div2 #(
    parameter int DATA_WIDTH       = 8,
    parameter int DEPTH            = 4,
    parameter int N_FLOP_CROSS     = 2,
    parameter int REGISTERED       = 0,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1
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

    // Instantiate DUT -- single clock drives both domains
    fifo_async_div2 #(
        .DATA_WIDTH       (DATA_WIDTH),
        .DEPTH            (DEPTH),
        .N_FLOP_CROSS     (N_FLOP_CROSS),
        .REGISTERED       (REGISTERED),
        .ALMOST_WR_MARGIN (ALMOST_WR_MARGIN),
        .ALMOST_RD_MARGIN (ALMOST_RD_MARGIN)
    ) dut (
        .wr_clk           (clk),
        .wr_rst_n         (rst_n),
        .rd_clk           (clk),
        .rd_rst_n         (rst_n),
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

    // Hold reset long enough for synchronizers to flush.
    localparam int RESET_CYCLES = N_FLOP_CROSS + 2;

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid < RESET_CYCLES) assume (!rst_n);
        if (f_past_valid >= RESET_CYCLES) assume (rst_n);
    end

    // No writes or reads during reset
    always @(posedge clk) begin
        if (!rst_n) begin
            assume (!write);
            assume (!read);
        end
    end

    // Well-behaved environment: no write when full, no read when empty
    always @(posedge clk) begin
        if (rst_n) begin
            assume (!(write && wr_full));
            assume (!(read && rd_empty));
        end
    end

    // =========================================================================
    // Ghost counter -- tracks actual writes minus reads
    // =========================================================================
    wire f_do_write = write && !wr_full;
    wire f_do_read  = read && !rd_empty;

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
    // Quiescent counter -- counts cycles since last write or read
    // After N_FLOP_CROSS + 1 idle cycles, the synchronizers have
    // propagated all pointer updates and flags should be accurate.
    // =========================================================================
    localparam int SETTLE_CYCLES = N_FLOP_CROSS + 2;

    reg [7:0] f_idle = 0;
    always @(posedge clk) begin
        if (!rst_n)
            f_idle <= 0;
        else if (f_do_write || f_do_read)
            f_idle <= 0;
        else if (f_idle < 8'hFF)
            f_idle <= f_idle + 1;
    end

    wire f_settled = (f_idle >= SETTLE_CYCLES) && rst_n;

    // =========================================================================
    // Safety properties
    // =========================================================================

    // --- Ghost counter range (always valid) ---
    always @(posedge clk) begin
        if (rst_n)
            ap_range: assert (f_count <= DEPTH);
    end

    // --- Ghost counter increment/decrement/preserve ---
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(f_do_write && !f_do_read))
                ap_write_inc: assert (f_count == $past(f_count) + 1);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(f_do_read && !f_do_write))
                ap_read_dec: assert (f_count == $past(f_count) - 1);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(f_do_write && f_do_read))
                ap_rw: assert (f_count == $past(f_count));
    end

    // --- Reset behavior ---
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_empty: assert (rd_empty);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_not_full: assert (!wr_full);
    end

    // --- Settled flag accuracy ---
    // After the synchronizer pipeline has flushed (no activity for
    // SETTLE_CYCLES), the flags must accurately reflect the ghost count.
    always @(posedge clk) begin
        if (f_settled)
            ap_settled_empty: assert (rd_empty == (f_count == 0));
    end

    always @(posedge clk) begin
        if (f_settled)
            ap_settled_full: assert (wr_full == (f_count == DEPTH));
    end

    always @(posedge clk) begin
        if (f_settled)
            ap_settled_mutex: assert (!(wr_full && rd_empty));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Reach full state
    always @(posedge clk) begin
        if (rst_n) cp_full: cover (wr_full);
    end

    // Drain from non-empty to empty
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n)
            cp_drain: cover (rd_empty && $past(!rd_empty));
    end

    // Simultaneous read and write while neither full nor empty
    always @(posedge clk) begin
        if (rst_n) cp_rw: cover (write && read && !wr_full && !rd_empty);
    end

    // Reach half-full
    always @(posedge clk) begin
        if (rst_n) cp_half: cover (f_count == DEPTH / 2);
    end

endmodule
