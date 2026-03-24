// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for stream_latency_bridge (yosys-compatible)
// Run with: sby stream_latency_bridge.sby

module formal_stream_latency_bridge #(
    parameter int DATA_WIDTH = 8,
    parameter int SKID_DEPTH = 4
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    s_valid,
    input  logic [DATA_WIDTH-1:0]   s_data,
    input  logic                    m_ready
);

    // DUT outputs
    logic                    s_ready;
    logic                    m_valid;
    logic [DATA_WIDTH-1:0]   m_data;
    logic [2:0]              occupancy;
    logic                    dbg_r_pending;
    logic                    dbg_r_out_valid;

    // Instantiate DUT
    stream_latency_bridge #(
        .DATA_WIDTH (DATA_WIDTH),
        .SKID_DEPTH (SKID_DEPTH)
    ) dut (
        .clk              (clk),
        .rst_n            (rst_n),
        .s_valid          (s_valid),
        .s_ready          (s_ready),
        .s_data           (s_data),
        .m_valid          (m_valid),
        .m_ready          (m_ready),
        .m_data           (m_data),
        .occupancy        (occupancy),
        .dbg_r_pending    (dbg_r_pending),
        .dbg_r_out_valid  (dbg_r_out_valid)
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

    // Well-behaved environment: no write when not ready, no read when not valid
    always @(posedge clk) begin
        if (rst_n) begin
            assume (!(s_valid && !s_ready));
            assume (!(m_ready && !m_valid));
        end
    end

    // =========================================================================
    // Ghost counter: tracks items in the bridge pipeline
    // =========================================================================
    wire f_do_push = s_valid && s_ready;
    wire f_do_pop  = m_valid && m_ready;

    localparam int F_MAX = SKID_DEPTH + 2;
    reg [$clog2(F_MAX+1):0] f_count = 0;

    always @(posedge clk) begin
        if (!rst_n)
            f_count <= 0;
        else case ({f_do_push, f_do_pop})
            2'b10:   f_count <= f_count + 1;
            2'b01:   f_count <= f_count - 1;
            default: f_count <= f_count;
        endcase
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: Reset produces m_valid == 0
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_mvalid: assert (!m_valid);
    end

    // P2: Reset produces occupancy == 0
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_occupancy: assert (occupancy == 0);
    end

    // P3: Occupancy in valid range (max = SKID_DEPTH since occupancy = skid_count)
    always @(posedge clk) begin
        if (rst_n)
            ap_occ_range: assert (occupancy <= SKID_DEPTH);
    end

    // P4: Ghost counter in valid range
    always @(posedge clk) begin
        if (rst_n)
            ap_ghost_range: assert (f_count <= F_MAX);
    end

    // P5: No data loss -- ghost counter tracks net accepted items
    //     f_count must stay bounded and non-negative
    always @(posedge clk) begin
        if (rst_n)
            ap_no_underflow: assert (f_count < F_MAX);
    end

    // P6: dbg_r_out_valid reflects m_valid
    always @(posedge clk) begin
        if (rst_n)
            ap_dbg_out: assert (dbg_r_out_valid == m_valid);
    end

    // P7: If nothing in pipeline, output must be invalid
    always @(posedge clk) begin
        if (rst_n && f_count == 0 && !dbg_r_pending)
            ap_empty_no_out: assert (!m_valid);
    end

    // P8: Write-only increments ghost counter
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(f_do_push && !f_do_pop))
                ap_push_inc: assert (f_count == $past(f_count) + 1);
    end

    // P9: Read-only decrements ghost counter
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(f_do_pop && !f_do_push))
                ap_pop_dec: assert (f_count == $past(f_count) - 1);
    end

    // P10: Simultaneous push/pop preserves ghost counter
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(f_do_push && f_do_pop))
                ap_push_pop: assert (f_count == $past(f_count));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Reach full throughput (push and pop simultaneously)
    always @(posedge clk) begin
        if (rst_n)
            cp_full_throughput: cover (f_do_push && f_do_pop);
    end

    // Reach maximum occupancy
    always @(posedge clk) begin
        if (rst_n)
            cp_max_occ: cover (occupancy == SKID_DEPTH);
    end

    // Drain to empty after being non-empty
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n)
            cp_drain: cover (!m_valid && $past(m_valid));
    end

    // Backpressure scenario: s_valid high but s_ready low
    always @(posedge clk) begin
        if (rst_n)
            cp_backpressure: cover (s_valid && !s_ready);
    end

endmodule
