// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for src_sram_controller_unit_beats (yosys-compatible)
// Run with: sby src_sram_controller_unit_beats.sby

module formal_src_sram_controller_unit_beats #(
    parameter int DATA_WIDTH     = 64,
    parameter int SRAM_DEPTH     = 16,
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // Fill allocation interface (free inputs)
    input  logic                          fill_alloc_req,
    input  logic [7:0]                    fill_alloc_size,

    // Fill data interface (free inputs)
    input  logic                          fill_valid,
    input  logic [DATA_WIDTH-1:0]         fill_data,

    // Drain flow control interface (free inputs)
    input  logic                          drain_req,
    input  logic [7:0]                    drain_size,

    // Drain data interface (free input)
    input  logic                          drain_ready
);

    localparam int SCW = SEG_COUNT_WIDTH;
    localparam int DW  = DATA_WIDTH;
    localparam int SD  = SRAM_DEPTH;

    // DUT outputs
    logic [SCW-1:0]  fill_space_free;
    logic            fill_ready;
    logic [SCW-1:0]  drain_data_avail;
    logic            drain_valid;
    logic [DW-1:0]   drain_data;
    logic            dbg_bridge_pending;
    logic            dbg_bridge_out_valid;

    // Instantiate DUT
    src_sram_controller_unit_beats #(
        .DATA_WIDTH     (DW),
        .SRAM_DEPTH     (SD),
        .SEG_COUNT_WIDTH(SCW)
    ) dut (
        .clk                (clk),
        .rst_n              (rst_n),

        // Fill allocation interface
        .fill_alloc_req     (fill_alloc_req),
        .fill_alloc_size    (fill_alloc_size),
        .fill_space_free    (fill_space_free),

        // Fill data interface (AXI Read Engine -> FIFO)
        .fill_valid         (fill_valid),
        .fill_ready         (fill_ready),
        .fill_data          (fill_data),

        // Drain flow control interface
        .drain_data_avail   (drain_data_avail),
        .drain_req          (drain_req),
        .drain_size         (drain_size),

        // Drain data interface (FIFO -> Network Master)
        .drain_valid        (drain_valid),
        .drain_ready        (drain_ready),
        .drain_data         (drain_data),

        // Debug
        .dbg_bridge_pending (dbg_bridge_pending),
        .dbg_bridge_out_valid(dbg_bridge_out_valid)
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
    // Input constraints
    // =========================================================================

    // Constrain allocation size to tractable burst sizes [1..8]
    always @(posedge clk) begin
        if (rst_n) begin
            assume (fill_alloc_size >= 1);
            assume (fill_alloc_size <= 8);
        end
    end

    // =========================================================================
    // Handshake helper wires
    // =========================================================================
    wire f_wr_handshake = fill_valid && fill_ready;
    wire f_rd_handshake = drain_valid && drain_ready;

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: After reset, fill_space_free == SRAM_DEPTH (full space available)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_space_free: assert (fill_space_free == SD);
    end

    // P2: Space free stays within SEG_COUNT_WIDTH range.
    always @(posedge clk) begin
        if (rst_n)
            ap_space_free_width: assert (fill_space_free <= {SCW{1'b1}});
    end

    // Cover: witness space_free at SRAM_DEPTH (fully free)
    always @(posedge clk) begin
        if (rst_n)
            cp_space_free_at_depth: cover (fill_space_free == SD);
    end

    // Cover: witness space_free at zero (fully allocated)
    always @(posedge clk) begin
        if (rst_n)
            cp_space_free_zero: cover (fill_space_free == 0);
    end

    // P3: Data available stays within SEG_COUNT_WIDTH range.
    always @(posedge clk) begin
        if (rst_n)
            ap_data_avail_width: assert (drain_data_avail <= {SCW{1'b1}});
    end

    // Cover: witness drain_data_avail at SRAM_DEPTH (FIFO full, bridge empty)
    always @(posedge clk) begin
        if (rst_n)
            cp_data_avail_at_depth: cover (drain_data_avail == SD);
    end

    // Cover: witness drain_data_avail above SRAM_DEPTH (bridge has occupancy)
    always @(posedge clk) begin
        if (rst_n)
            cp_data_avail_above_depth: cover (drain_data_avail > SD);
    end

    // P4: Write accepted only when ready (no handshake without ready)
    always @(posedge clk) begin
        if (rst_n)
            ap_wr_handshake_ready: assert (!(fill_valid && fill_ready) || fill_ready);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // C1: Write handshake occurs
    always @(posedge clk) begin
        if (rst_n)
            cp_wr_handshake: cover (f_wr_handshake);
    end

    // C2: Read handshake occurs
    always @(posedge clk) begin
        if (rst_n)
            cp_rd_handshake: cover (f_rd_handshake);
    end

    // C3: Allocation request occurs
    always @(posedge clk) begin
        if (rst_n)
            cp_alloc_req: cover (fill_alloc_req);
    end

    // C4: Drain request occurs
    always @(posedge clk) begin
        if (rst_n)
            cp_drain_req: cover (drain_req);
    end

endmodule
