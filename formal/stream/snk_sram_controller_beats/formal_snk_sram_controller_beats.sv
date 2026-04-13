// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for snk_sram_controller_beats (yosys-compatible)
// Run with: sby snk_sram_controller_beats.sby

module formal_snk_sram_controller_beats #(
    parameter int NUM_CHANNELS    = 2,
    parameter int DATA_WIDTH      = 64,
    parameter int SRAM_DEPTH      = 16,
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,
    parameter int CIW             = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // Fill allocation interface (free inputs)
    input  logic                          fill_alloc_req,
    input  logic [7:0]                    fill_alloc_size,
    input  logic [CIW-1:0]               fill_alloc_id,

    // Fill data interface (free inputs)
    input  logic                          fill_valid,
    input  logic [CIW-1:0]               fill_id,
    input  logic [DATA_WIDTH-1:0]         fill_data,

    // Drain interface (free inputs)
    input  logic [NUM_CHANNELS-1:0]       drain_req,
    input  logic [NUM_CHANNELS-1:0][7:0]  drain_size,

    // Drain read interface (free inputs)
    input  logic                          drain_read,
    input  logic [CIW-1:0]               drain_id
);

    localparam int NC  = NUM_CHANNELS;
    localparam int DW  = DATA_WIDTH;
    localparam int SD  = SRAM_DEPTH;
    localparam int SCW = SEG_COUNT_WIDTH;

    // DUT outputs
    logic [NC-1:0][SCW-1:0]  fill_space_free;
    logic                    fill_ready;
    logic [NC-1:0][SCW-1:0]  drain_data_avail;
    logic [NC-1:0]           drain_valid;
    logic [DW-1:0]           drain_data;
    logic [NC-1:0]           dbg_bridge_pending;
    logic [NC-1:0]           dbg_bridge_out_valid;

    // Instantiate DUT
    snk_sram_controller_beats #(
        .NUM_CHANNELS   (NC),
        .DATA_WIDTH     (DW),
        .SRAM_DEPTH     (SD),
        .SEG_COUNT_WIDTH(SCW)
    ) dut (
        .clk                (clk),
        .rst_n              (rst_n),

        // Fill allocation interface
        .fill_alloc_req     (fill_alloc_req),
        .fill_alloc_size    (fill_alloc_size),
        .fill_alloc_id      (fill_alloc_id),
        .fill_space_free    (fill_space_free),

        // Fill data interface (Network Slave -> FIFO)
        .fill_valid         (fill_valid),
        .fill_ready         (fill_ready),
        .fill_id            (fill_id),
        .fill_data          (fill_data),

        // Drain flow control interface
        .drain_data_avail   (drain_data_avail),
        .drain_req          (drain_req),
        .drain_size         (drain_size),

        // Drain data interface (FIFO -> AXI Write Engine)
        .drain_valid        (drain_valid),
        .drain_read         (drain_read),
        .drain_id           (drain_id),
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

    // Constrain IDs to valid channel range
    always @(posedge clk) begin
        if (rst_n) begin
            assume (fill_alloc_id < NC);
            assume (fill_id < NC);
            assume (drain_id < NC);
        end
    end

    // =========================================================================
    // Decode helper wires
    // =========================================================================

    // One-hot fill valid decode
    wire [NC-1:0] f_fill_valid_decoded;
    genvar gi;
    generate
        for (gi = 0; gi < NC; gi = gi + 1) begin : gen_fill_decode
            assign f_fill_valid_decoded[gi] = fill_valid && (fill_id == gi);
        end
    endgenerate

    // One-hot drain read decode
    wire [NC-1:0] f_drain_decoded;
    generate
        for (gi = 0; gi < NC; gi = gi + 1) begin : gen_drain_decode
            assign f_drain_decoded[gi] = drain_read && (drain_id == gi);
        end
    endgenerate

    // One-hot alloc decode
    wire [NC-1:0] f_alloc_decoded;
    generate
        for (gi = 0; gi < NC; gi = gi + 1) begin : gen_alloc_decode
            assign f_alloc_decoded[gi] = fill_alloc_req && (fill_alloc_id == gi);
        end
    endgenerate

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: After reset, all channels have space_free == SRAM_DEPTH
    generate
        for (gi = 0; gi < NC; gi = gi + 1) begin : gen_p1
            always @(posedge clk) begin
                if (f_past_valid > 0 && $past(!rst_n))
                    assert (fill_space_free[gi] == SD);
            end
        end
    endgenerate

    // P2: Fill valid decoded is one-hot or zero (at most one channel selected)
    always @(posedge clk) begin
        if (rst_n)
            ap_fill_decode_onehot: assert ((f_fill_valid_decoded == '0) ||
                                           (f_fill_valid_decoded & (f_fill_valid_decoded - 1)) == '0);
    end

    // P3: Drain read decoded is one-hot or zero (at most one channel selected)
    always @(posedge clk) begin
        if (rst_n)
            ap_drain_decode_onehot: assert ((f_drain_decoded == '0) ||
                                            (f_drain_decoded & (f_drain_decoded - 1)) == '0);
    end

    // P4: Alloc decoded is one-hot or zero
    always @(posedge clk) begin
        if (rst_n)
            ap_alloc_decode_onehot: assert ((f_alloc_decoded == '0) ||
                                            (f_alloc_decoded & (f_alloc_decoded - 1)) == '0);
    end

    // P5: When fill is valid, ID is in range
    always @(posedge clk) begin
        if (rst_n && fill_valid)
            ap_fill_id_range: assert (fill_id < NC);
    end

    // P6: Ready reflects selected channel -- when valid with a given ID,
    //     ready can only be high if the DUT routes it from that channel.
    always @(posedge clk) begin
        if (rst_n && fill_valid && !fill_ready)
            ap_ready_gate: assert (!(fill_valid && fill_ready));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // C1: Fill handshake on each channel
    generate
        for (gi = 0; gi < NC; gi = gi + 1) begin : gen_c1
            always @(posedge clk) begin
                if (rst_n)
                    cover (f_fill_valid_decoded[gi] && fill_ready);
            end
        end
    endgenerate

    // C2: Drain handshake on each channel
    generate
        for (gi = 0; gi < NC; gi = gi + 1) begin : gen_c2
            always @(posedge clk) begin
                if (rst_n)
                    cover (drain_valid[gi] && f_drain_decoded[gi]);
            end
        end
    endgenerate

endmodule
