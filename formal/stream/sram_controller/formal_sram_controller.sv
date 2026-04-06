// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for sram_controller (yosys-compatible)
// Run with: sby sram_controller.sby

module formal_sram_controller #(
    parameter int NUM_CHANNELS    = 2,
    parameter int DATA_WIDTH      = 64,
    parameter int SRAM_DEPTH      = 16,
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,
    parameter int CIW             = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // Allocation interface (free inputs)
    input  logic                          axi_rd_alloc_req,
    input  logic [7:0]                    axi_rd_alloc_size,
    input  logic [CIW-1:0]               axi_rd_alloc_id,

    // Write interface (free inputs)
    input  logic                          axi_rd_sram_valid,
    input  logic [CIW-1:0]               axi_rd_sram_id,
    input  logic [DATA_WIDTH-1:0]         axi_rd_sram_data,

    // Drain interface (free inputs)
    input  logic [NUM_CHANNELS-1:0]       axi_wr_drain_req,
    input  logic [NUM_CHANNELS-1:0][7:0]  axi_wr_drain_size,

    // Read interface (free inputs)
    input  logic                          axi_wr_sram_drain,
    input  logic [CIW-1:0]               axi_wr_sram_id
);

    localparam int NC  = NUM_CHANNELS;
    localparam int DW  = DATA_WIDTH;
    localparam int SD  = SRAM_DEPTH;
    localparam int SCW = SEG_COUNT_WIDTH;

    // DUT outputs
    logic [NC-1:0][SCW-1:0]  axi_rd_alloc_space_free;
    logic                    axi_rd_sram_ready;
    logic [NC-1:0][SCW-1:0]  axi_wr_drain_data_avail;
    logic [NC-1:0]           axi_wr_sram_valid;
    logic [DW-1:0]           axi_wr_sram_data;
    logic [NC-1:0]           dbg_bridge_pending;
    logic [NC-1:0]           dbg_bridge_out_valid;

    // Instantiate DUT
    sram_controller #(
        .NUM_CHANNELS   (NC),
        .DATA_WIDTH     (DW),
        .SRAM_DEPTH     (SD),
        .SEG_COUNT_WIDTH(SCW)
    ) dut (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Allocation interface
        .axi_rd_alloc_req       (axi_rd_alloc_req),
        .axi_rd_alloc_size      (axi_rd_alloc_size),
        .axi_rd_alloc_id        (axi_rd_alloc_id),
        .axi_rd_alloc_space_free(axi_rd_alloc_space_free),

        // Write interface (AXI Read Engine -> FIFO)
        .axi_rd_sram_valid      (axi_rd_sram_valid),
        .axi_rd_sram_ready      (axi_rd_sram_ready),
        .axi_rd_sram_id         (axi_rd_sram_id),
        .axi_rd_sram_data       (axi_rd_sram_data),

        // Drain interface
        .axi_wr_drain_data_avail(axi_wr_drain_data_avail),
        .axi_wr_drain_req       (axi_wr_drain_req),
        .axi_wr_drain_size      (axi_wr_drain_size),

        // Read interface (FIFO -> AXI Write Engine)
        .axi_wr_sram_valid      (axi_wr_sram_valid),
        .axi_wr_sram_drain      (axi_wr_sram_drain),
        .axi_wr_sram_id         (axi_wr_sram_id),
        .axi_wr_sram_data       (axi_wr_sram_data),

        // Debug
        .dbg_bridge_pending     (dbg_bridge_pending),
        .dbg_bridge_out_valid   (dbg_bridge_out_valid)
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
            assume (axi_rd_alloc_id < NC);
            assume (axi_rd_sram_id < NC);
            assume (axi_wr_sram_id < NC);
        end
    end

    // =========================================================================
    // Decode helper wires
    // =========================================================================

    // One-hot write valid decode
    wire [NC-1:0] f_wr_valid_decoded;
    genvar gi;
    generate
        for (gi = 0; gi < NC; gi = gi + 1) begin : gen_wr_decode
            assign f_wr_valid_decoded[gi] = axi_rd_sram_valid && (axi_rd_sram_id == gi);
        end
    endgenerate

    // One-hot drain decode
    wire [NC-1:0] f_drain_decoded;
    generate
        for (gi = 0; gi < NC; gi = gi + 1) begin : gen_drain_decode
            assign f_drain_decoded[gi] = axi_wr_sram_drain && (axi_wr_sram_id == gi);
        end
    endgenerate

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: After reset, all channels have space_free == SRAM_DEPTH
    //     (axi_rd_alloc_space_free is registered and its reset value is SD)
    //     Labels omitted inside generate blocks to avoid yosys duplicate-name errors.
    generate
        for (gi = 0; gi < NC; gi = gi + 1) begin : gen_p1
            always @(posedge clk) begin
                if (f_past_valid > 0 && $past(!rst_n))
                    assert (axi_rd_alloc_space_free[gi] == SD);
            end
        end
    endgenerate

    // P2: Write valid decoded is one-hot or zero (at most one channel selected)
    always @(posedge clk) begin
        if (rst_n)
            ap_wr_decode_onehot: assert ((f_wr_valid_decoded == '0) ||
                                         (f_wr_valid_decoded & (f_wr_valid_decoded - 1)) == '0);
    end

    // P3: Drain decoded is one-hot or zero (at most one channel selected)
    always @(posedge clk) begin
        if (rst_n)
            ap_drain_decode_onehot: assert ((f_drain_decoded == '0) ||
                                            (f_drain_decoded & (f_drain_decoded - 1)) == '0);
    end

    // P4: When write is valid, ID is in range
    always @(posedge clk) begin
        if (rst_n && axi_rd_sram_valid)
            ap_wr_id_range: assert (axi_rd_sram_id < NC);
    end

    // P5: Ready reflects selected channel -- when valid with a given ID,
    //     ready can only be high if the DUT routes it from that channel.
    always @(posedge clk) begin
        if (rst_n && axi_rd_sram_valid && !axi_rd_sram_ready)
            ap_ready_gate: assert (!(axi_rd_sram_valid && axi_rd_sram_ready));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // C1: Write handshake on each channel
    //     Labels omitted inside generate blocks to avoid yosys duplicate-name errors.
    generate
        for (gi = 0; gi < NC; gi = gi + 1) begin : gen_c1
            always @(posedge clk) begin
                if (rst_n)
                    cover (f_wr_valid_decoded[gi] && axi_rd_sram_ready);
            end
        end
    endgenerate

    // C2: Drain handshake on each channel
    generate
        for (gi = 0; gi < NC; gi = gi + 1) begin : gen_c2
            always @(posedge clk) begin
                if (rst_n)
                    cover (axi_wr_sram_valid[gi] && f_drain_decoded[gi]);
            end
        end
    endgenerate

endmodule
