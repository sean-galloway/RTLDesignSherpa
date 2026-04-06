// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for descriptor_engine_beats (RAPIDS fub_beats variant)
// Run with: sby descriptor_engine_beats.sby
//
// All assertions use PORT-LEVEL signals only (no hierarchical references
// into the DUT), ensuring compatibility with sv2v-flattened RTL.
//
// Properties verified:
//   P1: Reset clears outputs (idle asserted, ar_valid/descriptor_valid/error deasserted)
//   P2: ar_burst always INCR (2'b01) when ar_valid
//   P3: ar_size matches 512-bit AXI data width (3'b110 = 64 bytes)
//   P4: ar_len always 0 (single-beat descriptor fetch)
//   P5: AXI handshake stability (ar_valid held until ar_ready)
//   P6: Descriptor error blocks descriptor_valid
//   P7: Idle means no outstanding AXI (ar_valid deasserted)

module formal_descriptor_engine_beats (
    input  logic        clk,
    input  logic        rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam int CHANNEL_ID          = 0;
    localparam int NUM_CHANNELS        = 2;
    localparam int CHAN_WIDTH           = 1;   // $clog2(2)
    localparam int ADDR_WIDTH          = 32;
    localparam int AXI_ID_WIDTH        = 4;
    localparam int FIFO_DEPTH          = 4;
    localparam int DESC_ADDR_FIFO_DEPTH = 2;
    localparam int TIMEOUT_CYCLES      = 20;

    // =========================================================================
    // Free inputs (driven by formal engine)
    // =========================================================================
    (* anyseq *) reg                        apb_valid;
    (* anyseq *) reg  [ADDR_WIDTH-1:0]      apb_addr;
    (* anyseq *) reg                        channel_idle;
    (* anyseq *) reg                        descriptor_ready;

    // AXI AR channel
    (* anyseq *) reg                        ar_ready;

    // AXI R channel
    (* anyseq *) reg                        r_valid;
    (* anyseq *) reg  [255:0]               r_data;
    (* anyseq *) reg  [1:0]                 r_resp;
    (* anyseq *) reg                        r_last;
    (* anyseq *) reg  [AXI_ID_WIDTH-1:0]    r_id;

    // Configuration
    (* anyseq *) reg                        cfg_prefetch_enable;
    (* anyseq *) reg  [3:0]                 cfg_fifo_threshold;
    (* anyseq *) reg  [ADDR_WIDTH-1:0]      cfg_addr0_base;
    (* anyseq *) reg  [ADDR_WIDTH-1:0]      cfg_addr0_limit;
    (* anyseq *) reg  [ADDR_WIDTH-1:0]      cfg_addr1_base;
    (* anyseq *) reg  [ADDR_WIDTH-1:0]      cfg_addr1_limit;
    (* anyseq *) reg                        cfg_channel_reset;

    // Monitor bus
    (* anyseq *) reg                        mon_ready;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire                        apb_ready_o;
    wire                        descriptor_valid_o;
    wire [255:0]                descriptor_packet_o;
    wire                        descriptor_error_o;
    wire                        descriptor_eos_o;
    wire                        descriptor_eol_o;
    wire                        descriptor_eod_o;
    wire [1:0]                  descriptor_type_o;

    wire                        ar_valid_o;
    wire [ADDR_WIDTH-1:0]       ar_addr_o;
    wire [7:0]                  ar_len_o;
    wire [2:0]                  ar_size_o;
    wire [1:0]                  ar_burst_o;
    wire [AXI_ID_WIDTH-1:0]     ar_id_o;
    wire                        ar_lock_o;
    wire [3:0]                  ar_cache_o;
    wire [2:0]                  ar_prot_o;
    wire [3:0]                  ar_qos_o;
    wire [3:0]                  ar_region_o;

    wire                        r_ready_o;

    wire                        descriptor_engine_idle_o;
    wire                        mon_valid_o;
    wire [63:0]                 mon_packet_o;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    descriptor_engine_beats #(
        .CHANNEL_ID          (CHANNEL_ID),
        .NUM_CHANNELS        (NUM_CHANNELS),
        .CHAN_WIDTH           (CHAN_WIDTH),
        .ADDR_WIDTH          (ADDR_WIDTH),
        .AXI_ID_WIDTH        (AXI_ID_WIDTH),
        .FIFO_DEPTH          (FIFO_DEPTH),
        .DESC_ADDR_FIFO_DEPTH(DESC_ADDR_FIFO_DEPTH),
        .TIMEOUT_CYCLES      (TIMEOUT_CYCLES)
    ) dut (
        .clk                 (clk),
        .rst_n               (rst_n),

        // APB interface
        .apb_valid           (apb_valid),
        .apb_ready           (apb_ready_o),
        .apb_addr            (apb_addr),

        // Scheduler interface
        .channel_idle        (channel_idle),
        .descriptor_valid    (descriptor_valid_o),
        .descriptor_ready    (descriptor_ready),
        .descriptor_packet   (descriptor_packet_o),
        .descriptor_error    (descriptor_error_o),
        .descriptor_eos      (descriptor_eos_o),
        .descriptor_eol      (descriptor_eol_o),
        .descriptor_eod      (descriptor_eod_o),
        .descriptor_type     (descriptor_type_o),

        // AXI AR channel
        .ar_valid            (ar_valid_o),
        .ar_ready            (ar_ready),
        .ar_addr             (ar_addr_o),
        .ar_len              (ar_len_o),
        .ar_size             (ar_size_o),
        .ar_burst            (ar_burst_o),
        .ar_id               (ar_id_o),
        .ar_lock             (ar_lock_o),
        .ar_cache            (ar_cache_o),
        .ar_prot             (ar_prot_o),
        .ar_qos              (ar_qos_o),
        .ar_region           (ar_region_o),

        // AXI R channel
        .r_valid             (r_valid),
        .r_ready             (r_ready_o),
        .r_data              (r_data),
        .r_resp              (r_resp),
        .r_last              (r_last),
        .r_id                (r_id),

        // Configuration
        .cfg_prefetch_enable (cfg_prefetch_enable),
        .cfg_fifo_threshold  (cfg_fifo_threshold),
        .cfg_addr0_base      (cfg_addr0_base),
        .cfg_addr0_limit     (cfg_addr0_limit),
        .cfg_addr1_base      (cfg_addr1_base),
        .cfg_addr1_limit     (cfg_addr1_limit),
        .cfg_channel_reset   (cfg_channel_reset),

        // Status
        .descriptor_engine_idle (descriptor_engine_idle_o),

        // Monitor bus
        .mon_valid           (mon_valid_o),
        .mon_ready           (mon_ready),
        .mon_packet          (mon_packet_o)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Reset sequence: assert reset for first 2 cycles
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // =========================================================================
    // Environment constraints
    // =========================================================================

    // Address range constraints: base <= limit
    always @(posedge clk) begin
        if (rst_n) begin
            assume (cfg_addr0_base <= cfg_addr0_limit);
            assume (cfg_addr1_base <= cfg_addr1_limit);
        end
    end

    // Channel reset disabled for this proof.
    // Channel reset intentionally violates AXI handshake stability (by design),
    // so we constrain it to 0 to verify normal-operation properties cleanly.
    // A separate proof could verify channel reset behavior.
    always @(*) assume (cfg_channel_reset == 1'b0);

    // =========================================================================
    // P1: Reset clears outputs - idle asserted, control signals deasserted
    // =========================================================================
    // Uses only port-level signals (no hierarchical state reference)

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_idle: assert (descriptor_engine_idle_o == 1'b1);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_ar_valid: assert (ar_valid_o == 1'b0);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_desc_valid: assert (descriptor_valid_o == 1'b0);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_desc_error: assert (descriptor_error_o == 1'b0);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_mon_valid: assert (mon_valid_o == 1'b0);
    end

    // =========================================================================
    // P2: ar_burst always INCR (2'b01) when ar_valid
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_ar_burst_incr: assert (!ar_valid_o || ar_burst_o == 2'b01);
    end

    // =========================================================================
    // P3: ar_size matches 512-bit AXI data width (3'b110 = 64 bytes)
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_ar_size: assert (!ar_valid_o || ar_size_o == 3'b110);
    end

    // =========================================================================
    // P4: ar_len always 0 (single-beat descriptor fetch)
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_ar_len_zero: assert (!ar_valid_o || ar_len_o == 8'h00);
    end

    // =========================================================================
    // P5: AXI handshake stability - ar_valid held until ar_ready
    // =========================================================================
    // AXI spec: once valid is asserted, it must remain asserted until ready.
    // cfg_channel_reset is constrained to 0 (see environment constraints),
    // so normal-operation stability can be checked directly.
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            ap_ar_valid_stable: assert (
                !($past(ar_valid_o) && !$past(ar_ready)) || ar_valid_o
            );
    end

    // =========================================================================
    // P6: Descriptor error blocks descriptor_valid
    // =========================================================================
    // When error is asserted, descriptor_valid must be deasserted
    always @(posedge clk) begin
        if (rst_n)
            ap_error_blocks_valid: assert (
                !descriptor_error_o || !descriptor_valid_o
            );
    end

    // =========================================================================
    // P7: Idle means no outstanding AXI requests
    // =========================================================================
    // When idle is asserted, ar_valid must be deasserted
    always @(posedge clk) begin
        if (rst_n)
            ap_idle_no_axi: assert (
                !descriptor_engine_idle_o || !ar_valid_o
            );
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // AR handshake
    always @(posedge clk) begin
        if (rst_n)
            cp_ar_handshake: cover (ar_valid_o && ar_ready);
    end

    // R handshake
    always @(posedge clk) begin
        if (rst_n)
            cp_r_handshake: cover (r_valid && r_ready_o);
    end

    // Descriptor output valid
    always @(posedge clk) begin
        if (rst_n)
            cp_descriptor_valid: cover (descriptor_valid_o);
    end

    // APB handshake
    always @(posedge clk) begin
        if (rst_n)
            cp_apb_handshake: cover (apb_valid && apb_ready_o);
    end

    // Descriptor error
    always @(posedge clk) begin
        if (rst_n)
            cp_descriptor_error: cover (descriptor_error_o);
    end

    // Idle-to-active transition (proves engine actually does something)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n)
            cp_idle_to_active: cover ($past(descriptor_engine_idle_o) && !descriptor_engine_idle_o);
    end

endmodule
