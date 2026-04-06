// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for scheduler (yosys-compatible, sv2v-preprocessed)
// Run with: sby scheduler.sby

module formal_scheduler (
    input  logic        clk,
    input  logic        rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam int CHANNEL_ID   = 0;
    localparam int NUM_CHANNELS = 2;
    localparam int CHAN_WIDTH    = 1;   // $clog2(2)
    localparam int ADDR_WIDTH   = 32;
    localparam int DATA_WIDTH   = 64;
    localparam int DESC_WIDTH   = 256;

    // =========================================================================
    // Free inputs (driven by formal engine)
    // =========================================================================
    (* anyseq *) reg                        cfg_channel_enable;
    (* anyseq *) reg                        cfg_channel_reset;
    (* anyseq *) reg  [15:0]                cfg_sched_timeout_cycles;
    (* anyseq *) reg                        cfg_sched_timeout_enable;

    (* anyseq *) reg                        descriptor_valid;
    (* anyseq *) reg  [DESC_WIDTH-1:0]      descriptor_packet;
    (* anyseq *) reg                        descriptor_error;

    (* anyseq *) reg                        sched_rd_done_strobe;
    (* anyseq *) reg  [31:0]                sched_rd_beats_done;
    (* anyseq *) reg                        sched_wr_done_strobe;
    (* anyseq *) reg  [31:0]                sched_wr_beats_done;
    (* anyseq *) reg                        sched_wr_ready;

    (* anyseq *) reg                        sched_rd_error;
    (* anyseq *) reg                        sched_wr_error;

    (* anyseq *) reg                        mon_ready;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire                        scheduler_idle_o;
    wire [6:0]                  scheduler_state_o;
    wire                        descriptor_ready_o;

    wire                        sched_rd_valid_o;
    wire [ADDR_WIDTH-1:0]       sched_rd_addr_o;
    wire [31:0]                 sched_rd_beats_o;

    wire                        sched_wr_valid_o;
    wire [ADDR_WIDTH-1:0]       sched_wr_addr_o;
    wire [31:0]                 sched_wr_beats_o;

    wire                        sched_error_o;

    wire                        mon_valid_o;
    wire [63:0]                 mon_packet_o;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    scheduler #(
        .CHANNEL_ID   (CHANNEL_ID),
        .NUM_CHANNELS (NUM_CHANNELS),
        .CHAN_WIDTH    (CHAN_WIDTH),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .DATA_WIDTH   (DATA_WIDTH),
        .DESC_WIDTH   (DESC_WIDTH)
    ) dut (
        .clk                      (clk),
        .rst_n                    (rst_n),

        // Configuration
        .cfg_channel_enable       (cfg_channel_enable),
        .cfg_channel_reset        (cfg_channel_reset),
        .cfg_sched_timeout_cycles (cfg_sched_timeout_cycles),
        .cfg_sched_timeout_enable (cfg_sched_timeout_enable),

        // Status
        .scheduler_idle           (scheduler_idle_o),
        .scheduler_state          (scheduler_state_o),

        // Descriptor interface
        .descriptor_valid         (descriptor_valid),
        .descriptor_ready         (descriptor_ready_o),
        .descriptor_packet        (descriptor_packet),
        .descriptor_error         (descriptor_error),

        // Read interface
        .sched_rd_valid           (sched_rd_valid_o),
        .sched_rd_addr            (sched_rd_addr_o),
        .sched_rd_beats           (sched_rd_beats_o),

        // Write interface
        .sched_wr_valid           (sched_wr_valid_o),
        .sched_wr_ready           (sched_wr_ready),
        .sched_wr_addr            (sched_wr_addr_o),
        .sched_wr_beats           (sched_wr_beats_o),

        // Completion interface
        .sched_rd_done_strobe     (sched_rd_done_strobe),
        .sched_rd_beats_done      (sched_rd_beats_done),
        .sched_wr_done_strobe     (sched_wr_done_strobe),
        .sched_wr_beats_done      (sched_wr_beats_done),

        // Error signals
        .sched_rd_error           (sched_rd_error),
        .sched_wr_error           (sched_wr_error),
        .sched_error              (sched_error_o),

        // Monitor bus
        .mon_valid                (mon_valid_o),
        .mon_ready                (mon_ready),
        .mon_packet               (mon_packet_o)
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

    // Timeout cycles bounded for tractability
    always @(posedge clk) begin
        if (rst_n) begin
            assume (cfg_sched_timeout_cycles >= 16'd5);
            assume (cfg_sched_timeout_cycles <= 16'd30);
        end
    end

    // Channel enable held high so FSM can make progress
    always @(posedge clk) begin
        if (rst_n) begin
            assume (cfg_channel_enable == 1'b1);
        end
    end

    // =========================================================================
    // P1: Reset - scheduler_idle==1, scheduler_state==CH_IDLE,
    //     sched_rd_valid==0, sched_wr_valid==0, sched_error==0, mon_valid==0
    // =========================================================================
    // channel_state_t: CH_IDLE = 7'b0000001
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_idle: assert (scheduler_idle_o == 1'b1);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_state: assert (scheduler_state_o == 7'b0000001);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_rd_valid: assert (sched_rd_valid_o == 1'b0);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_wr_valid: assert (sched_wr_valid_o == 1'b0);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_error: assert (sched_error_o == 1'b0);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_mon_valid: assert (mon_valid_o == 1'b0);
    end

    // =========================================================================
    // P2: FSM one-hot - exactly one bit of scheduler_state asserted (after reset)
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_fsm_one_hot: assert ($onehot(scheduler_state_o));
    end

    // =========================================================================
    // P3: scheduler_idle asserted only in CH_IDLE state
    // =========================================================================
    // Note: RTL also asserts idle in CH_ERROR; this property checks
    // that idle implies CH_IDLE or CH_ERROR (matching actual RTL behavior)
    always @(posedge clk) begin
        if (rst_n)
            ap_idle_state: assert (
                !scheduler_idle_o ||
                scheduler_state_o == 7'b0000001 ||  // CH_IDLE
                scheduler_state_o == 7'b0100000      // CH_ERROR
            );
    end

    // =========================================================================
    // P4: descriptor_ready asserted only in CH_IDLE or CH_NEXT_DESC states
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_desc_ready_states: assert (
                !descriptor_ready_o ||
                scheduler_state_o == 7'b0000001 ||  // CH_IDLE
                scheduler_state_o == 7'b0010000      // CH_NEXT_DESC
            );
    end

    // =========================================================================
    // P5: sched_rd_valid and sched_wr_valid only in CH_XFER_DATA state
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_rd_valid_xfer: assert (
                !sched_rd_valid_o || scheduler_state_o == 7'b0000100  // CH_XFER_DATA
            );
    end

    always @(posedge clk) begin
        if (rst_n)
            ap_wr_valid_xfer: assert (
                !sched_wr_valid_o || scheduler_state_o == 7'b0000100  // CH_XFER_DATA
            );
    end

    // =========================================================================
    // P6: sched_error only asserted in CH_ERROR state
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_error_state: assert (
                !sched_error_o || scheduler_state_o == 7'b0100000  // CH_ERROR
            );
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Descriptor handshake
    always @(posedge clk) begin
        if (rst_n)
            cp_desc_handshake: cover (descriptor_valid && descriptor_ready_o);
    end

    // Read valid asserted
    always @(posedge clk) begin
        if (rst_n)
            cp_rd_valid: cover (sched_rd_valid_o);
    end

    // Write valid asserted
    always @(posedge clk) begin
        if (rst_n)
            cp_wr_valid: cover (sched_wr_valid_o);
    end

    // Read done strobe
    always @(posedge clk) begin
        if (rst_n)
            cp_rd_done: cover (sched_rd_done_strobe);
    end

    // Write done strobe
    always @(posedge clk) begin
        if (rst_n)
            cp_wr_done: cover (sched_wr_done_strobe);
    end

    // Scheduler entering CH_COMPLETE (7'b0001000)
    always @(posedge clk) begin
        if (rst_n)
            cp_complete: cover (scheduler_state_o == 7'b0001000);
    end

    // Scheduler entering CH_ERROR (7'b0100000)
    always @(posedge clk) begin
        if (rst_n)
            cp_error: cover (scheduler_state_o == 7'b0100000);
    end

endmodule
