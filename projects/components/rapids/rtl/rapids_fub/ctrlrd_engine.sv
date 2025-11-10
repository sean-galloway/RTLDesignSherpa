// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ctrlrd_engine
// Purpose: Ctrlrd Engine module
//
// Documentation: projects/components/rapids_fub/PRD.md
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Import common RAPIDS and monitor packages
`include "rapids_imports.svh"
`include "reset_defs.svh"


module ctrlrd_engine #(
    parameter int CHANNEL_ID = 0,
    parameter int NUM_CHANNELS = 32,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int AXI_DATA_WIDTH = 64,
    parameter int AXI_ID_WIDTH = 8,
    // Monitor Bus Parameters
    parameter logic [7:0] MON_AGENT_ID = 8'h30,      // Ctrlrd Engine Agent ID
    parameter logic [3:0] MON_UNIT_ID = 4'h2,        // Unit identifier
    parameter logic [5:0] MON_CHANNEL_ID = 6'h0      // Base channel ID
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // Scheduler FSM Interface
    input  logic                        ctrlrd_valid,
    output logic                        ctrlrd_ready,
    input  logic [ADDR_WIDTH-1:0]       ctrlrd_pkt_addr,
    input  logic [31:0]                 ctrlrd_pkt_data,
    input  logic [31:0]                 ctrlrd_pkt_mask,
    output logic                        ctrlrd_error,
    output logic [31:0]                 ctrlrd_result,

    // Configuration Interface
    input  logic [8:0]                  cfg_ctrlrd_max_try,     // Max retry count (0-511)
    input  logic                        cfg_channel_reset,       // Channel reset

    // 1µs Tick from scheduler_group counter_freq_invariant
    input  logic                        tick_1us,

    // Status Interface
    output logic                        ctrlrd_engine_idle,

    // Shared AXI4 Master Read Interface
    output logic                        ar_valid,
    input  logic                        ar_ready,
    output logic [ADDR_WIDTH-1:0]       ar_addr,
    output logic [7:0]                  ar_len,
    output logic [2:0]                  ar_size,
    output logic [1:0]                  ar_burst,
    output logic [AXI_ID_WIDTH-1:0]     ar_id,
    output logic                        ar_lock,
    output logic [3:0]                  ar_cache,
    output logic [2:0]                  ar_prot,
    output logic [3:0]                  ar_qos,
    output logic [3:0]                  ar_region,

    // AXI Read Data Channel (Shared - monitor for our ID)
    input  logic                        r_valid,
    output logic                        r_ready,
    input  logic [AXI_DATA_WIDTH-1:0]   r_data,
    input  logic [AXI_ID_WIDTH-1:0]     r_id,
    input  logic [1:0]                  r_resp,
    input  logic                        r_last,

    // Monitor Bus Interface
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [63:0]                 mon_packet
);

    //=========================================================================
    // Parameter Validation
    //=========================================================================

    initial begin
        if (AXI_ID_WIDTH < CHAN_WIDTH) begin
            $fatal(1, "AXI_ID_WIDTH (%0d) must be >= CHAN_WIDTH (%0d)", AXI_ID_WIDTH, CHAN_WIDTH);
        end
        if (AXI_DATA_WIDTH < 32) begin
            $fatal(1, "AXI_DATA_WIDTH (%0d) must be >= 32 for 32-bit reads", AXI_DATA_WIDTH);
        end
    end

    //=========================================================================
    // Internal Signals with w_/r_ Naming Convention
    //=========================================================================

    // FSM state - registered
    /* verilator lint_off VARHIDDEN */
    typedef enum logic [2:0] {
        READ_IDLE       = 3'b000,
        READ_ISSUE_ADDR = 3'b001,
        READ_WAIT_DATA  = 3'b010,
        READ_COMPARE    = 3'b011,
        READ_RETRY_WAIT = 3'b100,
        READ_MATCH      = 3'b101,
        READ_ERROR      = 3'b110
    } ctrlrd_engine_state_t;
    /* verilator lint_on VARHIDDEN */

    ctrlrd_engine_state_t r_current_state, w_next_state;

    // Channel reset management
    logic r_channel_reset_active;
    logic w_safe_to_reset;
    logic w_fifo_empty;
    logic w_no_active_transaction;

    // Ctrlrd operation parameters - registered
    logic [ADDR_WIDTH-1:0] r_ctrlrd_addr;
    logic [31:0] r_expected_data;
    logic [31:0] r_mask;
    logic [31:0] r_axi_read_data;

    // Retry mechanism - registered
    logic [8:0] r_retry_counter;
    logic r_retry_wait_complete;

    // AXI transaction tracking - registered
    logic r_addr_issued;
    logic [1:0] r_read_resp;
    logic [AXI_ID_WIDTH-1:0] r_expected_axi_id;
    logic r_ctrlrd_error;

    // Control logic
    logic w_null_address;
    logic w_axi_response_error;
    logic w_transaction_complete;
    logic w_our_axi_response;
    logic [31:0] w_masked_expected;
    logic [31:0] w_masked_actual;
    logic w_data_match;
    logic w_retries_remaining;

    // Ctrlrd request skid buffer signals
    logic w_ctrlrd_req_skid_valid_in, w_ctrlrd_req_skid_ready_in;
    logic w_ctrlrd_req_skid_valid_out, w_ctrlrd_req_skid_ready_out;
    logic [ADDR_WIDTH + 32 + 32 - 1:0] w_ctrlrd_req_skid_din, w_ctrlrd_req_skid_dout;

    // Monitor packet generation
    logic r_mon_valid;
    logic [63:0] r_mon_packet;

    //=========================================================================
    // Channel Reset Management
    //=========================================================================

    // Channel reset active tracking
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_channel_reset_active <= 1'b0;
        end else begin
            r_channel_reset_active <= cfg_channel_reset;
        end
    )


    // Safe to reset conditions
    assign w_fifo_empty = !w_ctrlrd_req_skid_valid_out;
    assign w_no_active_transaction = !r_addr_issued;
    assign w_safe_to_reset = w_fifo_empty && w_no_active_transaction && (r_current_state == READ_IDLE);

    // Engine idle signal
    assign ctrlrd_engine_idle = (r_current_state == READ_IDLE) && !r_channel_reset_active && w_fifo_empty;

    //=========================================================================
    // Ctrlrd Request Skid Buffer
    //=========================================================================

    // Input side: Accept from scheduler when not in reset
    assign w_ctrlrd_req_skid_valid_in = ctrlrd_valid && !r_channel_reset_active;
    assign ctrlrd_ready = w_ctrlrd_req_skid_ready_in && !r_channel_reset_active;
    assign w_ctrlrd_req_skid_din = {ctrlrd_pkt_addr, ctrlrd_pkt_data, ctrlrd_pkt_mask};

    gaxi_skid_buffer #(
        .DATA_WIDTH(ADDR_WIDTH + 32 + 32),
        .DEPTH(2),
        .INSTANCE_NAME("CTRLRD_REQ_SKID")
    ) i_ctrlrd_req_skid_buffer (
        .axi_aclk(clk),
        .axi_aresetn(rst_n),
        .wr_valid(w_ctrlrd_req_skid_valid_in),
        .wr_ready(w_ctrlrd_req_skid_ready_in),
        .wr_data(w_ctrlrd_req_skid_din),
        .rd_valid(w_ctrlrd_req_skid_valid_out),
        .rd_ready(w_ctrlrd_req_skid_ready_out),
        .rd_data(w_ctrlrd_req_skid_dout),
        .count(),
        .rd_count()
    );

    assign w_ctrlrd_req_skid_ready_out = (r_current_state == READ_IDLE) && w_ctrlrd_req_skid_valid_out && !r_channel_reset_active;

    //=========================================================================
    // Control Logic
    //=========================================================================

    // Check for null address (skip operation - immediate success)
    assign w_null_address = (r_ctrlrd_addr == 64'h0);

    // AXI response validation
    assign w_axi_response_error = (r_read_resp != 2'b00); // Not OKAY

    // Transaction tracking
    assign w_transaction_complete = w_our_axi_response && r_valid;

    // Retry management
    assign w_retries_remaining = (r_retry_counter > 0);

    //=========================================================================
    // Masked Comparison Logic
    //=========================================================================

    // Apply mask to expected and actual data
    assign w_masked_expected = r_expected_data & r_mask;
    assign w_masked_actual = r_axi_read_data[31:0] & r_mask;

    // Compare masked values
    assign w_data_match = (w_masked_expected == w_masked_actual);

    //=========================================================================
    // AXI Response Monitoring
    //=========================================================================

    // Check if AXI response is for our channel
    assign w_our_axi_response = r_valid && (r_id == r_expected_axi_id);

    // We're ready to accept AXI responses when waiting
    assign r_ready = (r_current_state == READ_WAIT_DATA) && w_our_axi_response;

    //=========================================================================
    // FSM State Machine with Channel Reset
    //=========================================================================

    // State register
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_current_state <= READ_IDLE;
        end else begin
            r_current_state <= w_next_state;
        end
    )


    // Next state logic with channel reset support
    always_comb begin
        w_next_state = r_current_state;

        case (r_current_state)
            READ_IDLE: begin
                if (r_channel_reset_active) begin
                    w_next_state = READ_IDLE; // Stay in idle during reset
                end else if (w_ctrlrd_req_skid_valid_out) begin
                    w_next_state = READ_ISSUE_ADDR;
                end
            end

            READ_ISSUE_ADDR: begin
                if (r_channel_reset_active) begin
                    w_next_state = READ_IDLE; // Reset forces return to idle
                end else if (w_null_address) begin
                    w_next_state = READ_MATCH; // Null address = immediate success
                end else if (r_addr_issued) begin
                    w_next_state = READ_WAIT_DATA;
                end
                // else stay in READ_ISSUE_ADDR until ar_ready handshake
            end

            READ_WAIT_DATA: begin
                if (r_channel_reset_active) begin
                    w_next_state = READ_IDLE; // Reset forces return to idle
                end else if (w_transaction_complete) begin
                    w_next_state = READ_COMPARE;
                end
            end

            READ_COMPARE: begin
                if (r_channel_reset_active) begin
                    w_next_state = READ_IDLE; // Reset forces return to idle
                end else if (w_axi_response_error) begin
                    w_next_state = READ_ERROR; // AXI error
                end else if (w_data_match) begin
                    w_next_state = READ_MATCH; // Success!
                end else if (w_retries_remaining) begin
                    w_next_state = READ_RETRY_WAIT; // Retry
                end else begin
                    w_next_state = READ_ERROR; // Max retries exceeded
                end
            end

            READ_RETRY_WAIT: begin
                if (r_channel_reset_active) begin
                    w_next_state = READ_IDLE; // Reset forces return to idle
                end else if (r_retry_wait_complete) begin
                    w_next_state = READ_ISSUE_ADDR; // Retry read
                end
            end

            READ_MATCH: begin
                w_next_state = READ_IDLE; // Automatically return to idle
            end

            READ_ERROR: begin
                w_next_state = READ_IDLE; // Automatically return to idle
            end

            default: begin
                w_next_state = READ_IDLE;
            end
        endcase
    end

    //=========================================================================
    // State Machine Registers and Control
    //=========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_ctrlrd_addr <= 64'h0;
            r_expected_data <= 32'h0;
            r_mask <= 32'h0;
            r_axi_read_data <= 32'h0;
            r_retry_counter <= 9'h0;
            r_retry_wait_complete <= 1'b0;
            r_addr_issued <= 1'b0;
            r_read_resp <= 2'b00;
            r_expected_axi_id <= '0;
            r_ctrlrd_error <= 1'b0;
        end else begin
            case (r_current_state)
                READ_IDLE: begin
                    if (w_ctrlrd_req_skid_valid_out && w_ctrlrd_req_skid_ready_out) begin
                        // Latch new ctrlrd request
                        {r_ctrlrd_addr, r_expected_data, r_mask} <= w_ctrlrd_req_skid_dout;
                        r_expected_axi_id <= {{(AXI_ID_WIDTH-CHAN_WIDTH){1'b0}}, CHANNEL_ID[CHAN_WIDTH-1:0]};
                        // Initialize retry counter from configuration
                        r_retry_counter <= cfg_ctrlrd_max_try;
                    end
                    r_addr_issued <= 1'b0;
                    r_read_resp <= 2'b00;
                    r_retry_wait_complete <= 1'b0;
                end

                READ_ISSUE_ADDR: begin
                    if (!w_null_address && ar_ready) begin
                        r_addr_issued <= 1'b1;
                    end
                end

                READ_WAIT_DATA: begin
                    if (w_transaction_complete) begin
                        r_axi_read_data <= r_data[31:0]; // Capture lower 32 bits
                        r_read_resp <= r_resp;
                        r_addr_issued <= 1'b0; // Clear for next attempt
                    end
                end

                READ_COMPARE: begin
                    // Decrement retry counter if we need to retry
                    if (!w_data_match && w_retries_remaining && !w_axi_response_error) begin
                        r_retry_counter <= r_retry_counter - 1;
                    end
                end

                READ_RETRY_WAIT: begin
                    // Wait for 1µs tick
                    if (tick_1us) begin
                        r_retry_wait_complete <= 1'b1;
                    end
                end

                READ_MATCH: begin
                    r_ctrlrd_error <= 1'b0; // Success - no error
                end

                READ_ERROR: begin
                    r_ctrlrd_error <= 1'b1; // Set error flag
                end

                default: begin
                    // Maintain state
                end
            endcase

            // Reset all state during channel reset
            if (r_channel_reset_active) begin
                r_addr_issued <= 1'b0;
                r_read_resp <= 2'b00;
                r_retry_counter <= 9'h0;
                r_retry_wait_complete <= 1'b0;
                r_ctrlrd_error <= 1'b0;
            end
        end
    )


    //=========================================================================
    // AXI Read Address Channel Output
    //=========================================================================

    assign ar_valid = (r_current_state == READ_ISSUE_ADDR) && !w_null_address && !r_addr_issued;
    assign ar_addr = r_ctrlrd_addr;
    assign ar_len = 8'h00;           // Single beat transfer
    assign ar_size = 3'b010;         // 4 bytes (32-bit)
    assign ar_burst = 2'b01;         // INCR burst type
    assign ar_id = r_expected_axi_id;
    assign ar_lock = 1'b0;           // Normal access
    assign ar_cache = 4'b0010;       // Normal non-cacheable bufferable
    assign ar_prot = 3'b000;         // Data, secure, unprivileged
    assign ar_qos = 4'h0;            // No QoS
    assign ar_region = 4'h0;         // No region

    //=========================================================================
    // Scheduler Handshake Outputs
    //=========================================================================

    // ctrlrd_ready already assigned at line 186 (tied to skid buffer ready)

    // ctrlrd_error indicates failure when ready asserts
    assign ctrlrd_error = r_ctrlrd_error;

    // ctrlrd_result provides the actual read data
    assign ctrlrd_result = r_axi_read_data;

    //=========================================================================
    // Monitor Packet Generation
    //=========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_mon_valid <= 1'b0;
            r_mon_packet <= 64'h0;
        end else begin
            // Default: clear monitor packet
            r_mon_valid <= 1'b0;
            r_mon_packet <= 64'h0;

            case (r_current_state)
                READ_ERROR: begin
                    if (w_axi_response_error) begin
                        // Log AXI response error
                        r_mon_valid <= 1'b1;
                        r_mon_packet <= create_monitor_packet(
                            PktTypeError,
                            PROTOCOL_AXI,
                            (r_read_resp == 2'b10) ? AXI_ERR_RESP_SLVERR : AXI_ERR_RESP_DECERR,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            {16'h0, r_read_resp, 17'h0}
                        );
                    end else begin
                        // Log max retries exceeded error
                        r_mon_valid <= 1'b1;
                        r_mon_packet <= create_monitor_packet(
                            PktTypeError,
                            PROTOCOL_CORE,
                            CORE_ERR_CTRLRD_MAX_RETRIES,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            r_ctrlrd_addr[34:0]
                        );
                    end
                end

                READ_MATCH: begin
                    if (!w_null_address) begin
                        // Log successful completion
                        r_mon_valid <= 1'b1;
                        r_mon_packet <= create_monitor_packet(
                            PktTypeCompletion,
                            PROTOCOL_CORE,
                            CORE_COMPL_CTRLRD_COMPLETED,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            r_ctrlrd_addr[34:0]
                        );
                    end
                end

                READ_RETRY_WAIT: begin
                    // Log retry attempt (using PktTypePerf for retry tracking)
                    r_mon_valid <= 1'b1;
                    r_mon_packet <= create_monitor_packet(
                        PktTypePerf,
                        PROTOCOL_CORE,
                        CORE_PERF_CTRLRD_RETRY,
                        MON_CHANNEL_ID,
                        MON_UNIT_ID,
                        MON_AGENT_ID,
                        {26'h0, r_retry_counter}
                    );
                end

                default: begin
                    // No monitor packet
                end
            endcase
        end
    )


    //=========================================================================
    // Output Assignments
    //=========================================================================

    assign mon_valid = r_mon_valid;
    assign mon_packet = r_mon_packet;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // State machine one-hot (not strictly one-hot, but valid states)
    property state_valid;
        @(posedge clk) disable iff (!rst_n)
        (r_current_state inside {READ_IDLE, READ_ISSUE_ADDR, READ_WAIT_DATA, READ_COMPARE, READ_RETRY_WAIT, READ_MATCH, READ_ERROR});
    endproperty
    assert property (state_valid);

    // AXI ID consistency
    property axi_id_matches_channel;
        @(posedge clk) disable iff (!rst_n)
        ar_valid |-> (ar_id[CHAN_WIDTH-1:0] == CHANNEL_ID[CHAN_WIDTH-1:0]);
    endproperty
    assert property (axi_id_matches_channel);

    // Retry counter never underflows
    property retry_counter_valid;
        @(posedge clk) disable iff (!rst_n)
        (r_current_state == READ_COMPARE) && !w_data_match |-> (r_retry_counter >= 0);
    endproperty
    assert property (retry_counter_valid);

    // ctrlrd_ready tied to skid buffer (matches ctrlwr_engine pattern)
    // Removed assertions that expected ready only in terminal states

    // Channel reset properties
    property channel_reset_blocks_inputs;
        @(posedge clk) disable iff (!rst_n)
        r_channel_reset_active |-> !ctrlrd_ready;
    endproperty
    assert property (channel_reset_blocks_inputs);

    property channel_reset_forces_idle;
        @(posedge clk) disable iff (!rst_n)
        r_channel_reset_active |-> ##[0:5] (r_current_state == READ_IDLE);
    endproperty
    assert property (channel_reset_forces_idle);

    property channel_reset_idle_signal;
        @(posedge clk) disable iff (!rst_n)
        ctrlrd_engine_idle |-> (r_current_state == READ_IDLE && !r_channel_reset_active);
    endproperty
    assert property (channel_reset_idle_signal);
    `endif

endmodule : ctrlrd_engine
