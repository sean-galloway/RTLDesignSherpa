// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ctrlwr_engine
// Purpose: Ctrlwr Engine module
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


module ctrlwr_engine #(
    parameter int CHANNEL_ID = 0,
    parameter int NUM_CHANNELS = 32,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int AXI_ID_WIDTH = 8,
    // Monitor Bus Parameters
    parameter logic [7:0] MON_AGENT_ID = 8'h20,      // Ctrlwr Engine Agent ID
    parameter logic [3:0] MON_UNIT_ID = 4'h1,        // Unit identifier
    parameter logic [5:0] MON_CHANNEL_ID = 6'h0      // Base channel ID
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // Scheduler FSM Interface
    input  logic                        ctrlwr_valid,
    output logic                        ctrlwr_ready,
    input  logic [ADDR_WIDTH-1:0]       ctrlwr_pkt_addr,
    input  logic [31:0]                 ctrlwr_pkt_data,
    output logic                        ctrlwr_error,

    // Configuration Interface (FIXED: Channel reset restored)
    input  logic                        cfg_channel_reset,      // FIXED: Restored

    // Status Interface (FIXED: Idle signal restored)
    output logic                        ctrlwr_engine_idle,     // FIXED: Restored

    // Shared AXI4 Master Write Interface (32-bit data)
    output logic                        aw_valid,
    input  logic                        aw_ready,
    output logic [ADDR_WIDTH-1:0]       aw_addr,
    output logic [7:0]                  aw_len,
    output logic [2:0]                  aw_size,
    output logic [1:0]                  aw_burst,
    output logic [AXI_ID_WIDTH-1:0]     aw_id,
    output logic                        aw_lock,
    output logic [3:0]                  aw_cache,
    output logic [2:0]                  aw_prot,
    output logic [3:0]                  aw_qos,
    output logic [3:0]                  aw_region,

    // AXI Write Data Channel
    output logic                        w_valid,
    input  logic                        w_ready,
    output logic [31:0]                 w_data,
    output logic [3:0]                  w_strb,
    output logic                        w_last,

    // AXI Write Response Channel (Shared - monitor for our ID)
    input  logic                        b_valid,
    output logic                        b_ready,
    input  logic [AXI_ID_WIDTH-1:0]     b_id,
    input  logic [1:0]                  b_resp,

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
    end

    //=========================================================================
    // Internal Signals with w_/r_ Naming Convention
    //=========================================================================

    // FSM state - registered
    // NOTE: Ctrlwr engine uses simplified state encoding without ARBITRATE state
    // (single-channel module doesn't need arbitration, so we define local states)
    /* verilator lint_off VARHIDDEN */
    typedef enum logic [2:0] {
        WRITE_IDLE       = 3'b000,
        WRITE_ISSUE_ADDR = 3'b001,
        WRITE_ISSUE_DATA = 3'b010,
        WRITE_WAIT_RESP  = 3'b011,
        WRITE_COMPLETE   = 3'b100,
        WRITE_ERROR      = 3'b101
    } ctrlwr_engine_state_t;
    /* verilator lint_on VARHIDDEN */

    ctrlwr_engine_state_t r_current_state, w_next_state;

    // FIXED: Channel reset management
    logic r_channel_reset_active;
    logic w_safe_to_reset;
    logic w_fifo_empty;
    logic w_no_active_transaction;

    // Ctrlwr operation parameters - registered
    logic [ADDR_WIDTH-1:0] r_ctrlwr_addr;
    logic [31:0] r_ctrlwr_data;

    // AXI transaction tracking - registered
    logic r_addr_issued;
    logic r_data_issued;
    logic [1:0] r_write_resp;
    logic [AXI_ID_WIDTH-1:0] r_expected_axi_id;
    logic r_ctrlwr_error;

    // Control logic
    logic w_null_address;
    logic w_address_error;
    logic w_axi_response_error;
    logic w_both_phases_issued;
    logic w_transaction_complete;
    logic w_our_axi_response;

    // Ctrlwr request skid buffer signals
    logic w_ctrlwr_req_skid_valid_in, w_ctrlwr_req_skid_ready_in;
    logic w_ctrlwr_req_skid_valid_out, w_ctrlwr_req_skid_ready_out;
    logic [ADDR_WIDTH + 32 - 1:0] w_ctrlwr_req_skid_din, w_ctrlwr_req_skid_dout;

    // Monitor packet generation
    logic r_mon_valid;
    logic [63:0] r_mon_packet;

    //=========================================================================
    // FIXED: Channel Reset Management
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
    assign w_fifo_empty = !w_ctrlwr_req_skid_valid_out;
    assign w_no_active_transaction = !r_addr_issued && !r_data_issued;
    assign w_safe_to_reset = w_fifo_empty && w_no_active_transaction && (r_current_state == WRITE_IDLE);

    // Engine idle signal (FIXED: Restored)
    assign ctrlwr_engine_idle = (r_current_state == WRITE_IDLE) && !r_channel_reset_active && w_fifo_empty;

    //=========================================================================
    // Ctrlwr Request Skid Buffer
    //=========================================================================

    // Input side: Accept from scheduler when not in reset
    assign w_ctrlwr_req_skid_valid_in = ctrlwr_valid && !r_channel_reset_active;
    assign ctrlwr_ready = w_ctrlwr_req_skid_ready_in && !r_channel_reset_active;
    assign w_ctrlwr_req_skid_din = {ctrlwr_pkt_addr, ctrlwr_pkt_data};

    gaxi_skid_buffer #(
        .DATA_WIDTH(ADDR_WIDTH + 32),
        .DEPTH(2),
        .INSTANCE_NAME("CTRLWR_REQ_SKID")
    ) i_ctrlwr_req_skid_buffer (
        .axi_aclk(clk),
        .axi_aresetn(rst_n),
        .wr_valid(w_ctrlwr_req_skid_valid_in),
        .wr_ready(w_ctrlwr_req_skid_ready_in),
        .wr_data(w_ctrlwr_req_skid_din),
        .rd_valid(w_ctrlwr_req_skid_valid_out),
        .rd_ready(w_ctrlwr_req_skid_ready_out),
        .rd_data(w_ctrlwr_req_skid_dout),
        .count(),
        .rd_count()
    );

    assign w_ctrlwr_req_skid_ready_out = (r_current_state == WRITE_IDLE) && w_ctrlwr_req_skid_valid_out && !r_channel_reset_active;

    //=========================================================================
    // Address and Control Logic
    //=========================================================================

    // Check for null address (skip operation)
    assign w_null_address = (r_ctrlwr_addr == 64'h0);

    // Address validation (must be 4-byte aligned for 32-bit writes)
    assign w_address_error = (r_ctrlwr_addr[1:0] != 2'b00) && !w_null_address;

    // AXI response validation
    assign w_axi_response_error = (r_write_resp != 2'b00); // Not OKAY

    // Transaction tracking
    assign w_both_phases_issued = r_addr_issued && r_data_issued;
    assign w_transaction_complete = w_our_axi_response && b_valid;

    //=========================================================================
    // AXI Response Monitoring
    //=========================================================================

    // Check if AXI response is for our channel
    assign w_our_axi_response = b_valid && (b_id == r_expected_axi_id);

    // We're ready to accept AXI responses when waiting
    assign b_ready = (r_current_state == WRITE_WAIT_RESP) && w_our_axi_response;

    //=========================================================================
    // FIXED: FSM State Machine with Channel Reset (UPDATED: Use RAPIDS package states)
    //=========================================================================

    // State register
    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_current_state <= WRITE_IDLE;
        end else begin
            r_current_state <= w_next_state;
        end
    )


    // Next state logic with channel reset support
    always_comb begin
        w_next_state = r_current_state;

        case (r_current_state)
            WRITE_IDLE: begin
                if (r_channel_reset_active) begin
                    w_next_state = WRITE_IDLE; // Stay in idle during reset
                end else if (w_ctrlwr_req_skid_valid_out) begin
                    w_next_state = WRITE_ISSUE_ADDR;
                end
            end

            WRITE_ISSUE_ADDR: begin
                if (r_channel_reset_active) begin
                    w_next_state = WRITE_IDLE; // Reset forces return to idle
                end else if (w_address_error) begin
                    w_next_state = WRITE_ERROR;
                end else if (w_null_address) begin
                    w_next_state = WRITE_IDLE; // Skip null address operations
                end else if (r_addr_issued) begin
                    // BUG FIX #1: Only advance when address phase completes
                    w_next_state = WRITE_ISSUE_DATA;
                end
                // else stay in WRITE_ISSUE_ADDR until aw_ready handshake
            end

            WRITE_ISSUE_DATA: begin
                if (r_channel_reset_active) begin
                    w_next_state = WRITE_IDLE; // Reset forces return to idle
                end else if (w_both_phases_issued) begin
                    // BUG FIX #2: Only advance when both phases complete
                    w_next_state = WRITE_WAIT_RESP;
                end
                // else stay in WRITE_ISSUE_DATA until both addr and data complete
            end

            WRITE_WAIT_RESP: begin
                if (r_channel_reset_active) begin
                    w_next_state = WRITE_IDLE; // Reset forces return to idle
                end else if (w_transaction_complete) begin
                    if (w_axi_response_error) begin
                        w_next_state = WRITE_ERROR;
                    end else begin
                        w_next_state = WRITE_COMPLETE;
                    end
                end
            end

            WRITE_COMPLETE: begin
                w_next_state = WRITE_IDLE;
            end

            WRITE_ERROR: begin
                w_next_state = WRITE_IDLE;
            end

            default: begin
                w_next_state = WRITE_IDLE;
            end
        endcase
    end

    //=========================================================================
    // State Machine Registers and Control
    //=========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_ctrlwr_addr <= 64'h0;
            r_ctrlwr_data <= 32'h0;
            r_addr_issued <= 1'b0;
            r_data_issued <= 1'b0;
            r_write_resp <= 2'b00;
            r_expected_axi_id <= '0;
            r_ctrlwr_error <= 1'b0;
        end else begin
            case (r_current_state)
                WRITE_IDLE: begin
                    if (w_ctrlwr_req_skid_valid_out && w_ctrlwr_req_skid_ready_out) begin
                        // Latch new ctrlwr request
                        {r_ctrlwr_addr, r_ctrlwr_data} <= w_ctrlwr_req_skid_dout;
                        r_expected_axi_id <= {{(AXI_ID_WIDTH-CHAN_WIDTH){1'b0}}, CHANNEL_ID[CHAN_WIDTH-1:0]};
                    end
                    r_addr_issued <= 1'b0;
                    r_data_issued <= 1'b0;
                    r_write_resp <= 2'b00;
                    // BUG FIX #3: Don't auto-clear error in IDLE
                    // Error should persist until reset or channel_reset (handled below)
                    // r_ctrlwr_error <= 1'b0;  // REMOVED
                end

                WRITE_ISSUE_ADDR: begin
                    if (w_address_error) begin
                        r_ctrlwr_error <= 1'b1;
                    end else if (!w_null_address && aw_ready) begin
                        r_addr_issued <= 1'b1;
                    end
                end

                WRITE_ISSUE_DATA: begin
                    if (w_ready) begin
                        r_data_issued <= 1'b1;
                    end
                end

                WRITE_WAIT_RESP: begin
                    if (w_transaction_complete) begin
                        r_write_resp <= b_resp;
                        if (w_axi_response_error) begin
                            r_ctrlwr_error <= 1'b1;
                        end
                    end
                end

                WRITE_ERROR: begin
                    r_ctrlwr_error <= 1'b1;
                end

                default: begin
                    // Maintain state
                end
            endcase

            // FIXED: Reset all state during channel reset
            if (r_channel_reset_active) begin
                r_addr_issued <= 1'b0;
                r_data_issued <= 1'b0;
                r_write_resp <= 2'b00;
                r_ctrlwr_error <= 1'b0;
            end
        end
    )


    //=========================================================================
    // AXI Write Address Channel Output
    //=========================================================================

    assign aw_valid = (r_current_state == WRITE_ISSUE_ADDR) && !w_null_address && !w_address_error && !r_addr_issued;
    assign aw_addr = r_ctrlwr_addr;
    assign aw_len = 8'h00;           // Single beat transfer
    assign aw_size = 3'b010;         // 4 bytes (32-bit)
    assign aw_burst = 2'b01;         // INCR burst type
    assign aw_id = r_expected_axi_id;
    assign aw_lock = 1'b0;           // Normal access
    assign aw_cache = 4'b0010;       // Normal non-cacheable bufferable
    assign aw_prot = 3'b000;         // Data, secure, unprivileged
    assign aw_qos = 4'h0;            // No QoS
    assign aw_region = 4'h0;         // No region

    //=========================================================================
    // AXI Write Data Channel Output
    //=========================================================================

    assign w_valid = (r_current_state == WRITE_ISSUE_DATA) && !w_null_address && r_addr_issued && !r_data_issued;
    assign w_data = r_ctrlwr_data;
    assign w_strb = 4'b1111;         // All bytes valid
    assign w_last = 1'b1;            // Single beat transfer

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
                WRITE_ERROR: begin
                    if (w_address_error) begin
                        // Log address alignment error
                        r_mon_valid <= 1'b1;
                        r_mon_packet <= create_monitor_packet(
                            PktTypeError,
                            PROTOCOL_CORE,
                            CORE_ERR_CTRLWR_ENGINE,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            r_ctrlwr_addr[34:0]
                        );
                    end else if (w_axi_response_error) begin
                        // Log AXI response error
                        r_mon_valid <= 1'b1;
                        r_mon_packet <= create_monitor_packet(
                            PktTypeError,
                            PROTOCOL_AXI,
                            (r_write_resp == 2'b10) ? AXI_ERR_RESP_SLVERR : AXI_ERR_RESP_DECERR,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            {16'h0, r_write_resp, 17'h0}
                        );
                    end
                end

                WRITE_COMPLETE: begin
                    if (!w_null_address) begin
                        // Log successful completion
                        r_mon_valid <= 1'b1;
                        r_mon_packet <= create_monitor_packet(
                            PktTypeCompletion,
                            PROTOCOL_CORE,
                            CORE_COMPL_CTRLWR_COMPLETED,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            r_ctrlwr_addr[34:0]
                        );
                    end
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

    assign ctrlwr_error = r_ctrlwr_error;
    assign mon_valid = r_mon_valid;
    assign mon_packet = r_mon_packet;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // State machine one-hot
    property state_one_hot;
        @(posedge clk) disable iff (!rst_n)
        $onehot(r_current_state);
    endproperty
    assert property (state_one_hot);

    // AXI ID consistency
    property axi_id_matches_channel;
        @(posedge clk) disable iff (!rst_n)
        aw_valid |-> (aw_id[CHAN_WIDTH-1:0] == CHANNEL_ID[CHAN_WIDTH-1:0]);
    endproperty
    assert property (axi_id_matches_channel);

    // Address alignment for 32-bit writes
    property address_aligned;
        @(posedge clk) disable iff (!rst_n)
        (r_current_state == WRITE_ISSUE_DATA) && !w_null_address |-> (r_ctrlwr_addr[1:0] == 2'b00);
    endproperty
    assert property (address_aligned);

    // FIXED: Channel reset properties
    property channel_reset_blocks_inputs;
        @(posedge clk) disable iff (!rst_n)
        r_channel_reset_active |-> !ctrlwr_ready;
    endproperty
    assert property (channel_reset_blocks_inputs);

    property channel_reset_forces_idle;
        @(posedge clk) disable iff (!rst_n)
        r_channel_reset_active |-> ##[0:3] (r_current_state == WRITE_IDLE);
    endproperty
    assert property (channel_reset_forces_idle);

    property channel_reset_idle_signal;
        @(posedge clk) disable iff (!rst_n)
        ctrlwr_engine_idle |-> (r_current_state == WRITE_IDLE && !r_channel_reset_active);
    endproperty
    assert property (channel_reset_idle_signal);
    `endif

endmodule : ctrlwr_engine