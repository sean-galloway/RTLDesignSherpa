// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apbtodescr
// Purpose: APB-to-Descriptor Engine Router - Address-based routing glue logic
//
// Description:
//   Routes APB writes from register slave to descriptor engine APB kick-off ports.
//   Address decode determines target channel, write data becomes descriptor address.
//
//   Address Map (relative to BASE_ADDR):
//     BASE + 0x00 → Channel 0 descriptor address
//     BASE + 0x04 → Channel 1 descriptor address
//     BASE + 0x08 → Channel 2 descriptor address
//     BASE + 0x0C → Channel 3 descriptor address
//     BASE + 0x10 → Channel 4 descriptor address
//     BASE + 0x14 → Channel 5 descriptor address
//     BASE + 0x18 → Channel 6 descriptor address
//     BASE + 0x1C → Channel 7 descriptor address
//
//   Write Flow:
//     1. Software writes descriptor address to CHx_CTRL register
//     2. PeakRDL APB slave presents write on cmd/rsp interface
//     3. This module decodes address → channel_id
//     4. Asserts desc_apb_valid[channel_id], drives desc_apb_addr[channel_id]
//     5. Waits for desc_apb_ready[channel_id] (descriptor engine accepted)
//     6. Completes APB transaction (asserts apb_rsp_valid)
//
//   Key Features:
//     - No internal registers (pure routing logic)
//     - Parameterized base address
//     - Back-pressure handling (delays rsp_ready if descriptor engine busy)
//     - Address range checking (error on out-of-range)
//     - Integration signal (apb_descriptor_kickoff_hit) for response muxing
//
//   Integration:
//     The apb_descriptor_kickoff_hit signal allows parent modules to mux APB
//     responses between register file and kick-off logic. When asserted, the
//     parent should route apb_rsp_* from this module instead of register file.
//
// Documentation: projects/components/stream/docs/stream_spec/ch02_blocks/00_apbtodescr.md
// Subsystem: stream_macro
//
// Author: sean galloway
// Created: 2025-10-20

`timescale 1ns / 1ps

// Import STREAM packages
`include "stream_imports.svh"
`include "reset_defs.svh"


module apbtodescr #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int NUM_CHANNELS = 8
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // APB Slave CMD/RSP Interface (from PeakRDL apb_slave)
    // CMD: Master → Slave (write request)
    input  logic                        apb_cmd_valid,
    output logic                        apb_cmd_ready,
    input  logic [ADDR_WIDTH-1:0]       apb_cmd_addr,
    input  logic [DATA_WIDTH-1:0]       apb_cmd_wdata,
    input  logic                        apb_cmd_write,   // 1=write, 0=read

    // RSP: Slave → Master (response)
    output logic                        apb_rsp_valid,
    input  logic                        apb_rsp_ready,
    output logic [DATA_WIDTH-1:0]       apb_rsp_rdata,
    output logic                        apb_rsp_error,

    // Descriptor Engine APB Ports (to descriptor_engine[0..7])
    // NOTE: Uses 64-bit address width for descriptor addresses
    output logic [NUM_CHANNELS-1:0]                 desc_apb_valid,
    input  logic [NUM_CHANNELS-1:0]                 desc_apb_ready,
    output logic [NUM_CHANNELS-1:0][63:0]           desc_apb_addr,

    // Integration Control Signal
    // Indicates this module is handling a kick-off transaction
    // Parent module should mux APB response from this block when asserted
    output logic                                    apb_descriptor_kickoff_hit
);

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // Address decode
    logic [2:0]             channel_id;          // Decoded channel ID (0-7, 3 bits)
    logic                   addr_in_range;       // Address within valid range

    // FSM for transaction control
    typedef enum logic [1:0] {
        IDLE        = 2'b00,    // Waiting for APB command
        ROUTE       = 2'b01,    // Routing to descriptor engine
        RESPOND     = 2'b10     // Sending APB response
    } state_t;

    state_t r_state, w_next_state;

    // Registered transaction info
    logic [2:0]             r_channel_id;        // Latched channel ID (0-7, 3 bits)
    logic [DATA_WIDTH-1:0]  r_wdata;             // Latched write data
    logic                   r_error;             // Latched error flag

    //=========================================================================
    // Address Decode
    //=========================================================================

    // Extract channel ID from address (word-aligned: addr[4:2])
    // Address bits [1:0] are ignored (word-aligned)
    // Address bits [4:2] select channel 0-7
    assign channel_id = apb_cmd_addr[4:2];

    // Check if address is within valid range (first 4KB of address space)
    // Valid: 0x00 to 0x1C (8 channels × 4 bytes) within lower 12 bits
    assign addr_in_range = ({20'h0, apb_cmd_addr[11:0]} < (NUM_CHANNELS * 4));

    //=========================================================================
    // FSM State Register
    //=========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_state <= IDLE;
        end else begin
            r_state <= w_next_state;
        end
    )


    //=========================================================================
    // FSM Next State Logic
    //=========================================================================

    always_comb begin
        w_next_state = r_state;  // Default: hold state

        case (r_state)
            IDLE: begin
                // Wait for valid APB command
                if (apb_cmd_valid && apb_cmd_write) begin
                    w_next_state = ROUTE;
                end else if (apb_cmd_valid && !apb_cmd_write) begin
                    // Read not supported - go directly to error response
                    w_next_state = RESPOND;
                end
            end

            ROUTE: begin
                // Wait for descriptor engine to accept
                // Only the selected channel's ready matters
                if (r_error) begin
                    // Address error - skip routing, go to response
                    w_next_state = RESPOND;
                end else if (desc_apb_ready[r_channel_id]) begin
                    // Descriptor engine accepted - go to response
                    w_next_state = RESPOND;
                end
                // Otherwise stay in ROUTE (back-pressure from descriptor engine)
            end

            RESPOND: begin
                // Wait for APB master to accept response
                if (apb_rsp_ready) begin
                    w_next_state = IDLE;
                end
            end

            default: begin
                w_next_state = IDLE;  // Safety: recover to IDLE
            end
        endcase
    end

    //=========================================================================
    // Transaction Capture (IDLE state)
    //=========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_channel_id <= 3'h0;
            r_wdata <= '0;
            r_error <= 1'b0;
        end else begin
            if (r_state == IDLE && apb_cmd_valid) begin
                // Latch transaction info
                r_channel_id <= channel_id;
                r_wdata <= apb_cmd_wdata;

                // Latch error conditions
                if (!apb_cmd_write) begin
                    r_error <= 1'b1;  // Read not supported
                end else if (!addr_in_range) begin
                    r_error <= 1'b1;  // Address out of range
                end else begin
                    r_error <= 1'b0;  // Valid write
                end
            end
        end
    )


    //=========================================================================
    // APB CMD Interface Outputs
    //=========================================================================

    // Accept command when in IDLE state
    assign apb_cmd_ready = (r_state == IDLE);

    //=========================================================================
    // APB RSP Interface Outputs
    //=========================================================================

    // Assert response valid in RESPOND state
    assign apb_rsp_valid = (r_state == RESPOND);

    // Read data always zero (writes only)
    assign apb_rsp_rdata = '0;

    // Error flag from latched error
    assign apb_rsp_error = r_error;

    //=========================================================================
    // Descriptor Engine APB Outputs
    //=========================================================================

    // Generate per-channel valid signals
    always_comb begin
        desc_apb_valid = '0;  // Default: no valid

        // Assert valid for selected channel when in ROUTE state (and no error)
        if (r_state == ROUTE && !r_error) begin
            desc_apb_valid[r_channel_id] = 1'b1;
        end
    end

    // Broadcast write data (descriptor address) to all channels
    // Only the selected channel's valid will be asserted
    always_comb begin
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            // Zero-extend 32-bit write data to 64-bit descriptor address
            // Upper 32 bits are 0 (assumes descriptors in lower 4GB)
            desc_apb_addr[ch] = {32'h0000_0000, r_wdata};
        end
    end

    //=========================================================================
    // Integration Control Signal
    //=========================================================================

    // Assert when this block is handling a valid kick-off transaction
    // Parent module uses this to mux between register file responses and kick-off responses
    assign apb_descriptor_kickoff_hit = (r_state == ROUTE || r_state == RESPOND) && !r_error;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // Only one channel can be selected at a time
    property one_channel_valid;
        @(posedge clk) disable iff (!rst_n)
        $onehot0(desc_apb_valid);  // At most one valid
    endproperty
    assert property (one_channel_valid);

    // Valid only asserted in ROUTE state
    property valid_only_in_route;
        @(posedge clk) disable iff (!rst_n)
        |desc_apb_valid |-> (r_state == ROUTE);
    endproperty
    assert property (valid_only_in_route);

    // Response valid only in RESPOND state
    property response_in_respond_state;
        @(posedge clk) disable iff (!rst_n)
        apb_rsp_valid |-> (r_state == RESPOND);
    endproperty
    assert property (response_in_respond_state);

    // No simultaneous cmd_ready and rsp_valid
    property no_overlap;
        @(posedge clk) disable iff (!rst_n)
        !(apb_cmd_ready && apb_rsp_valid);
    endproperty
    assert property (no_overlap);

    // Channel ID must be valid when routing
    property valid_channel_id;
        @(posedge clk) disable iff (!rst_n)
        (r_state == ROUTE && !r_error) |-> (r_channel_id < NUM_CHANNELS);
    endproperty
    assert property (valid_channel_id);
    `endif

endmodule : apbtodescr
