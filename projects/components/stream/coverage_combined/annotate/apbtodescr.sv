//      // verilator_coverage annotation
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
 000750     input  logic                        clk,
%000002     input  logic                        rst_n,
        
            // APB Slave CMD/RSP Interface (from PeakRDL apb_slave)
            // CMD: Master → Slave (write request)
%000008     input  logic                        apb_cmd_valid,
 000010     output logic                        apb_cmd_ready,
%000000     input  logic [ADDR_WIDTH-1:0]       apb_cmd_addr,
%000000     input  logic [DATA_WIDTH-1:0]       apb_cmd_wdata,
%000009     input  logic                        apb_cmd_write,   // 1=write, 0=read
        
            // RSP: Slave → Master (response)
%000008     output logic                        apb_rsp_valid,
%000006     input  logic                        apb_rsp_ready,
%000000     output logic [DATA_WIDTH-1:0]       apb_rsp_rdata,
%000000     output logic                        apb_rsp_error,
        
            // Descriptor Engine APB Ports (to descriptor_engine[0..7])
            // NOTE: Uses 64-bit address width for descriptor addresses
%000000     output logic [NUM_CHANNELS-1:0]                 desc_apb_valid,
%000002     input  logic [NUM_CHANNELS-1:0]                 desc_apb_ready,
            output logic [NUM_CHANNELS-1:0][63:0]           desc_apb_addr,
        
            // Integration Control Signal
            // Indicates this module is handling a kick-off transaction
            // Parent module should mux APB response from this block when asserted
%000004     output logic                                    apb_descriptor_kickoff_hit
        );
        
            //=========================================================================
            // Internal Signals
            //=========================================================================
        
            // Address decode
%000000     logic [2:0]             channel_id;          // Decoded channel ID (0-7, 3 bits)
%000008     logic                   addr_in_range;       // Address within valid range
        
            // FSM for transaction control
            typedef enum logic [2:0] {
                IDLE          = 3'b000,    // Waiting for APB command (LOW write)
                RESPOND_LOW   = 3'b001,    // Sending response after LOW write
                WAIT_HIGH     = 3'b010,    // Waiting for HIGH write
                ROUTE         = 3'b011,    // Routing to descriptor engine
                RESPOND_HIGH  = 3'b100     // Sending final response after HIGH write
            } state_t;
        
%000004     state_t r_state, w_next_state;
        
            // Registered transaction info
%000000     logic [2:0]             r_channel_id;        // Latched channel ID (0-7, 3 bits)
%000000     logic [DATA_WIDTH-1:0]  r_wdata_low;         // Latched LOW write data [31:0]
%000000     logic [DATA_WIDTH-1:0]  r_wdata_high;        // Latched HIGH write data [63:32]
%000000     logic                   r_error;             // Latched error flag
 000012     logic                   r_is_high_write;     // Current write is HIGH (bit 2 = 1)
        
            //=========================================================================
            // Address Decode
            //=========================================================================
        
            // Extract channel ID from address (dword-aligned: addr[5:3])
            // Address bits [1:0] are ignored (word-aligned)
            // Address bit  [2]   selects LOW (0) or HIGH (1) register
            // Address bits [5:3] select channel 0-7
            assign channel_id = apb_cmd_addr[5:3];
            assign r_is_high_write = apb_cmd_addr[2];
        
            // Check if address is within valid range (first 4KB of address space)
            // Valid: 0x00 to 0x3F (8 channels × 8 bytes) within lower 12 bits
            assign addr_in_range = ({20'h0, apb_cmd_addr[11:0]} < (NUM_CHANNELS * 8));
        
            //=========================================================================
            // FSM State Register
            //=========================================================================
        
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_state <= IDLE;
                end else begin
                    r_state <= w_next_state;
                end
 000022     )
        
        
            //=========================================================================
            // FSM Next State Logic
            //=========================================================================
        
 002401     always_comb begin
 002401         w_next_state = r_state;  // Default: hold state
        
 002401         case (r_state)
 001380             IDLE: begin
                        // Wait for valid APB command (must be LOW write first)
%000000                 if (apb_cmd_valid && !apb_cmd_write) begin
                            // Read not supported - go directly to error response
%000000                     w_next_state = RESPOND_LOW;
 000018                 end else if (apb_cmd_valid && apb_cmd_write) begin
%000000                     if (!r_is_high_write) begin
                                // LOW write - respond, then wait for HIGH
 000018                         w_next_state = RESPOND_LOW;
%000000                     end else begin
                                // HIGH write without LOW - error
%000000                         w_next_state = RESPOND_LOW;
                            end
                        end
                    end
        
 000018             RESPOND_LOW: begin
                        // Send response after LOW write (or error)
%000000                 if (apb_rsp_ready) begin
%000000                     if (r_error) begin
                                // Error during LOW write - return to IDLE
%000000                         w_next_state = IDLE;
 000018                     end else begin
                                // Successful LOW write - wait for HIGH write
 000018                         w_next_state = WAIT_HIGH;
                            end
                        end
                    end
        
 000210             WAIT_HIGH: begin
                        // Wait for HIGH write to complete the 64-bit address
%000000                 if (apb_cmd_valid && !apb_cmd_write) begin
                            // Read during sequence - error
%000000                     w_next_state = RESPOND_HIGH;
 000018                 end else if (apb_cmd_valid && apb_cmd_write) begin
%000000                     if (r_is_high_write && (channel_id == r_channel_id)) begin
                                // HIGH write to same channel - proceed to ROUTE
 000018                         w_next_state = ROUTE;
%000000                     end else begin
                                // Wrong write (LOW again or different channel) - error
%000000                         w_next_state = RESPOND_HIGH;
                            end
                        end
                    end
        
 000018             ROUTE: begin
                        // Wait for descriptor engine to accept
                        // Only the selected channel's ready matters
%000000                 if (r_error) begin
                            // Address error - skip routing, go to response
%000000                     w_next_state = RESPOND_HIGH;
%000000                 end else if (desc_apb_ready[r_channel_id]) begin
                            // Descriptor engine accepted - go to response
 000018                     w_next_state = RESPOND_HIGH;
                        end
                        // Otherwise stay in ROUTE (back-pressure from descriptor engine)
                    end
        
 000018             RESPOND_HIGH: begin
                        // Send final response after HIGH write (or error)
%000000                 if (apb_rsp_ready) begin
 000018                     w_next_state = IDLE;
                        end
                    end
        
%000000             default: begin
%000000                 w_next_state = IDLE;  // Safety: recover to IDLE
                    end
                endcase
            end
        
            //=========================================================================
            // Transaction Capture (IDLE state)
            //=========================================================================
        
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_channel_id <= 3'h0;
                    r_wdata_low <= '0;
                    r_wdata_high <= '0;
                    r_error <= 1'b0;
                end else begin
                    // Capture LOW write in IDLE state
                    if (r_state == IDLE && apb_cmd_valid) begin
                        if (!apb_cmd_write) begin
                            r_error <= 1'b1;  // Read not supported
                        end else if (!addr_in_range) begin
                            r_error <= 1'b1;  // Address out of range
                        end else if (r_is_high_write) begin
                            r_error <= 1'b1;  // HIGH write without LOW
                        end else begin
                            // Valid LOW write
                            r_channel_id <= channel_id;
                            r_wdata_low <= apb_cmd_wdata;
                            r_error <= 1'b0;
                        end
                    end
        
                    // Capture HIGH write in WAIT_HIGH state
                    if (r_state == WAIT_HIGH && apb_cmd_valid) begin
                        if (!apb_cmd_write) begin
                            r_error <= 1'b1;  // Read during sequence
                        end else if (!r_is_high_write) begin
                            r_error <= 1'b1;  // LOW write again
                        end else if (channel_id != r_channel_id) begin
                            r_error <= 1'b1;  // Different channel
                        end else begin
                            // Valid HIGH write
                            r_wdata_high <= apb_cmd_wdata;
                            r_error <= 1'b0;
                        end
                    end
                end
%000000     )
        
        
            //=========================================================================
            // APB CMD Interface Outputs
            //=========================================================================
        
            // Accept command when in IDLE or WAIT_HIGH state
            assign apb_cmd_ready = (r_state == IDLE) || (r_state == WAIT_HIGH);
        
            //=========================================================================
            // APB RSP Interface Outputs
            //=========================================================================
        
            // Assert response valid in RESPOND_LOW or RESPOND_HIGH state
            assign apb_rsp_valid = (r_state == RESPOND_LOW) || (r_state == RESPOND_HIGH);
        
            // Read data always zero (writes only)
            assign apb_rsp_rdata = '0;
        
            // Error flag from latched error
            assign apb_rsp_error = r_error;
        
            //=========================================================================
            // Descriptor Engine APB Outputs
            //=========================================================================
        
            // Generate per-channel valid signals
 002401     always_comb begin
 002401         desc_apb_valid = '0;  // Default: no valid
        
                // Assert valid for selected channel when in ROUTE state (and no error)
 000018         if (r_state == ROUTE && !r_error) begin
 000018             desc_apb_valid[r_channel_id] = 1'b1;
                end
            end
        
            // Broadcast assembled 64-bit descriptor address to all channels
            // Only the selected channel's valid will be asserted
%000002     always_comb begin
%000002         for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
                    // Assemble 64-bit descriptor address from LOW + HIGH writes
 000016             desc_apb_addr[ch] = {r_wdata_high, r_wdata_low};
                end
            end
        
            //=========================================================================
            // Integration Control Signal
            //=========================================================================
        
            // Assert when this block is handling a valid kick-off transaction
            // Only assert during ROUTE/RESPOND_HIGH (not during RESPOND_LOW - still waiting for HIGH write)
            // Parent module uses this to mux between register file responses and kick-off responses
            assign apb_descriptor_kickoff_hit = (r_state == ROUTE || r_state == RESPOND_HIGH) && !r_error;
        
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
        
            // Response valid only in RESPOND_LOW or RESPOND_HIGH state
            property response_in_respond_state;
                @(posedge clk) disable iff (!rst_n)
                apb_rsp_valid |-> ((r_state == RESPOND_LOW) || (r_state == RESPOND_HIGH));
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
        
