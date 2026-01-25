//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: arbiter_priority_encoder
        // Purpose: //   High-speed priority encoder optimized for common client counts used in
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: arbiter_priority_encoder
        //==============================================================================
        // Description:
        //   High-speed priority encoder optimized for common client counts used in
        //   arbitration. Implements fixed-priority arbitration where lower-indexed
        //   clients have higher priority (client 0 wins all ties). For power-of-2
        //   client counts (4, 8, 16, 32), uses fully unrolled casez logic for maximum
        //   timing performance. For other counts, uses synthesizable loop.
        //
        // Features:
        //   - Configurable number of clients (2 to 32+)
        //   - Optimized implementations for 4, 8, 16, 32 clients
        //   - Generic loop-based implementation for other sizes
        //   - Dual request input support (masked and unmasked)
        //   - Single-cycle combinational operation
        //   - Minimal LUT depth (1-3 levels)
        //
        //------------------------------------------------------------------------------
        // Parameters:
        //------------------------------------------------------------------------------
        //   CLIENTS:
        //     Description: Number of requesting clients
        //     Type: int
        //     Range: 2 to 1024 (practical limit)
        //     Default: 4
        //     Constraints: Power-of-2 values get optimized implementation
        //
        //   N:
        //     Description: Derived parameter for winner ID width
        //     Type: int
        //     Default: $clog2(CLIENTS)
        //     Constraints: Automatically calculated, do not override
        //
        //------------------------------------------------------------------------------
        // Ports:
        //------------------------------------------------------------------------------
        //   Inputs:
        //     requests_masked[CLIENTS-1:0]:   Masked request vector (higher priority)
        //     requests_unmasked[CLIENTS-1:0]: Unmasked request vector (fallback)
        //     any_masked_requests:             Select between masked/unmasked
        //
        //   Outputs:
        //     winner[N-1:0]:  Binary-encoded winner client ID
        //     winner_valid:   Winner output is valid (at least one request)
        //
        //------------------------------------------------------------------------------
        // Timing:
        //------------------------------------------------------------------------------
        //   Latency: Combinational (0 cycles)
        //   Propagation Delay:
        //     - Optimized (4,8,16,32 clients): 1-2 LUT levels
        //     - Generic (<64 clients): 2-3 LUT levels
        //     - Generic (>64 clients): 3-4 LUT levels
        //   Critical Path: Through casez or priority loop
        //
        //------------------------------------------------------------------------------
        // Behavior:
        //------------------------------------------------------------------------------
        //   Priority Order:
        //   - Client 0 has highest priority
        //   - Client 1 has second highest priority
        //   - ...
        //   - Client CLIENTS-1 has lowest priority
        //
        //   Request Selection:
        //   1. If any_masked_requests = 1:
        //      - Evaluate requests_masked
        //      - Find lowest-indexed asserted bit
        //   2. If any_masked_requests = 0:
        //      - Evaluate requests_unmasked
        //      - Find lowest-indexed asserted bit
        //   3. If no requests asserted:
        //      - winner = 0 (don't care)
        //      - winner_valid = 0
        //
        //   Optimized Implementations:
        //   - CLIENTS == 4:  Fully unrolled casez with 4 cases
        //   - CLIENTS == 8:  Fully unrolled casez with 8 cases
        //   - CLIENTS == 16: Fully unrolled casez with 16 cases
        //   - CLIENTS == 32: Fully unrolled casez with 32 cases
        //   - Other:         Synthesizable for-loop with priority flag
        //
        //   Example (4 clients, requests = 4'b0101):
        //   - Bit 0 = 1 (client 0 requesting)
        //   - Bit 2 = 1 (client 2 requesting)
        //   - Result: winner = 0, winner_valid = 1
        //   - Client 0 wins (lower index = higher priority)
        //
        //   Timing Diagram (CLIENTS=4, demonstrating priority):
        //
        //   {signal: [
        //     {name: 'requests[3:0]', wave: '3.4.5.6.7.', data: ['0001','0010','0011','0100','0101']},
        //     {},
        //     {name: 'winner[1:0]',   wave: '=.=.=.=.=.', data: ['0','1','0','2','0']},
        //     {name: 'winner_valid',  wave: '1..........'},
        //     {},
        //     {name: 'Priority',      wave: '2.4.2.6.2.', data: ['C0','C1','C0 wins','C2','C0 wins']},
        //     {},
        //     {name: 'Note',          wave: 'x.2.......x', data: ['Lower index = higher priority']}
        //   ]}
        //
        //------------------------------------------------------------------------------
        // Usage Example:
        //------------------------------------------------------------------------------
        //   // Standalone priority encoder (single request input)
        //   arbiter_priority_encoder #(
        //       .CLIENTS(8)
        //   ) u_pri_enc (
        //       .requests_masked   (8'b0),           // Unused
        //       .requests_unmasked (client_reqs),     // Primary request vector
        //       .any_masked_requests(1'b0),          // Always use unmasked
        //       .winner            (winner_id),
        //       .winner_valid      (grant_valid)
        //   );
        //
        //   // Dual-input priority encoder (masked + unmasked)
        //   arbiter_priority_encoder #(
        //       .CLIENTS(16)
        //   ) u_pri_enc_dual (
        //       .requests_masked    (masked_reqs),    // Higher priority requests
        //       .requests_unmasked  (all_reqs),       // All requests
        //       .any_masked_requests(|masked_reqs),   // Select masked if any present
        //       .winner             (winner_id),
        //       .winner_valid       (grant_valid)
        //   );
        //
        //   // Used in round-robin arbiter
        //   // (masked requests = clients above last winner, unmasked = all clients)
        //   arbiter_priority_encoder #(
        //       .CLIENTS(CLIENTS)
        //   ) u_priority_encoder (
        //       .requests_masked    (w_requests_masked),
        //       .requests_unmasked  (w_requests_unmasked),
        //       .any_masked_requests(w_any_masked_requests),
        //       .winner             (w_winner),
        //       .winner_valid       (w_winner_valid)
        //   );
        //
        //------------------------------------------------------------------------------
        // Notes:
        //------------------------------------------------------------------------------
        //   - **Combinational logic only** - No clock or reset
        //   - Lower index = higher priority (client 0 always wins if requesting)
        //   - Masked input has priority over unmasked (selected by any_masked_requests)
        //   - Winner output is don't-care when winner_valid = 0
        //   - **Synthesis:** Optimized casez infers efficient priority logic
        //   - **Timing:** Unrolled versions typically meet 500+ MHz on modern FPGAs
        //   - **Area:** O(CLIENTS) for optimized, O(CLIENTS × log(CLIENTS)) for generic
        //   - For CLIENTS > 32, consider hierarchical priority encoding
        //   - Used internally by arbiter_round_robin for winner selection
        //
        //------------------------------------------------------------------------------
        // Related Modules:
        //------------------------------------------------------------------------------
        //   - arbiter_round_robin.sv - Uses this module for winner selection
        //   - arbiter_round_robin_simple.sv - Alternative simplified arbiter
        //   - arbiter_round_robin_weighted.sv - Weighted arbitration
        //   - encoder.sv - General-purpose binary encoder
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_arbiter_priority_encoder.py
        //   Run: pytest val/common/test_arbiter_priority_encoder.py -v
        //   Coverage: 95%
        //   Key Test Scenarios:
        //     - Priority order verification (all bit patterns)
        //     - Masked vs unmasked selection
        //     - No requests (winner_valid = 0)
        //     - All clients requesting simultaneously
        //     - Single client at a time
        //     - Power-of-2 sizes (4, 8, 16, 32)
        //     - Non-power-of-2 sizes (5, 12 - generic implementation)
        //
        //------------------------------------------------------------------------------
        // References:
        //------------------------------------------------------------------------------
        //   - "Arbiters: Design Ideas and Coding Styles" - Matt Weber, SNUG 2001
        //   - SystemVerilog casez statement - IEEE 1800-2017 Section 12.5
        //   - Priority encoder algorithms - Digital Design textbooks
        //
        //==============================================================================
        
        module arbiter_priority_encoder #(
            parameter int CLIENTS = 4,
            parameter int N = $clog2(CLIENTS)
        ) (
%000000     input  logic [CLIENTS-1:0]  requests_masked,
 000012     input  logic [CLIENTS-1:0]  requests_unmasked,
 000056     input  logic                any_masked_requests,
        
 000060     output logic [N-1:0]        winner,
 000298     output logic                winner_valid
        );
        
            // Priority selection: masked requests have priority
 000012     logic [CLIENTS-1:0] w_priority_requests;
            assign w_priority_requests = any_masked_requests ? requests_masked : requests_unmasked;
        
            // =======================================================================
            // OPTIMIZED PRIORITY ENCODER IMPLEMENTATIONS
            // Use unrolled casez logic for common power-of-2 sizes, loop for others
            // =======================================================================
        
            generate
                if (CLIENTS == 4) begin : gen_pe_4
                    // Fully unrolled 4-input priority encoder using casez
                    // Priority: client 0 > client 1 > client 2 > client 3
%000000             always_comb begin
%000000                 casez (w_priority_requests)
%000000                     4'b???1: begin winner = 2'd0; winner_valid = 1'b1; end  // Client 0 has highest priority
%000000                     4'b??10: begin winner = 2'd1; winner_valid = 1'b1; end  // Client 1 if client 0 not requesting
%000000                     4'b?100: begin winner = 2'd2; winner_valid = 1'b1; end  // Client 2 if clients 0,1 not requesting
%000000                     4'b1000: begin winner = 2'd3; winner_valid = 1'b1; end  // Client 3 if only client 3 requesting
%000000                     default: begin winner = 2'd0; winner_valid = 1'b0; end
                        endcase
                    end
                end
        
                else if (CLIENTS == 8) begin : gen_pe_8
                    // Fully unrolled 8-input priority encoder using casez
                    // Priority: client 0 > client 1 > ... > client 7
%000000             always_comb begin
%000000                 casez (w_priority_requests)
%000000                     8'b???????1: begin winner = 3'd0; winner_valid = 1'b1; end
%000000                     8'b??????10: begin winner = 3'd1; winner_valid = 1'b1; end
%000000                     8'b?????100: begin winner = 3'd2; winner_valid = 1'b1; end
%000000                     8'b????1000: begin winner = 3'd3; winner_valid = 1'b1; end
%000000                     8'b???10000: begin winner = 3'd4; winner_valid = 1'b1; end
%000000                     8'b??100000: begin winner = 3'd5; winner_valid = 1'b1; end
%000000                     8'b?1000000: begin winner = 3'd6; winner_valid = 1'b1; end
%000000                     8'b10000000: begin winner = 3'd7; winner_valid = 1'b1; end
%000000                     default:     begin winner = 3'd0; winner_valid = 1'b0; end
                        endcase
                    end
                end
        
                else if (CLIENTS == 16) begin : gen_pe_16
                    // Fully unrolled 16-input priority encoder using casez
                    // Priority: client 0 > client 1 > ... > client 15
                    always_comb begin
                        casez (w_priority_requests)
                            16'b???????????????1: begin winner = 4'd0;  winner_valid = 1'b1; end
                            16'b??????????????10: begin winner = 4'd1;  winner_valid = 1'b1; end
                            16'b?????????????100: begin winner = 4'd2;  winner_valid = 1'b1; end
                            16'b????????????1000: begin winner = 4'd3;  winner_valid = 1'b1; end
                            16'b???????????10000: begin winner = 4'd4;  winner_valid = 1'b1; end
                            16'b??????????100000: begin winner = 4'd5;  winner_valid = 1'b1; end
                            16'b?????????1000000: begin winner = 4'd6;  winner_valid = 1'b1; end
                            16'b????????10000000: begin winner = 4'd7;  winner_valid = 1'b1; end
                            16'b???????100000000: begin winner = 4'd8;  winner_valid = 1'b1; end
                            16'b??????1000000000: begin winner = 4'd9;  winner_valid = 1'b1; end
                            16'b?????10000000000: begin winner = 4'd10; winner_valid = 1'b1; end
                            16'b????100000000000: begin winner = 4'd11; winner_valid = 1'b1; end
                            16'b???1000000000000: begin winner = 4'd12; winner_valid = 1'b1; end
                            16'b??10000000000000: begin winner = 4'd13; winner_valid = 1'b1; end
                            16'b?100000000000000: begin winner = 4'd14; winner_valid = 1'b1; end
                            16'b1000000000000000: begin winner = 4'd15; winner_valid = 1'b1; end
                            default:              begin winner = 4'd0;  winner_valid = 1'b0; end
                        endcase
                    end
                end
        
                else if (CLIENTS == 32) begin : gen_pe_32
                    // Fully unrolled 32-input priority encoder using casez
                    // Priority: client 0 > client 1 > ... > client 31
                    // Assumes w_priority_requests[0] is the LSB (rightmost bit)
                    always_comb begin
                        casez (w_priority_requests)
                            32'b???????????????????????????????1: begin winner = 5'd0;  winner_valid = 1'b1; end
                            32'b??????????????????????????????10: begin winner = 5'd1;  winner_valid = 1'b1; end
                            32'b?????????????????????????????100: begin winner = 5'd2;  winner_valid = 1'b1; end
                            32'b????????????????????????????1000: begin winner = 5'd3;  winner_valid = 1'b1; end
                            32'b???????????????????????????10000: begin winner = 5'd4;  winner_valid = 1'b1; end
                            32'b??????????????????????????100000: begin winner = 5'd5;  winner_valid = 1'b1; end
                            32'b?????????????????????????1000000: begin winner = 5'd6;  winner_valid = 1'b1; end
                            32'b????????????????????????10000000: begin winner = 5'd7;  winner_valid = 1'b1; end
                            32'b???????????????????????100000000: begin winner = 5'd8;  winner_valid = 1'b1; end
                            32'b??????????????????????1000000000: begin winner = 5'd9;  winner_valid = 1'b1; end
                            32'b?????????????????????10000000000: begin winner = 5'd10; winner_valid = 1'b1; end
                            32'b????????????????????100000000000: begin winner = 5'd11; winner_valid = 1'b1; end
                            32'b???????????????????1000000000000: begin winner = 5'd12; winner_valid = 1'b1; end
                            32'b??????????????????10000000000000: begin winner = 5'd13; winner_valid = 1'b1; end
                            32'b?????????????????100000000000000: begin winner = 5'd14; winner_valid = 1'b1; end
                            32'b????????????????1000000000000000: begin winner = 5'd15; winner_valid = 1'b1; end
                            32'b???????????????10000000000000000: begin winner = 5'd16; winner_valid = 1'b1; end
                            32'b??????????????100000000000000000: begin winner = 5'd17; winner_valid = 1'b1; end
                            32'b?????????????1000000000000000000: begin winner = 5'd18; winner_valid = 1'b1; end
                            32'b????????????10000000000000000000: begin winner = 5'd19; winner_valid = 1'b1; end
                            32'b???????????100000000000000000000: begin winner = 5'd20; winner_valid = 1'b1; end
                            32'b??????????1000000000000000000000: begin winner = 5'd21; winner_valid = 1'b1; end
                            32'b?????????10000000000000000000000: begin winner = 5'd22; winner_valid = 1'b1; end
                            32'b????????100000000000000000000000: begin winner = 5'd23; winner_valid = 1'b1; end
                            32'b???????1000000000000000000000000: begin winner = 5'd24; winner_valid = 1'b1; end
                            32'b??????10000000000000000000000000: begin winner = 5'd25; winner_valid = 1'b1; end
                            32'b?????100000000000000000000000000: begin winner = 5'd26; winner_valid = 1'b1; end
                            32'b????1000000000000000000000000000: begin winner = 5'd27; winner_valid = 1'b1; end
                            32'b???10000000000000000000000000000: begin winner = 5'd28; winner_valid = 1'b1; end
                            32'b??100000000000000000000000000000: begin winner = 5'd29; winner_valid = 1'b1; end
                            32'b?1000000000000000000000000000000: begin winner = 5'd30; winner_valid = 1'b1; end
                            32'b10000000000000000000000000000000: begin winner = 5'd31; winner_valid = 1'b1; end
                            default:                             begin winner = 5'd0;  winner_valid = 1'b0; end
                        endcase
                    end
                end
        
                else begin : gen_pe_generic
                    // Generic loop-based priority encoder for non-standard sizes
                    // Synthesizable version without break statement
                    always_comb begin
                        winner = '0;
                        winner_valid = 1'b0;
        
                        // Use flag to implement priority (first match wins)
                        for (int i = 0; i < CLIENTS; i++) begin
                            if (w_priority_requests[i] && !winner_valid) begin
                                winner = i[N-1:0];
                                winner_valid = 1'b1;
                            end
                        end
                    end
                end
            endgenerate
        
        endmodule : arbiter_priority_encoder
        
