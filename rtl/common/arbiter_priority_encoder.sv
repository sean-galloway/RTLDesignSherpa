`timescale 1ns / 1ps

/*
================================================================================
OPTIMIZED PRIORITY ENCODER MODULE
================================================================================

This module implements a high-speed priority encoder optimized for common
client counts used in arbitration. For power-of-2 client counts (4,8,16,32),
it uses fully unrolled casez logic for maximum timing performance. For other counts,
it falls back to a synthesizable loop.

TIMING OPTIMIZATION:
- Unrolled versions: 1-2 LUT levels maximum
- Loop version: 2-3 LUT levels (still optimized)
- Priority order: Lower index = higher priority (client 0 wins ties)

USAGE:
- Connect requests_masked and requests_unmasked
- any_masked_requests selects between them
- winner and winner_valid provide the result
*/

module arbiter_priority_encoder #(
    parameter int CLIENTS = 4,
    parameter int N = $clog2(CLIENTS)
) (
    input  logic [CLIENTS-1:0]  requests_masked,
    input  logic [CLIENTS-1:0]  requests_unmasked,
    input  logic                any_masked_requests,

    output logic [N-1:0]        winner,
    output logic                winner_valid
);

    // Priority selection: masked requests have priority
    logic [CLIENTS-1:0] w_priority_requests;
    assign w_priority_requests = any_masked_requests ? requests_masked : requests_unmasked;

    // =======================================================================
    // OPTIMIZED PRIORITY ENCODER IMPLEMENTATIONS
    // Use unrolled casez logic for common power-of-2 sizes, loop for others
    // =======================================================================

    generate
        if (CLIENTS == 4) begin : gen_pe_4
            // Fully unrolled 4-input priority encoder using casez
            // Priority: client 0 > client 1 > client 2 > client 3
            always_comb begin
                casez (w_priority_requests)
                    4'b???1: begin winner = 2'd0; winner_valid = 1'b1; end  // Client 0 has highest priority
                    4'b??10: begin winner = 2'd1; winner_valid = 1'b1; end  // Client 1 if client 0 not requesting
                    4'b?100: begin winner = 2'd2; winner_valid = 1'b1; end  // Client 2 if clients 0,1 not requesting
                    4'b1000: begin winner = 2'd3; winner_valid = 1'b1; end  // Client 3 if only client 3 requesting
                    default: begin winner = 2'd0; winner_valid = 1'b0; end
                endcase
            end
        end

        else if (CLIENTS == 8) begin : gen_pe_8
            // Fully unrolled 8-input priority encoder using casez
            // Priority: client 0 > client 1 > ... > client 7
            always_comb begin
                casez (w_priority_requests)
                    8'b???????1: begin winner = 3'd0; winner_valid = 1'b1; end
                    8'b??????10: begin winner = 3'd1; winner_valid = 1'b1; end
                    8'b?????100: begin winner = 3'd2; winner_valid = 1'b1; end
                    8'b????1000: begin winner = 3'd3; winner_valid = 1'b1; end
                    8'b???10000: begin winner = 3'd4; winner_valid = 1'b1; end
                    8'b??100000: begin winner = 3'd5; winner_valid = 1'b1; end
                    8'b?1000000: begin winner = 3'd6; winner_valid = 1'b1; end
                    8'b10000000: begin winner = 3'd7; winner_valid = 1'b1; end
                    default:     begin winner = 3'd0; winner_valid = 1'b0; end
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
