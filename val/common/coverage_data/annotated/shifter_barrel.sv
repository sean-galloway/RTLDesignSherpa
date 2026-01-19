//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: shifter_barrel
        // Purpose: Shifter Barrel module
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        module shifter_barrel #(
            parameter int WIDTH = 8
        ) (
%000000     input  logic         [WIDTH-1:0] data,          // Input data
%000000     input  logic               [2:0] ctrl,          // Control signal (3-bit)
                                                              // 000 No shift
                                                              // 001 Logical Right Shift (no wrap)
                                                              // 010 Arithmetic Right Shift
                                                              // 011 Logical Right Shift (wrap)
                                                              // 100 Logical Left Shift (no wrap)
                                                              // 110 Logical Left Shift (wrap)
%000000     input  logic [($clog2(WIDTH)):0] shift_amount,  // Shift amount (number of positions to shift)
%000000     output logic         [WIDTH-1:0] data_out      // Output data
        );
        
            // Internal shift unrolled lookup arrays
%000000     logic [WIDTH-1:0] w_array_rs[WIDTH];  // Right shift (wrap)
%000000     logic [WIDTH-1:0] w_array_ls[WIDTH];  // Left shift (wrap)
        
            // Concatenate input for wrapping purposes
%000000     logic [WIDTH*2-1:0] w_data_double;
            assign w_data_double = {data, data};
        
            // Clamp shift amount modulo WIDTH
%000000     logic [$clog2(WIDTH)-1:0] shift_amount_mod;
            assign shift_amount_mod = shift_amount[$clog2(WIDTH)-1:0];
        
            // Generate lookup values for rotating shifts
            genvar i;
            generate
                for (i = 0; i < WIDTH; i++) begin : gen_unrolled_shifts
                    assign w_array_rs[i] = w_data_double[WIDTH-1+i:i];
                    assign w_array_ls[i] = w_data_double[WIDTH*2-1-i:WIDTH-i];
                end
            endgenerate
        
            // Main shifter logic
 000122     always_comb begin
 000122         case (ctrl)
%000000             3'b000: // No shift
%000000                 data_out = data;
        
 000061             3'b001: // Logical Right Shift (no wrap)
 000061                 data_out = (shift_amount_mod == 0) ? data : data >> shift_amount;
        
%000000             3'b010: // Arithmetic Right Shift (preserve sign)
%000000                 data_out = $signed(data) >>> shift_amount_mod;
        
%000000             3'b011: // Logical Right Shift with wrap
%000000                 data_out = w_array_rs[shift_amount_mod];
        
 000061             3'b100: // Logical Left Shift (no wrap)
 000061                 data_out = (shift_amount_mod == 0) ? data : data << shift_amount;
        
%000000             3'b110: // Logical Left Shift with wrap
%000000                 data_out = w_array_ls[shift_amount_mod];
        
%000000             default:
%000000                 data_out = data;
                endcase
            end
        
        endmodule : shifter_barrel
        
