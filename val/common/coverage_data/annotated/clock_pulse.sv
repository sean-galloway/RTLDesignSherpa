//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: clock_pulse
        // Purpose: Clock Pulse module
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        `include "reset_defs.svh"
        
        module clock_pulse #(
            parameter int WIDTH = 10  // Width of the generated pulse in clock cycles
        ) (
 000786     input  logic clk,    // Input clock signal
 000042     input  logic rst_n,  // Input reset signal
 000056     output logic pulse   // Output pulse signal
        );
        
%000000     logic [WIDTH-1:0] r_counter;
%000000     logic [WIDTH-1:0] w_width_minus_one;
        
            // Create a properly sized constant
            assign w_width_minus_one = WIDTH[WIDTH-1:0] - 1'b1;
        
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_counter <= 'b0;
                    pulse     <= 'b0;
                end else begin
                    if (r_counter < w_width_minus_one) r_counter <= r_counter + 1'b1;
                    else r_counter <= 'b0;
        
                    pulse <= (r_counter == w_width_minus_one);
                end
 000028     )
        
        
        endmodule : clock_pulse
        
