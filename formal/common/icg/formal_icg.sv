// SPDX-License-Identifier: MIT
// Formal wrapper for icg — minimal properties (latch-based)
module formal_icg (input logic clk, input logic en);
    logic gclk;
    icg dut (.en(en), .clk(clk), .gclk(gclk));
    
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    
    // When en is low for 2+ cycles, gclk should be low at posedge
    always @(posedge clk) begin
        if (f_past_valid > 0 && !$past(en) && !en)
            ap_disabled: assert (!gclk);
    end
    
    always @(posedge clk) begin
        cp_enabled: cover (gclk);
        cp_disabled: cover (!gclk && en);
    end
endmodule
