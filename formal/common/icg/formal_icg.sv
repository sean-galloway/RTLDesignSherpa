// SPDX-License-Identifier: MIT
// Formal wrapper for icg — latch-based clock gate
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

    // gclk = en_out && clk, where en_out latches en on negedge clk.
    // At posedge clk: gclk == en_out (since clk=1).
    // If en was high during the preceding low phase, en_out=1 and gclk=1.
    // Cover: en was high in the past (latch captured it)
    always @(posedge clk) begin
        if (f_past_valid > 0)
            cp_enabled: cover ($past(en));
    end

    always @(posedge clk) begin
        cp_disabled: cover (!gclk);
    end
endmodule
