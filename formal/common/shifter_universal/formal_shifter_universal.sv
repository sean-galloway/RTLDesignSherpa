// Formal wrapper for shifter_universal (4-mode: hold, right, left, load)
module formal_shifter_universal (
    input logic clk,
    input logic rst_n
);

    localparam int WIDTH = 4;

    (* anyseq *) reg [1:0]       select;
    (* anyseq *) reg [WIDTH-1:0] i_pdata;
    (* anyseq *) reg             i_sdata_lt;
    (* anyseq *) reg             i_sdata_rt;

    wire [WIDTH-1:0] o_pdata;
    wire             o_sdata_lt;
    wire             o_sdata_rt;

    shifter_universal #(.WIDTH(WIDTH)) dut (
        .clk        (clk),
        .rst_n      (rst_n),
        .select     (select),
        .i_pdata    (i_pdata),
        .i_sdata_lt (i_sdata_lt),
        .i_sdata_rt (i_sdata_rt),
        .o_pdata    (o_pdata),
        .o_sdata_lt (o_sdata_lt),
        .o_sdata_rt (o_sdata_rt)
    );

    // Formal infrastructure
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk)
        if (f_past_valid >= 2) assume (rst_n);

    // P1: Reset clears all outputs
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_pdata: assert (o_pdata == '0);
            ap_reset_slt: assert (!o_sdata_lt);
            ap_reset_srt: assert (!o_sdata_rt);
        end
    end

    // P2: Hold mode (select==00) preserves data
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(select) == 2'b00)
            ap_hold: assert (o_pdata == $past(o_pdata));
    end

    // P3: Load mode (select==11) loads parallel data
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(select) == 2'b11)
            ap_load: assert (o_pdata == $past(i_pdata));
    end

    // P4: Right shift (select==01) shifts right, serial in from MSB
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(select) == 2'b01) begin
            ap_rshift: assert (o_pdata == {$past(i_sdata_rt), $past(o_pdata[WIDTH-1:1])});
            ap_rshift_out: assert (o_sdata_rt == $past(o_pdata[0]));
        end
    end

    // P5: Left shift (select==10) shifts left, serial in from LSB
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(select) == 2'b10) begin
            ap_lshift: assert (o_pdata == {$past(o_pdata[WIDTH-2:0]), $past(i_sdata_lt)});
            ap_lshift_out: assert (o_sdata_lt == $past(o_pdata[WIDTH-1]));
        end
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_hold: cover (select == 2'b00 && o_pdata != '0);
            cp_rshift: cover (select == 2'b01);
            cp_lshift: cover (select == 2'b10);
            cp_load: cover (select == 2'b11);
            cp_nonzero: cover (o_pdata != '0);
        end
    end

endmodule
