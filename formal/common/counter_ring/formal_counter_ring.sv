// Formal wrapper for counter_ring
module formal_counter_ring (
    input logic clk,
    input logic rst_n
);

    localparam int WIDTH = 4;

    (* anyseq *) reg enable;

    wire [WIDTH-1:0] ring_out;

    counter_ring #(.WIDTH(WIDTH)) dut (
        .clk      (clk),
        .rst_n    (rst_n),
        .enable   (enable),
        .ring_out (ring_out)
    );

    // Formal infrastructure
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk)
        if (f_past_valid >= 2) assume (rst_n);

    // P1: Reset initializes to 1 (LSB set)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset: assert (ring_out == {{(WIDTH-1){1'b0}}, 1'b1});
    end

    // P2: One-hot invariant -- exactly one bit set at all times
    always @(posedge clk) begin
        if (rst_n)
            ap_onehot: assert ($onehot(ring_out));
    end

    // P3: Hold when disabled
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && !$past(enable))
            ap_hold: assert (ring_out == $past(ring_out));
    end

    // P4: Right rotation -- MSB gets LSB, others shift right
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(enable))
            ap_rotate: assert (ring_out == {$past(ring_out[0]), $past(ring_out[WIDTH-1:1])});
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_enable: cover (enable);
            cp_msb_set: cover (ring_out[WIDTH-1]);
            cp_full_rotation: cover (ring_out == {{(WIDTH-1){1'b0}}, 1'b1} && f_past_valid > 5);
        end
    end

endmodule
