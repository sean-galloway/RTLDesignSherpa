// Formal wrapper for clock_pulse (periodic pulse generator)
module formal_clock_pulse (
    input logic clk,
    input logic rst_n
);

    localparam int WIDTH = 4;  // Period = 4 cycles for tractability

    wire pulse;

    clock_pulse #(.WIDTH(WIDTH)) dut (
        .clk   (clk),
        .rst_n (rst_n),
        .pulse (pulse)
    );

    // Formal infrastructure
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk)
        if (f_past_valid >= 2) assume (rst_n);

    // Shadow counter to track periodicity
    reg [WIDTH-1:0] f_counter;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            f_counter <= 0;
        else begin
            if (f_counter < WIDTH[WIDTH-1:0] - 1)
                f_counter <= f_counter + 1;
            else
                f_counter <= 0;
        end
    end

    // P1: Reset clears pulse
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset: assert (!pulse);
    end

    // P2: Pulse matches shadow (pulse when counter == WIDTH-1)
    always @(posedge clk) begin
        if (rst_n && f_past_valid > 1)
            ap_pulse_match: assert (pulse == (f_counter == 0 && $past(f_counter) == WIDTH[WIDTH-1:0] - 1));
    end

    // P3: Pulse is periodic -- exactly 1 cycle out of every WIDTH cycles
    // No two consecutive pulses
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(pulse))
            ap_no_consecutive: assert (!pulse);
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_pulse: cover (pulse);
            cp_second_pulse: cover (pulse && f_past_valid > WIDTH + 2);
        end
    end

endmodule
