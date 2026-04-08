// Formal wrapper for counter (basic mod-MAX counter with tick output)
module formal_counter (
    input logic clk,
    input logic rst_n
);

    localparam int MAX = 7;  // Small for tractability
    localparam int W = $clog2(MAX + 1);

    wire tick;

    counter #(.MAX(MAX)) dut (
        .clk   (clk),
        .rst_n (rst_n),
        .tick  (tick)
    );

    // Formal infrastructure
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk)
        if (f_past_valid >= 2) assume (rst_n);

    // Shadow counter to track internal state via output behavior
    reg [W-1:0] f_shadow_count;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            f_shadow_count <= 0;
        else begin
            if (f_shadow_count == MAX[W-1:0])
                f_shadow_count <= 0;
            else
                f_shadow_count <= f_shadow_count + 1;
        end
    end

    // P1: Reset clears tick
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_tick: assert (!tick);
    end

    // P2: Tick matches shadow (tick when count == MAX)
    always @(posedge clk) begin
        if (rst_n)
            ap_tick_match: assert (tick == (f_shadow_count == MAX[W-1:0]));
    end

    // P3: Tick is periodic -- cannot be asserted two consecutive cycles (MAX > 0)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(tick))
            ap_no_consecutive_tick: assert (!tick);
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_tick: cover (tick);
            cp_second_tick: cover (tick && f_past_valid > MAX + 2);
        end
    end

endmodule
