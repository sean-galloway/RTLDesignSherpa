// Formal wrapper for sync_pulse
// Single-clock model: i_src_clk = i_dst_clk = clk (verifies logic, not CDC timing)
module formal_sync_pulse (
    input logic clk,
    input logic rst_n
);

    localparam int SYNC_STAGES = 2;  // Minimum for tractability

    (* anyseq *) reg i_pulse;

    wire o_pulse;

    sync_pulse #(.SYNC_STAGES(SYNC_STAGES)) dut (
        .i_src_clk   (clk),
        .i_src_rst_n (rst_n),
        .i_pulse     (i_pulse),
        .i_dst_clk   (clk),
        .i_dst_rst_n (rst_n),
        .o_pulse     (o_pulse)
    );

    // Formal infrastructure
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk)
        if (f_past_valid >= 2) assume (rst_n);

    // Constrain input pulse to single-cycle (as required by spec)
    always @(posedge clk)
        if (rst_n && f_past_valid > 0 && $past(rst_n) && $past(i_pulse))
            assume (!i_pulse);

    // P1: Reset clears output
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset: assert (!o_pulse);
    end

    // P2: Output pulse is single-cycle (no two consecutive output pulses)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(o_pulse))
            ap_single_cycle: assert (!o_pulse);
    end

    // P3: No output pulse without prior input pulse
    // Track toggle count: each input pulse causes exactly one toggle
    reg [7:0] f_input_count;
    reg [7:0] f_output_count;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            f_input_count <= 0;
            f_output_count <= 0;
        end else begin
            if (i_pulse) f_input_count <= f_input_count + 1;
            if (o_pulse) f_output_count <= f_output_count + 1;
        end
    end

    // Output count never exceeds input count (no spurious pulses)
    always @(posedge clk) begin
        if (rst_n)
            ap_no_spurious: assert (f_output_count <= f_input_count);
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_output_pulse: cover (o_pulse);
            cp_input_pulse: cover (i_pulse);
            cp_second_output: cover (f_output_count >= 2);
        end
    end

endmodule
