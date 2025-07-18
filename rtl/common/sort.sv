`timescale 1ns / 1ps

module sort #(
    parameter int NUM_VALS = 5,
    parameter int SIZE     = 16
) (
    input  logic                     clk,
    input  logic                     rst_n,
    input  logic [NUM_VALS*SIZE-1:0] data,
    input  logic                     valid_in,    // Start sorting when asserted
    output logic [NUM_VALS*SIZE-1:0] sorted,
    output logic                     done
);

    // Calculate number of pipeline stages needed
    // For odd-even sort: NUM_VALS stages gives us enough passes
    localparam int STAGES = NUM_VALS;

    // Pipeline registers for data (flopped signals start with r_)
    logic [NUM_VALS*SIZE-1:0] r_stage_data [1:STAGES];
    logic r_stage_valid [1:STAGES];

    // Wire signals for combinational logic (wires start with w_)
    logic [SIZE-1:0] w_values [0:STAGES][0:NUM_VALS-1];
    logic [SIZE-1:0] w_next_values [1:STAGES][0:NUM_VALS-1];

    // Input stage wires (not registered)
    logic [NUM_VALS*SIZE-1:0] w_stage_data_0;
    logic w_stage_valid_0;

    // Input stage assignments
    assign w_stage_data_0 = data;
    assign w_stage_valid_0 = valid_in;

    // Unpack input into wire arrays
    generate
        for (genvar i = 0; i < NUM_VALS; i++) begin : unpack_input
            assign w_values[0][i] = w_stage_data_0[i*SIZE +: SIZE];
        end
    endgenerate

    // Unpack pipeline stage data into wire arrays
    generate
        for (genvar stage = 1; stage <= STAGES; stage++) begin : unpack_stages
            for (genvar i = 0; i < NUM_VALS; i++) begin : unpack_stage_data
                assign w_values[stage][i] = r_stage_data[stage][i*SIZE +: SIZE];
            end
        end
    endgenerate

    // Pipeline stages implementing odd-even sort
    generate
        for (genvar stage = 1; stage <= STAGES; stage++) begin : pipeline_stages

            // Determine if this is an odd or even pass
            localparam bit IS_ODD_PASS = ((stage-1) % 2) == 0;

            // Combinational logic for compare-and-swap (wires)
            always_comb begin
                // Default: pass through values unchanged
                for (int i = 0; i < NUM_VALS; i++) begin
                    w_next_values[stage][i] = w_values[stage-1][i];
                end

                // Perform compare-and-swap operations
                if (IS_ODD_PASS) begin
                    // Odd pass: compare (0,1), (2,3), (4,5), etc.
                    for (int i = 0; i < NUM_VALS-1; i += 2) begin
                        if (w_values[stage-1][i] < w_values[stage-1][i+1]) begin
                            w_next_values[stage][i]   = w_values[stage-1][i+1];
                            w_next_values[stage][i+1] = w_values[stage-1][i];
                        end
                    end
                end else begin
                    // Even pass: compare (1,2), (3,4), (5,6), etc.
                    for (int i = 1; i < NUM_VALS-1; i += 2) begin
                        if (w_values[stage-1][i] < w_values[stage-1][i+1]) begin
                            w_next_values[stage][i]   = w_values[stage-1][i+1];
                            w_next_values[stage][i+1] = w_values[stage-1][i];
                        end
                    end
                end
            end

            // Flop the results (r_ registers)
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    r_stage_data[stage] <= '0;
                    r_stage_valid[stage] <= 1'b0;
                end else begin
                    // Propagate valid signal
                    if (stage == 1) begin
                        r_stage_valid[stage] <= w_stage_valid_0;
                    end else begin
                        r_stage_valid[stage] <= r_stage_valid[stage-1];
                    end

                    // Pack sorted values back to data bus
                    for (int i = 0; i < NUM_VALS; i++) begin
                        r_stage_data[stage][i*SIZE +: SIZE] <= w_next_values[stage][i];
                    end
                end
            end
        end
    endgenerate

    // Output assignments
    assign sorted = r_stage_data[STAGES];
    assign done = r_stage_valid[STAGES];

endmodule
