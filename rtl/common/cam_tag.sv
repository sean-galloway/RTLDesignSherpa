`timescale 1ns / 1ps

module cam_tag #(
    parameter int ENABLE = 1,
    parameter int N = 8,       // Width of the TAG
    parameter int DEPTH = 16   // Number of TAG entries in the CAM
)(
    input  logic               clk,
    input  logic               rst_n,
    input  logic [N-1:0]       tag_in_status,
    input  logic               mark_valid,
    input  logic [N-1:0]       tag_in_valid,
    input  logic               mark_invalid,
    input  logic [N-1:0]       tag_in_invalid,
    output logic               tags_empty,
    output logic               tags_full,
    output logic               tag_status
);

    logic [N-1:0]     r_tag_array [0:DEPTH-1]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DEPTH-1:0] r_valid;

    integer w_next_valid_loc, w_match_loc, w_match_invalid_loc;

    ///////////////////////////////////////////////////////////////////////////
    // Find the next open slot
    always_comb begin
        w_next_valid_loc = -1;
        for (int i=DEPTH-1; i >= 0; i--)
            if (r_valid[i] == 1'b0)
                w_next_valid_loc = i;
    end

    ///////////////////////////////////////////////////////////////////////////
    // Find the index of the matching valid item
    always_comb begin
        w_match_loc = -1;  // Default value indicating 'no match'
        for (int i = 0; i < DEPTH; i++)
            if (r_valid[i] == 1'b1 && tag_in_status == r_tag_array[i])
                w_match_loc = i;
    end

    ///////////////////////////////////////////////////////////////////////////
    // Find the index of the matching invalid item
    always_comb begin
        w_match_invalid_loc = -1;  // Default value indicating 'no match'
        for (int i = 0; i < DEPTH; i++)
            if (r_valid[i] == 1'b1 && tag_in_invalid == r_tag_array[i])
                w_match_invalid_loc = i;
    end

    ///////////////////////////////////////////////////////////////////////////
    // Flop the valid and the tag
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_valid <= 'b0;
            for (int i = 0; i < DEPTH; i++) begin
                r_tag_array[i] <= 'b0;
            end
        end else begin
            if (mark_valid && !tags_full && (ENABLE != 0)) begin
                r_tag_array[w_next_valid_loc] <= tag_in_valid;
                r_valid[w_next_valid_loc] <= 1'b1;
            end else if (mark_invalid && w_match_invalid_loc >= 0) begin
                r_tag_array[w_match_invalid_loc] <= 'b0;
                r_valid[w_match_invalid_loc] <= 1'b0;
            end
        end
    end

    assign tag_status = (w_match_loc >= 0) ? r_valid[w_match_loc] : 1'b0;
    assign tags_empty = ~|r_valid;
    assign tags_full  =  &r_valid;

    /////////////////////////////////////////////////////////////////////////
    // error checking
    // synopsys translate_off
    // Generate a version of the tag array for waveforms
    logic [(N*DEPTH)-1:0] flat_r_tag_array;
    genvar j;
    generate
        for (j = 0; j < DEPTH; j++) begin : gen_flatten_memory
            assign flat_r_tag_array[j*N+:N] = r_tag_array[j];
        end
    endgenerate
    // synopsys translate_on

endmodule : cam_tag
