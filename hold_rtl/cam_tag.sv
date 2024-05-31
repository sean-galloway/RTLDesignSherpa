`timescale 1ns / 1ps

module cam_tag #(
    parameter int ENABLE = 1,
    parameter int N = 8,       // Width of the TAG
    parameter int DEPTH = 16   // Number of TAG entries in the CAM
)(
    input  logic               i_clk,
    input  logic               i_rst_n,
    input  logic [N-1:0]       i_tag_in_status,
    input  logic               i_mark_valid,
    input  logic [N-1:0]       i_tag_in_valid,
    input  logic               i_mark_invalid,
    input  logic [N-1:0]       i_tag_in_invalid,
    output logic               ow_tags_empty,
    output logic               ow_tags_full,
    output logic               ow_tag_status
);

    logic [N-1:0]     r_tag_array [0:DEPTH-1]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DEPTH-1:0] r_valid;

    integer i, w_next_valid_loc, w_match_loc, w_match_invalid_loc;

    ///////////////////////////////////////////////////////////////////////////
    // Find the next open slot
    always_comb begin
        w_next_valid_loc = -1;
        for (i=DEPTH-1; i >= 0; i--)
            if (r_valid[i] == 1'b0)
                w_next_valid_loc = i;
    end

    ///////////////////////////////////////////////////////////////////////////
    // Find the index of the matching valid item
    always_comb begin
        w_match_loc = -1;  // Default value indicating 'no match'
        for (i = 0; i < DEPTH; i++)
            if (r_valid[i] == 1'b1 && i_tag_in_status == r_tag_array[i])
                w_match_loc = i;
    end

    ///////////////////////////////////////////////////////////////////////////
    // Find the index of the matching invalid item
    always_comb begin
        w_match_invalid_loc = -1;  // Default value indicating 'no match'
        for (i = 0; i < DEPTH; i++)
            if (r_valid[i] == 1'b1 && i_tag_in_invalid == r_tag_array[i])
                w_match_invalid_loc = i;
    end

    ///////////////////////////////////////////////////////////////////////////
    // Flop the valid and the tag
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_valid <= 'b0;
            for (i = 0; i < DEPTH; i++) begin
                r_tag_array[i] <= 'b0;
            end
        end else begin
            if (i_mark_valid && !ow_tags_full && ENABLE) begin
                r_tag_array[w_next_valid_loc] <= i_tag_in_valid;
                r_valid[w_next_valid_loc] <= 1'b1;
            end else if (i_mark_invalid) begin
                r_tag_array[w_match_invalid_loc] <= 'b0;
                r_valid[w_match_invalid_loc] <= 1'b0;
            end
        end
    end

    assign ow_tag_status = (w_match_loc >= 0) ? r_valid[w_match_loc] : 1'b0;
    assign ow_tags_empty = ~|r_valid;
    assign ow_tags_full  =  &r_valid;

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
