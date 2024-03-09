`timescale 1ns / 1ps

module buffer_blocking_reorder #(
    parameter int TAG_WIDTH = 8,    // Width of the TAG
    parameter int ADDR_WIDTH = 16,  // Address Width
    parameter int DATA_WIDTH = 16,  // Data Width
    parameter int COUNT_WIDTH = 3,  // width of the counter to see how long to stay on one entry
    parameter int TIMER_WIDTH = 4,  // Timer Width
    parameter int DEPTH = 16        // Number of TAG entries in the CAM
)(
    input  logic                   i_clk,
    input  logic                   i_rst_n,
    input  logic                   i_pkt_put,
    input  logic [TAG_WIDTH-1:0]   i_pkt_tag,
    input  logic [ADDR_WIDTH-1:0]  i_pkt_addr,
    input  logic [DATA_WIDTH-1:0]  i_pkt_data,
    input  logic [COUNT_WIDTH-1:0] i_pkt_count,
    output logic                   ow_pkt_empty,
    output logic                   ow_pkt_full,
    output logic                   ow_pkt_valid,
    input  logic                   i_pkt_ready,
    output logic [TAG_WIDTH-1:0]   o_pkt_tag,
    output logic [ADDR_WIDTH-1:0]  o_pkt_addr,
    output logic [DATA_WIDTH-1:0]  o_pkt_data,
    output logic [COUNT_WIDTH-1:0] o_pkt_count,
    output logic                   o_pkt_last
);

    localparam  int TW = TAG_WIDTH;
    localparam  int AW = ADDR_WIDTH;
    localparam  int DW = DATA_WIDTH;
    localparam  int CW = COUNT_WIDTH;
    localparam  int TM = TIMER_WIDTH;

    // Define FSM states with one-hot encoding
    typedef enum logic [3:0] {
        IDLE =    4'b0001,
        BLOCKED = 4'b0010,
        WAIT =    4'b0100,
        IP =      4'b1000
    } state_t;

    state_t  r_state_array  [0:DEPTH-1]; // verilog_lint: waive unpacked-dimensions-range-ordering

    logic [AW-1:0] r_addr_array    [0:DEPTH-1]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DW-1:0] r_data_array    [0:DEPTH-1]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [TW-1:0] r_tag_array     [0:DEPTH-1]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [CW-1:0] r_count_array   [0:DEPTH-1]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [TM-1:0] r_timer_array   [0:DEPTH-1]; // verilog_lint: waive unpacked-dimensions-range-ordering

    integer idx;
    logic [$clog2(DEPTH):0] w_first_idle_index;
    logic w_found_idle, w_found_tag_to_block;

    ///////////////////////////////////////////////////////////////////////////
    // Find the first IDLE entry
    always_comb begin
        w_found_idle = 1'b0;
        w_first_idle_index = 'X;  // Initialize with an invalid value
        for (idx = 0; idx < DEPTH; idx++) begin
            if (r_state_array[idx] == IDLE && !w_found_idle) begin
                // Found the first IDLE state
                w_first_idle_index = idx;
                w_found_idle = 1'b1;  // Raise the flag to avoid changing index on further matches
            end
        end
    end

    ///////////////////////////////////////////////////////////////////////////
    // Find the tag that matches a valid entry to the input
    always_comb begin
        w_found_tag_to_block = 1'b0;  // Assume not found initially
        for (idx = 0; idx < DEPTH; idx++) begin
            // Check if the current state is not IDLE and the tag matches
            if ((r_state_array[idx] != IDLE) &&
                    (r_tag_array[idx] == i_pkt_tag) &&
                    (!w_found_tag_to_block)) begin
                w_found_tag_to_block = 1'b1;
            end
        end
    end

    ///////////////////////////////////////////////////////////////////////////
    // Flop the valid and the tag
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            for (int i = 0; i < DEPTH; i++) begin
                r_addr_array[i]  <= {AW{1'b0}};
                r_data_array[i]  <= {DW{1'b0}};
                r_tag_array[i]   <= {TW{1'b0}};
                r_count_array[i] <= {CW{1'b0}};
                r_timer_array[i] <= {TM{1'b1}};
                r_state_array[i] <= IDLE;
            end
        end else begin
            // put a new packet in
            if (i_pkt_put) begin
                r_addr_array[w_first_idle_index]  <= i_pkt_addr;
                r_data_array[w_first_idle_index]  <= i_pkt_data;
                r_tag_array[w_first_idle_index]   <= i_pkt_tag;
                r_count_array[w_first_idle_index] <= i_pkt_count;
                r_timer_array[w_first_idle_index] <= {TM{1'b1}};
                r_state_array[w_first_idle_index] <= (w_found_tag_to_block) ? BLOCKED: WAIT;
            end
            // Decrement the global timers
            for (idx=0; idx < DEPTH; idx++) begin
                if (r_state_array[idx] != IDLE)
                    if (idx != w_first_idle_index)
                        if (r_timer_array[idx] > 0)
                            r_timer_array[idx] <= r_timer_array[idx]-1;
            end
            if (ow_pkt_valid & i_pkt_ready) begin
                r_count_array[r_lowest_wait_index] <= r_count_array[r_lowest_wait_index] - 1;
            end
            if (w_next_arb_point) begin
                r_state_array[r_lowest_wait_index] <= IDLE;
                r_state_array[w_lowest_hold_index] <= WAIT;
            end
        end
    end

    ///////////////////////////////////////////////////////////////////////////
    // Full and Empty Flags
    logic [DEPTH-1:0] w_idle_vector;
    always_comb begin
        // Start by assuming vector is clear
        w_idle_vector = 'b0;
        // Iterate over the record array
        for (int i = 0; i < DEPTH; i++)
            if (r_state_array[i] == IDLE)
                w_idle_vector[i] = 1'b1;
    end

    ///////////////////////////////////////////////////////////////////////////
    // Find the next valid index for delivery
    logic [$clog2(DEPTH + 1)-1:0] w_lowest_wait_index; // Adjusted width to accommodate DEPTH + 1
    logic [$clog2(DEPTH + 1)-1:0] r_lowest_wait_index; // Adjusted width to accommodate DEPTH + 1
    logic [TIMER_WIDTH-1:0]       w_lowest_wait_timer;

    always_comb begin
        w_lowest_wait_index = DEPTH; // Start with DEPTH as an indicator for "no valid index"
        w_lowest_wait_timer = {TIMER_WIDTH{1'b1}}; // Max value assuming timer counts down

        for (int i = 0; i < DEPTH; i++) begin
            if (i != r_lowest_wait_index)
                if (r_state_array[i] == WAIT && r_timer_array[i] < w_lowest_wait_timer) begin
                    w_lowest_wait_index = i;
                    w_lowest_wait_timer = r_timer_array[i];
                end
        end
    end

    ///////////////////////////////////////////////////////////////////////////
    // Find a target to move from HOLD to WAIT
    logic [$clog2(DEPTH + 1)-1:0] w_lowest_hold_index; // Adjusted width to accommodate DEPTH + 1
    logic [TIMER_WIDTH-1:0]       w_lowest_hold_timer;

    always_comb begin
        w_lowest_wait_index = DEPTH; // Start with DEPTH as an indicator for "no valid index"
        w_lowest_wait_timer = {TIMER_WIDTH{1'b1}}; // Max value assuming timer counts down

        for (int i = 0; i < DEPTH; i++) begin
            if ( i != r_lowest_wait_index)
                if ((r_tag_array[i] == r_tag_array[r_lowest_wait_index]) &&
                        (r_timer_array[i] < w_lowest_wait_timer)) begin
                    w_lowest_hold_timer = r_timer_array[i];
                    w_lowest_hold_index = i;
                end
        end
    end

    ///////////////////////////////////////////////////////////////////////////
    // Flop the next valid index for delivery
    logic w_next_arb_point, w_pkt_done;
    logic r_active;
    assign w_next_arb_point = (r_active) ? w_pkt_done : 'b1;
    assign w_pkt_done = ow_pkt_valid & i_pkt_ready & o_pkt_last;

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_lowest_wait_index <= DEPTH;
            r_active <= 0;
        end else if (w_next_arb_point) begin
            if (w_lowest_wait_index < DEPTH) begin
                r_active <= 1;
                r_lowest_wait_index <= w_lowest_wait_index;
            end else begin
                r_active <= 0;
                r_lowest_wait_index <= DEPTH;
            end
        end
    end

    ///////////////////////////////////////////////////////////////////////////
    // assign the outputs
    assign ow_pkt_full  = ~|w_idle_vector;
    assign ow_pkt_empty =  &w_idle_vector;
    assign ow_pkt_valid = !ow_pkt_empty;
    assign o_pkt_tag = (r_lowest_wait_index != DEPTH) ? r_tag_array[r_lowest_wait_index] : '0;
    assign o_pkt_addr = (r_lowest_wait_index != DEPTH) ? r_addr_array[r_lowest_wait_index] : '0;
    assign o_pkt_data = (r_lowest_wait_index != DEPTH) ? r_data_array[r_lowest_wait_index] : '0;
    assign o_pkt_count = (r_lowest_wait_index != DEPTH) ? r_count_array[r_lowest_wait_index] : '0;
    assign o_pkt_last = (r_lowest_wait_index != DEPTH) ?
                            (r_count_array[r_lowest_wait_index] == 'b0) : '0;

    /////////////////////////////////////////////////////////////////////////
    // error checking
    // synopsys translate_off
    // Generate a version of the tag array for waveforms
    logic [(AW*DEPTH)-1:0] flat_r_addr_array;
    logic [(DW*DEPTH)-1:0] flat_r_data_array;
    logic [(TW*DEPTH)-1:0] flat_r_tag_array;
    logic [(8*DEPTH)-1:0]  flat_r_count_array;
    logic [(8*DEPTH)-1:0]  flat_r_timer_array;
    logic [(8*DEPTH)-1:0]  flat_r_state_array;
    genvar j;
    generate
        for (j = 0; j < DEPTH; j++) begin : gen_flatten
            assign flat_r_addr_array[j*AW+:AW] = r_addr_array[j];
            assign flat_r_data_array[j*DW+:DW] = r_data_array[j];
            assign flat_r_tag_array[j*TW+:TW] = r_tag_array[j];
            assign flat_r_count_array[j*8 +: 8] = {{(8-CW){1'b0}}, r_count_array[j]};
            assign flat_r_timer_array[j*8 +: 8] = {{(8-TM){1'b0}}, r_timer_array[j]};
            assign flat_r_state_array[j*8 +: 8] = {{4'b0000}, r_state_array[j]};
        end
    endgenerate
    // synopsys translate_on

endmodule : buffer_blocking_reorder
