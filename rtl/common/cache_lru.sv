`timescale 1ns / 1ps

module cache_lru #(
    parameter int DEPTH = 64,       // Total number of cache lines
    parameter int A = 4,            // Associativity (number of ways)
    parameter int DW = 32,          // Data width in bits
    parameter int AW = 32,          // Address width in bits
    parameter int LINE_SIZE = DW/8, // Line size in bytes
    parameter int LRU_WIDTH = 3     // Width of LRU counter (log2(A) in most cases)
)(
    input  logic                 i_clk,
    input  logic                 i_rst_n,
    // Read/Writ ports
    input  logic [AW-1:0]        i_rd_addr, // Read address
    input  logic                 i_rd,      // Read request
    input  logic [AW-1:0]        i_wr_addr, // Write address
    input  logic                 i_wr,      // Write request
    input  logic [DW-1:0]        i_wr_data, // Write data
    input  logic [LINE_SIZE-1:0] i_wr_dm,   // Write data mask (byte enables)
    output logic [DW-1:0]        o_rd_data, // Read data
    output logic                 o_rd_hit,  // Read hit/miss
    output logic                 o_wr_hit,  // Write hit/miss

    // Snoop port
    input  logic [AW-1:0]        i_snoop_addr,  // Snooped address
    input  logic                 i_snoop_valid, // Valid snoop request
    input  logic [3:0]           i_snoop_cmd,   // Snoop command (e.g., read, write, invalidate)
    output logic                 o_snoop_hit,   // Snoop hit/miss
    output logic                 o_snoop_dirty, // Snooped data is dirty
    output logic [DW-1:0]        o_snoop_data   // Snooped data
);

    localparam int S = 2**$clog2(DEPTH/A);
    localparam int TagWidth = AW - $clog2(DEPTH) - $clog2(LINE_SIZE);
    localparam int IndexWidth = $clog2(S);
    localparam int OffsetWidth = $clog2(LINE_SIZE);

    logic [TagWidth-1:0]  r_tag_array [0:DEPTH-1];   // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DW-1:0] r_data_array [0:DEPTH-1][0:A-1];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DEPTH-1:0]     r_valid_array;
    logic [DEPTH-1:0]     r_dirty_array;
    logic [LRU_WIDTH-1:0] r_lru_bits [0:S-1][0:A-1]; // verilog_lint: waive unpacked-dimensions-range-ordering

    wire [TagWidth-1:0]    w_rd_tag;
    wire [IndexWidth-1:0]  w_rd_index;
    wire [OffsetWidth-1:0] w_rd_offset;

    wire [TagWidth-1:0]    w_wr_tag;
    wire [IndexWidth-1:0]  w_wr_index;
    wire [OffsetWidth-1:0] w_wr_offset;

    assign w_rd_tag = i_rd_addr[AW-1:AW-TagWidth];
    assign w_rd_index = i_rd_addr[AW-TagWidth-1:AW-TagWidth-IndexWidth];
    assign w_rd_offset = i_rd_addr[AW-TagWidth-IndexWidth-1:AW-TagWidth-IndexWidth-OffsetWidth];

    assign w_wr_tag = i_wr_addr[AW-1:AW-TagWidth];
    assign w_wr_index = i_wr_addr[AW-TagWidth-1:AW-TagWidth-IndexWidth];
    assign w_wr_offset = i_wr_addr[AW-TagWidth-IndexWidth-1:AW-TagWidth-IndexWidth-OffsetWidth];

    wire [A-1:0] w_rd_way_hit;
    wire [A-1:0] w_wr_way_hit;
    assign       o_rd_hit = |w_rd_way_hit;
    assign       o_wr_hit = |w_wr_way_hit;

    genvar i;
    generate
        for (i = 0; i < A; i = i + 1) begin : gen_way_hit
            assign w_rd_way_hit[i] = r_valid_array[w_rd_index*A+i] && (r_tag_array[w_rd_index*A+i] == w_rd_tag);
            assign w_wr_way_hit[i] = r_valid_array[w_wr_index*A+i] && (r_tag_array[w_wr_index*A+i] == w_wr_tag);
        end
    endgenerate

    integer j;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (~i_rst_n) begin
            for (j = 0; j < DEPTH; j = j + 1) begin
                r_valid_array[j] <= 1'b0;
                r_dirty_array[j] <= 1'b0;
                r_tag_array[j] <= {TagWidth{1'b0}};
            end
            for (j = 0; j < S; j = j + 1) begin
                for (int k = 0; k < A; k++) begin
                    r_lru_bits[j][k] <= 0;
                end
            end
        end else begin
// Handle snoop requests
            if (i_snoop_valid) begin
                logic [IndexWidth-1:0] snoop_index;
                logic [TagWidth-1:0] snoop_tag;
                assign snoop_index = i_snoop_addr[AW-TagWidth-1:AW-TagWidth-IndexWidth];
                assign snoop_tag = i_snoop_addr[AW-1:AW-TagWidth];

                o_snoop_hit = 1'b0;
                o_snoop_dirty = 1'b0;
                o_snoop_data = {DW{1'b0}};

                case (i_snoop_cmd)
                    4'b0000: begin // Snoop read
                        for (j = 0; j < A; j = j + 1) begin
                            if (r_valid_array[snoop_index*A+j] && (r_tag_array[snoop_index*A+j] == snoop_tag)) begin
                                o_snoop_hit = 1'b1;
                                o_snoop_data = r_data_array[snoop_index][j];
                                o_snoop_dirty = r_dirty_array[snoop_index*A+j];
                                // Update LRU bits for the hit way
                                r_lru_bits[snoop_index][j] = {LRU_WIDTH{1'b1}};
                                for (int k = 0; k < A; k++) begin
                                    if (k != j) begin
                                        r_lru_bits[snoop_index][k] <= (r_lru_bits[snoop_index][k] == {LRU_WIDTH{1'b1}}) ? r_lru_bits[snoop_index][k] : r_lru_bits[snoop_index][k] + 1;
                                    end
                                end
                            end
                        end
                    end
                    4'b0001: begin // Snoop read for ownership (RFO)
                        o_snoop_hit = 1'b0;
                        o_snoop_dirty = 1'b0;
                        o_snoop_data = {DW{1'b0}};
                        for (j = 0; j < A; j = j + 1) begin
                            if (r_valid_array[snoop_index*A+j] && (r_tag_array[snoop_index*A+j] == snoop_tag)) begin
                                o_snoop_hit = 1'b1;
                                o_snoop_data = r_data_array[snoop_index][j];
                                o_snoop_dirty = r_dirty_array[snoop_index*A+j];
                                // Invalidate the cache line
                                r_valid_array[snoop_index*A+j] <= 1'b0;
                                // Update LRU bits for the invalidated way
                                r_lru_bits[snoop_index][j] = {LRU_WIDTH{1'b1}};
                                for (int k = 0; k < A; k++) begin
                                    if (k != j) begin
                                        r_lru_bits[snoop_index][k] <= (r_lru_bits[snoop_index][k] == {LRU_WIDTH{1'b1}}) ? r_lru_bits[snoop_index][k] : r_lru_bits[snoop_index][k] + 1;
                                    end
                                end
                            end
                        end
                    end
                    4'b0010: begin // Snoop invalidate
                        for (j = 0; j < A; j = j + 1) begin
                            if (r_valid_array[snoop_index*A+j] && (r_tag_array[snoop_index*A+j] == snoop_tag)) begin
                                // Invalidate the cache line
                                r_valid_array[snoop_index*A+j] <= 1'b0;
                                // Update LRU bits for the invalidated way
                                r_lru_bits[snoop_index][j] = {LRU_WIDTH{1'b1}};
                                for (int k = 0; k < A; k++) begin
                                    if (k != j) begin
                                        r_lru_bits[snoop_index][k] <= (r_lru_bits[snoop_index][k] == {LRU_WIDTH{1'b1}}) ? r_lru_bits[snoop_index][k] : r_lru_bits[snoop_index][k] + 1;
                                    end
                                end
                            end
                        end
                    end
                    4'b0011: begin // Snoop write back (WB)
                        // Handle write back operation
                        // Update main memory or higher-level cache with the dirty data
                        // ...
                    end
                    4'b0100: begin // Snoop intervention
                        // Handle intervention operation
                        // Provide the requested data directly to the requesting cache
                        // ...
                    end
                    default: begin
                        // signals are already forced to 0's
                    end
                endcase
            end

            // Handle read operations
            if (i_rd) begin
                if (o_rd_hit) begin
                    for (j = 0; j < A; j = j + 1) begin
                        if (w_rd_way_hit[j]) begin
                            o_rd_data <= r_data_array[w_rd_index][j][DW-1:DW-LINE_SIZE*8];
                            o_rd_data[LINE_SIZE*8-1:0] <= r_data_array[w_rd_index][j][LINE_SIZE*8-1:0] >> {w_rd_offset, {OffsetWidth{1'b0}}};
                            r_lru_bits[w_rd_index][j] <= 0;
                        end else begin
                            r_lru_bits[w_rd_index][j] <= (r_lru_bits[w_rd_index][j] == {LRU_WIDTH{1'b1}}) ? r_lru_bits[w_rd_index][j] : r_lru_bits[w_rd_index][j] + 1;
                        end
                    end
                end else begin
                    logic [A-1:0] w_empty_way;
                    w_empty_way = ~r_valid_array[w_rd_index*A +: A];

                    for (j = 0; j < A; j = j + 1) begin
                        if (w_empty_way[j]) begin
                            r_data_array[w_rd_index][j] <= {DW{1'b0}};
                            r_tag_array[w_rd_index*A+j] <= w_rd_tag;
                            r_valid_array[w_rd_index*A+j] <= 1'b1;
                            r_dirty_array[w_rd_index*A+j] <= 1'b0;
                            r_lru_bits[w_rd_index][j] <= 0;
                        end else begin
                            r_lru_bits[w_rd_index][j] <= (r_lru_bits[w_rd_index][j] == {LRU_WIDTH{1'b1}}) ? r_lru_bits[w_rd_index][j] : r_lru_bits[w_rd_index][j] + 1;
                        end
                    end

                    if (w_empty_way == {A{1'b0}}) begin
                        logic [LRU_WIDTH-1:0] w_lru_way;
                        w_lru_way = r_lru_bits[w_rd_index][0];
                        for (j = 1; j < A; j = j + 1) begin
                            w_lru_way = (w_lru_way > r_lru_bits[w_rd_index][j]) ? w_lru_way : r_lru_bits[w_rd_index][j];
                        end

                        for (j = 0; j < A; j = j + 1) begin
                            if (r_lru_bits[w_rd_index][j] == w_lru_way) begin
                                r_data_array[w_rd_index][j] <= {DW{1'b0}};
                                r_tag_array[w_rd_index*A+j] <= w_rd_tag;
                                r_valid_array[w_rd_index*A+j] <= 1'b1;
                                r_dirty_array[w_rd_index*A+j] <= 1'b0;
                                r_lru_bits[w_rd_index][j] <= 0;
                            end else begin
                                r_lru_bits[w_rd_index][j] <= 0;
                            end
                        end
                    end

                    o_rd_data <= {DW{1'b0}};
                end
            end

            // Handle write operations
            if (i_wr) begin
                logic w_found;
                w_found = 1'b0;

                if (o_wr_hit) begin
                    for (j = 0; j < A; j = j + 1) begin
                        if (w_wr_way_hit[j]) begin
                            r_data_array[w_wr_index][j][DW-1:DW-LINE_SIZE*8] <= r_data_array[w_wr_index][j][DW-1:DW-LINE_SIZE*8];
                            r_data_array[w_wr_index][j][LINE_SIZE*8-1:0] <= (r_data_array[w_wr_index][j][LINE_SIZE*8-1:0] & ~({{LINE_SIZE*8-OffsetWidth{1'b1}}, {OffsetWidth{1'b0}}} << w_wr_offset)) |
                                                                              ((i_wr_data << {w_wr_offset, {OffsetWidth{1'b0}}}) & ({{LINE_SIZE{i_wr_dm}}, {LINE_SIZE*8-LINE_SIZE{1'b0}}}));
                            r_dirty_array[w_wr_index*A+j] <= 1'b1;
                            r_lru_bits[w_wr_index][j] <= 0;
                        end else begin
                            r_lru_bits[w_wr_index][j] <= (r_lru_bits[w_wr_index][j] == {LRU_WIDTH{1'b1}}) ? r_lru_bits[w_wr_index][j] : r_lru_bits[w_wr_index][j] + 1;
                        end
                    end
                end else begin
                    logic [A-1:0] w_empty_way;
                    w_empty_way = ~r_valid_array[w_wr_index*A +: A];

                    for (j = 0; j < A; j = j + 1) begin
                        if (w_empty_way[j] && !w_found) begin
                            r_data_array[w_wr_index][j] <= (i_wr_data << {w_wr_offset, {OffsetWidth{1'b0}}}) & ({{LINE_SIZE{i_wr_dm}}, {LINE_SIZE*8-LINE_SIZE{1'b0}}});
                            r_tag_array[w_wr_index*A+j] <= w_wr_tag;
                            r_valid_array[w_wr_index*A+j] <= 1'b1;
                            r_dirty_array[w_wr_index*A+j] <= 1'b1;
                            r_lru_bits[w_wr_index][j] <= 0;
                            w_found = 1'b1;
                        end else if (!w_found) begin
                            r_lru_bits[w_wr_index][j] <= (r_lru_bits[w_wr_index][j] == {LRU_WIDTH{1'b1}}) ? r_lru_bits[w_wr_index][j] : r_lru_bits[w_wr_index][j] + 1;
                        end
                    end

                    if (!w_found) begin
                        logic [LRU_WIDTH-1:0] w_lru_way;
                        w_lru_way = r_lru_bits[w_wr_index][0];
                        for (j = 1; j < A; j = j + 1) begin
                            w_lru_way = (w_lru_way > r_lru_bits[w_wr_index][j]) ? w_lru_way : r_lru_bits[w_wr_index][j];
                        end

                        for (j = 0; j < A; j = j + 1) begin
                            if (r_lru_bits[w_wr_index][j] == w_lru_way) begin
                                r_data_array[w_wr_index][j] <= (i_wr_data << {w_wr_offset, {OffsetWidth{1'b0}}}) & ({{LINE_SIZE{i_wr_dm}}, {LINE_SIZE*8-LINE_SIZE{1'b0}}});
                                r_tag_array[w_wr_index*A+j] <= w_wr_tag;
                                r_valid_array[w_wr_index*A+j] <= 1'b1;
                                r_dirty_array[w_wr_index*A+j] <= 1'b1;
                                r_lru_bits[w_wr_index][j] <= 0;
                            end else begin
                                r_lru_bits[w_wr_index][j] <= 0;
                            end
                        end
                    end
                end
            end
        end
    end

    // logic [(TagWidth*DEPTH)-1:0] flat_r_tag_array;
    // genvar gen_i;
    // generate
    //     for (gen_i = 0; gen_i < DEPTH; gen_i++) begin : gen_flatten_tag_array
    //         assign flat_r_tag_array[gen_i*TagWidth+:TagWidth] = r_tag_array[gen_i];
    //     end
    // endgenerate

endmodule : cache_lru