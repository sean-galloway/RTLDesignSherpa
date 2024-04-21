`timescale 1ns / 1ps

module cache_plru_mesi #(
    parameter int DEPTH = 64,       // Total number of cache lines
    parameter int A = 4,            // Associativity (number of ways)
    parameter int DW = 32,          // Data width in bits
    parameter int AW = 32,          // Address width in bits
    parameter int DM = DW/8,        // Number of byte enables
    parameter int LINE_SIZE = DW/8  // Line size in bytes
)(
    input  logic                 i_clk,
    input  logic                 i_rst_n,

    // sysbus Input; the main reads and writes occur here
    input  logic                 i_sysbusin_valid,     // sysbus input transfer valid
    output logic                 o_sysbusin_ready,     // sysbus input transfer ready
    input  logic                 i_sysbusin_op_rdxwr,  // sysbus input transfer operation
    input  logic [AW-1:0]        i_sysbusin_addr,      // sysbus input transfer address
    input  logic [DW-1:0]        i_sysbusin_data,      // sysbus input transfer data
    input  logic [DM-1:0]        i_sysbusin_dm,        // sysbus input transfer dm

    // sysbus output for return read return data
    output logic                 o_sysbusout_valid,    // sysbus output transfer valid
    input  logic                 i_sysbusout_ready,    // sysbus output transfer ready
    output logic                 o_sysbusin_op_rdxwr,  // sysbus output transfer operation
    output logic [AW-1:0]        o_sysbusout_addr,     // sysbus output transfer address
    output logic [DW-1:0]        o_sysbusout_data,     // sysbus output transfer data
    output logic [DM-1:0]        o_sysbusout_dm,       // sysbus output transfer dm

    // Memory Input; when a read is issued to the memory sub-system, it comes back here
    input  logic                 i_memin_valid,     // memory input transfer valid
    output logic                 o_memin_ready,     // memory input transfer ready
    input  logic                 i_memin_op_rdxwr,  // memory input transfer operation
    input  logic [AW-1:0]        i_memin_addr,      // memory input transfer address
    input  logic [DW-1:0]        i_memin_data,      // memory input transfer data
    input  logic [DM-1:0]        i_memin_dm,        // memory input transfer dm

    // Memory output; for getting the read data or for evicting dirty entries
    output logic                 o_memout_valid,    // memory output transfer valid
    input  logic                 i_memout_ready,    // memory output transfer ready
    output logic                 o_memin_op_rdxwr,  // memory output transfer operation
    output logic [AW-1:0]        o_memout_addr,     // memory output transfer address
    output logic [DW-1:0]        o_memout_data,     // memory output transfer data
    output logic [DM-1:0]        o_memout_dm,       // memory output transfer dm

    output logic                 o_sysbusin_hit,

    // Snoop port
    input  logic                 i_snoop_valid, // Valid snoop request
    output logic                 i_snoop_ready, // snoop transfer ready
    input  logic [AW-1:0]        i_snoop_addr,  // Snooped address
    input  logic [3:0]           i_snoop_cmd,   // Snoop command (e.g., read, write, invalidate)

    output logic                 o_snoop_hit,   // Snoop hit/miss
    output logic                 o_snoop_dirty, // Snooped data is dirty
    output logic [DW-1:0]        o_snoop_data,  // Snooped data

    // Cache-to-cache Snoop transfer
    output logic                 o_c2c_snp_valid, // Cache-to-cache transfer valid
    input  logic                 i_c2c_snp_ready, // Cache-to-cache transfer ready
    output logic [AW-1:0]        o_c2c_snp_addr,  // Cache-to-cache transfer address
    output logic [DW-1:0]        o_c2c_snp_data,  // Cache-to-cache transfer data
    output logic [DM-1:0]        o_c2c_snp_dm     // Cache-to-cache transfer dm
);

    localparam int S = 2**$clog2(DEPTH/A);
    localparam int TagWidth = AW - $clog2(DEPTH) - $clog2(LINE_SIZE);
    localparam int IndexWidth = $clog2(S);
    localparam int OffsetWidth = $clog2(LINE_SIZE);

    // Add new States for MESI protocol
    localparam int StateM = 2'b00; // Modified
    localparam int StateE = 2'b01; // Exclusive
    localparam int StateS = 2'b10; // Shared
    localparam int StateI = 2'b11; // Invalid

    // Add invalidation command
    localparam int CmdSnpRead = 4'b0000;
    localparam int CmdSnpRfo  = 4'b0001;
    localparam int CmdSnpInv  = 4'b0010;

    function automatic logic [$clog2(A)-1:0] get_plru_way(logic [A-2:0] plru_bits);
        logic [$clog2(A)-1:0] way = {($clog2(A)){1'b0}};  // Explicitly sized zero
        logic [A-2:0] local_plru_bits = plru_bits;        // Use a local copy to modify

        for (int i = $clog2(A) - 1; i >= 0; i--) begin
            int index = A - 2 - i;
            way[i] = local_plru_bits[index];
            if (way[i] == 1'b0) begin
                local_plru_bits[index] = 1'b1;
            end else begin
                local_plru_bits[index] = 1'b0;
            end
        end

        return way;
    endfunction

    function automatic logic [A-2:0] update_plru(logic [A-2:0] plru_bits, logic [$clog2(A)-1:0] accessed_way);
        // Create a temporary copy of the PLRU bits
        logic [A-2:0] updated_plru_bits = plru_bits;

        // Traverse the binary tree based on the accessed way
        for (int i = $clog2(A) - 1; i >= 0; i--) begin
            if (accessed_way[i] == 1'b0) begin
                // Update the PLRU bit to point to the right subtree
                updated_plru_bits[A - 2 - $unsigned(i)] = 1'b1;
            end else begin
                // Update the PLRU bit to point to the left subtree
                updated_plru_bits[A - 2 - $unsigned(i)] = 1'b0;
            end
        end
        return updated_plru_bits;
    endfunction

    logic [TagWidth-1:0]  r_tag_array [0:DEPTH-1];          // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DW-1:0]        r_data_array [0:DEPTH-1][0:A-1];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DM-1:0]        r_dm_array [0:DEPTH-1][0:A-1];    // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DEPTH-1:0]     r_valid_array [0:A-1];            // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DEPTH-1:0]     r_dirty_array [0:A-1];            // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [A-2:0]         r_plru_bits [0:S-1];              // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [1:0]           r_state_array [0:DEPTH-1][0:A-1]; // verilog_lint: waive unpacked-dimensions-range-ordering

    wire [TagWidth-1:0]    w_sysbusin_tag;
    wire [IndexWidth-1:0]  w_sysbusin_index;
    wire [OffsetWidth-1:0] w_sysbusin_offset;
    wire [TagWidth-1:0]    w_memin_tag;
    wire [IndexWidth-1:0]  w_memin_index;
    wire [OffsetWidth-1:0] w_memin_offset;
    wire [TagWidth-1:0]    w_snoop_tag;
    wire [IndexWidth-1:0]  w_snoop_index;
    wire [OffsetWidth-1:0] w_snoop_offset;

    // Internal signals for FIFO operation
    logic r_sysbusin_valid, r_sysbusin_ready, r_sysbusin_op_rdxwr;
    logic [AW-1:0]   r_sysbusin_addr;
    logic [DW-1:0]   r_sysbusin_data;
    logic [DM-1:0]   r_sysbusin_dm;    // Instantiate the sysbusor in FIFO
    fifo_axi_sync #(
        .DATA_WIDTH(1+AW+DW+DM),
        .DEPTH(4),    // Depth of FIFO
        .DEL(1)       // Delay parameter for the FIFO
    ) sysbus_input (
        .i_axi_aclk     (i_clk),
        .i_axi_aresetn  (i_rst_n),
        .i_wr_valid     (i_sysbusin_valid),
        .o_wr_ready     (o_sysbusin_ready),
        .i_wr_data      ({i_sysbusin_op_rdxwr, i_sysbusin_addr, i_sysbusin_data, i_sysbusin_dm}),
        .o_rd_valid     (r_sysbusin_valid),
        .i_rd_ready     (r_sysbusin_ready),
        .o_rd_data      ({r_sysbusin_op_rdxwr, r_sysbusin_addr, r_sysbusin_data, r_sysbusin_dm})
    );

    // Internal signals for FIFO operation
    logic r_sysbusout_valid, r_sysbusout_ready, r_sysbusout_op_rdxwr;
    logic [AW-1:0]   r_sysbusout_addr;
    logic [DW-1:0]   r_sysbusout_data;
    logic [DM-1:0]   r_sysbusout_dm;    // Instantiate the sysbusor in FIFO
    fifo_axi_sync #(
        .DATA_WIDTH(1+AW+DW+DM),
        .DEPTH(4),   // Depth of FIFO
        .DEL(1)       // Delay parameter for the FIFO
    ) sysbus_output (
        .i_axi_aclk     (i_clk),
        .i_axi_aresetn  (i_rst_n),
        .i_wr_valid     (r_sysbusout_valid),
        .o_wr_ready     (r_sysbusout_ready),
        .i_wr_data      ({r_sysbusout_op_rdxwr, r_sysbusout_addr, r_sysbusout_data, r_sysbusout_dm}),
        .o_rd_valid     (o_sysbusout_valid),
        .i_rd_ready     (i_sysbusout_ready),
        .o_rd_data      ({o_sysbusout_op_rdxwr, o_sysbusout_addr, o_sysbusout_data, o_sysbusout_dm})
    );

    // Internal signals for FIFO operation
    logic r_memin_valid, r_memin_ready, r_memin_op_rdxwr;
    logic [AW-1:0]   r_memin_addr;
    logic [DW-1:0]   r_memin_data;
    logic [DM-1:0]   r_memin_dm;    // Instantiate the memor in FIFO
    fifo_axi_sync #(
        .DATA_WIDTH(1+AW+DW+DM),
        .DEPTH(4),   // Depth of FIFO
        .DEL(1)       // Delay parameter for the FIFO
    ) mem_input (
        .i_axi_aclk     (i_clk),
        .i_axi_aresetn  (i_rst_n),
        .i_wr_valid     (i_memin_valid),
        .o_wr_ready     (o_memin_ready),
        .i_wr_data      ({i_memin_op_rdxwr, i_memin_addr, i_memin_data, i_memin_dm}),
        .o_rd_valid     (r_memin_valid),
        .i_rd_ready     (r_memin_ready),
        .o_rd_data      ({r_memin_op_rdxwr, r_memin_addr, r_memin_data, r_memin_dm})
    );

    // Internal signals for FIFO operation
    logic r_memout_valid, r_memout_ready, r_memout_op_rdxwr;
    logic [AW-1:0]   r_memout_addr;
    logic [DW-1:0]   r_memout_data;
    logic [DM-1:0]   r_memout_dm;    // Instantiate the memor in FIFO
    fifo_axi_sync #(
        .DATA_WIDTH(1+AW+DW+DM),
        .DEPTH(4),   // Depth of FIFO
        .DEL(1)       // Delay parameter for the FIFO
    ) mem_output (
        .i_axi_aclk     (i_clk),
        .i_axi_aresetn  (i_rst_n),
        .i_wr_valid     (r_memout_valid),
        .o_wr_ready     (r_memout_ready),
        .i_wr_data      ({r_memout_op_rdxwr, r_memout_addr, r_memout_data, r_memout_dm}),
        .o_rd_valid     (o_memout_valid),
        .i_rd_ready     (i_memout_ready),
        .o_rd_data      ({o_memout_op_rdxwr, o_memout_addr, o_memout_data, o_memout_dm})
    );

    // Internal signals for FIFO operation
    logic r_snoop_valid, r_snoop_ready;
    logic [AW-1:0]   r_snoop_addr;
    logic [3:0]      r_snoop_cmd;
    fifo_axi_sync #(
        .DATA_WIDTH(AW+4),
        .DEPTH(4),   // Depth of FIFO
        .DEL(1)       // Delay parameter for the FIFO
    ) snoop (
        .i_axi_aclk     (i_clk),
        .i_axi_aresetn  (i_rst_n),
        .i_wr_valid     (i_snoop_valid),
        .o_wr_ready     (o_snoop_ready),
        .i_wr_data      ({i_snoop_addr, i_snoop_cmd}),
        .o_rd_valid     (r_snoop_valid),
        .i_rd_ready     (r_snoop_ready),
        .o_rd_data      ({r_snoop_addr, r_snoop_cmd})
    );

    // Internal signals for c2c snoop FIFO operation
    logic r_fifo_c2c_snp_valid, r_fifo_c2c_snp_ready;
    logic [AW-1:0]   r_c2c_snp_addr;
    logic [DW-1:0]   r_c2c_snp_data;
    logic [DM-1:0]   r_c2c_snp_dm;
    fifo_axi_sync #(
        .DATA_WIDTH(AW+DW+DM),
        .DEPTH(4),   // Depth of FIFO
        .DEL(1)       // Delay parameter for the FIFO
    ) c2c_snp_fifo (
        .i_axi_aclk     (i_clk),
        .i_axi_aresetn  (i_rst_n),
        .i_wr_valid     (r_fifo_c2c_snp_valid),
        .o_wr_ready     (r_fifo_c2c_snp_ready),
        .i_wr_data      ({r_c2c_snp_addr, r_c2c_snp_data, r_c2c_snp_dm}),
        .i_rd_ready     (i_c2c_snp_ready),
        .o_rd_valid     (o_c2c_snp_valid),
        .o_rd_data      ({o_c2c_snp_addr, o_c2c_snp_data, o_c2c_snp_dm})
    );

    // Side queue for reads that are sent to the memory
    logic r_read_fifo_wr_en, r_read_fifo_rd_en, r_read_fifo_full, r_read_fifo_empty;
    logic [$clog2(A)-1:0] r_allocated_way, r_read_fifo_rd_data;
    fifo_sync #(
        .DATA_WIDTH($clog2(A)),
        .DEPTH(4)
    ) read_request_fifo (
        .i_clk        (i_clk),
        .i_rst_n      (i_rst_n),
        .i_write      (r_read_fifo_wr_en),
        .i_wr_data    (r_allocated_way),
        .i_read       (r_read_fifo_rd_en),
        .o_rd_data    (r_read_fifo_rd_data),
        .o_wr_full    (r_read_fifo_full),
        .o_rd_empty   (r_read_fifo_empty)
    );

    assign w_sysbusin_tag = r_sysbusin_addr[AW-1:AW-TagWidth];
    assign w_sysbusin_index = r_sysbusin_addr[AW-TagWidth-1:AW-TagWidth-IndexWidth];
    assign w_sysbusin_offset = r_sysbusin_addr[AW-TagWidth-IndexWidth-1:AW-TagWidth-IndexWidth-OffsetWidth];
    assign w_memin_tag = r_memin_addr[AW-1:AW-TagWidth];
    assign w_memin_index = r_memin_addr[AW-TagWidth-1:AW-TagWidth-IndexWidth];
    assign w_memin_offset = r_memin_addr[AW-TagWidth-IndexWidth-1:AW-TagWidth-IndexWidth-OffsetWidth];
    assign w_snoop_tag = r_snoop_addr[AW-1:AW-TagWidth];
    assign w_snoop_index = r_snoop_addr[AW-TagWidth-1:AW-TagWidth-IndexWidth];
    assign w_snoop_offset = r_snoop_addr[AW-TagWidth-IndexWidth-1:AW-TagWidth-IndexWidth-OffsetWidth];

    wire [A-1:0] w_sysbusin_way_hit;
    wire [A-1:0] w_memin_way_hit;
    wire [A-1:0] w_snoop_way_hit;
    assign       o_sysbusin_hit = |w_sysbusin_way_hit;
    assign       o_snoop_hit = |w_snoop_way_hit;
    logic [$clog2(A)-1:0] new_way = get_plru_way(r_plru_bits[w_sysbusin_index]);
    logic [$clog2(A)-1:0] evict_way = get_plru_way(r_plru_bits[w_sysbusin_index]);

    genvar i;
    generate
        for (i = 0; i < A; i = i + 1) begin : gen_way_hit
            assign w_sysbusin_way_hit[i] = r_valid_array[w_sysbusin_index*A+i] && (r_tag_array[w_sysbusin_index*A+i] == w_sysbusin_tag);
            assign w_memin_way_hit[i] = r_valid_array[w_memin_index*A+i] && (r_tag_array[w_memin_index*A+i] == w_memin_tag);
            assign w_snoop_way_hit[i] = r_valid_array[w_snoop_index*A+i] && (r_tag_array[w_snoop_index*A+i] == w_snoop_tag);
        end
    endgenerate

    integer j, k;
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (~i_rst_n) begin
            for (j = 0; j < DEPTH; j++) begin
                r_valid_array[j] <= 1'b0;
                r_dirty_array[j] <= 1'b0;
                r_tag_array[j] <= {TagWidth{1'b0}};
            end
            for (j = 0; j < S; j = j + 1) begin
                r_plru_bits[j] <= {A-1{1'b0}};
            end
            for (j = 0; j < DEPTH; j = j + 1) begin
                for (int k = 0; k < A; k = k + 1) begin
                    r_state_array[j][k] <= StateI;
                    r_dm_array[j][k] <= {DM{1'b0}};
                end
            end
            r_memout_valid <= 1'b0;
            r_memout_op_rdxwr <= 1'b0;
            r_memout_addr <= {AW{1'b0}};
            r_memout_data <= {DW{1'b0}};
            r_memout_dm <= {DM{1'b0}};
            r_fifo_c2c_snp_valid <= 1'b0;
            r_c2c_snp_addr <= {AW{1'b0}};
            r_c2c_snp_data <= {DW{1'b0}};
            r_c2c_snp_dm <= {DM{1'b0}};
        end else begin
            //////////////////////////////////////////////////////////////////////////////////////////////////////////////
            // Read request handling
            if (r_sysbusin_valid && !r_sysbusin_op_rdxwr) begin
                if (o_sysbusin_hit) begin
                    // Read hit
                    r_sysbusin_ready <= 1'b1;
                    r_sysbusout_valid <= 1'b1;
                    r_sysbusout_op_rdxwr <= 'b0;
                    r_sysbusout_addr <= r_sysbusin_addr;
                    r_sysbusout_data <= r_data_array[w_sysbusin_index][w_sysbusin_way_hit][w_sysbusin_offset*DW/8 +: DW/8];
                    r_sysbusout_dm <= r_dm_array[w_sysbusin_index][w_sysbusin_way_hit][w_sysbusin_offset +: DM];
                end else begin
                    // Read miss, send a read to the memout interface
                    if (r_memout_ready && !r_read_fifo_full) begin
                        r_memout_valid <= 1'b1;
                        r_memout_op_rdxwr <= 1'b0;
                        r_memout_addr <= r_sysbusin_addr;
                        r_sysbusin_ready <= 1'b1;
                        // Allocate a new entry using PLRU
                        r_allocated_way <= new_way;
                        r_read_fifo_wr_en <= 1'b1;
                    end else begin
                        r_sysbusin_ready <= 1'b0;
                        r_read_fifo_wr_en <= 1'b0;
                    end
                end
            end else begin
                r_sysbusin_ready <= 1'b0;
                r_sysbusout_valid <= 1'b0;
                r_read_fifo_wr_en <= 1'b0;
            end
            //////////////////////////////////////////////////////////////////////////////////////////////////////////////
            // Handle memory input (read response)
            if (i_memin_valid && r_sysbusout_ready && !i_memin_op_rdxwr && !r_read_fifo_empty) begin
                // Get the allocated way from the side queue
                logic [$clog2(A)-1:0] allocated_way;
                allocated_way <= r_read_fifo_rd_data;
                // Update the cache entry with the received data
                r_tag_array[w_memin_index][allocated_way] <= w_memin_tag;
                for (int i = 0; i < A; i++) begin
                    r_data_array[w_memin_index][w_memin_way_hit][i*DW +: DW] <= i_memin_data[i*DW +: DW];
                end
                r_valid_array[w_memin_index][allocated_way] <= 1'b1;
                r_state_array[w_memin_index][allocated_way] <= StateE;
                // Provide the read data on the sysbus output
                r_sysbusout_valid <= 1'b1;
                r_sysbusout_op_rdxwr <= 'b0;
                r_sysbusout_addr <= i_memin_addr;
                r_sysbusout_data <= i_memin_data;
                r_sysbusout_dm <= i_memin_dm;
                // Update PLRU bits for the allocated way
                r_plru_bits[w_sysbusin_index] <= update_plru(r_plru_bits[w_sysbusin_index], allocated_way);
                // Remove the allocated way from the side queue
                r_read_fifo_rd_en <= 1'b1;
            end else begin
                r_read_fifo_rd_en <= 1'b0;
            end
            //////////////////////////////////////////////////////////////////////////////////////////////////////////////
            // Write request handling
            if (r_sysbusin_valid && r_sysbusin_op_rdxwr) begin
                if (o_sysbusin_hit) begin
                    // Write hit
                    for (int i = 0; i < A; i++) begin
                        if (w_sysbusin_way_hit[i]) begin
                            // Update the cache data and byte enables
                            for (int j = 0; j < DM; j++) begin
                                if (r_sysbusin_dm[j]) begin
                                    r_data_array[w_sysbusin_index][w_sysbusin_way_hit][w_sysbusin_offset*DW+j*8+:8] <= r_sysbusin_data[j*8+:8];
                                    r_dm_array[w_sysbusin_index][w_sysbusin_way_hit][w_sysbusin_offset*DM+j] <= 1'b1;
                                end
                            end
                            // Update the cache line state and dirty bit
                            r_state_array[w_sysbusin_index][i] <= StateM;
                            r_dirty_array[w_sysbusin_index][i] <= 1'b1;
                            // Update PLRU bits for the accessed set
                            r_plru_bits[w_sysbusin_index] <= update_plru(r_plru_bits[w_sysbusin_index], i);
                        end
                    end
                    r_sysbusin_ready <= 1'b1;
                end else begin
                    // Write miss
                    // Check for a dirty entry to evict
                    if (r_dirty_array[w_sysbusin_index*A+evict_way]) begin
                        // Evict the dirty entry
                        if (r_memout_ready) begin
                            r_memout_valid <= 1'b1;
                            r_memout_op_rdxwr <= 1'b1;
                            r_memout_addr <= {r_tag_array[w_sysbusin_index*A+evict_way], w_sysbusin_index, {OffsetWidth{1'b0}}};
                            for (int i = 0; i < A; i++) begin
                                r_memout_data[i*DW +: DW] <= r_data_array[w_sysbusin_index][evict_way][i*DW +: DW];
                                r_memout_dm[i*DM +: DM] <= r_dm_array[w_sysbusin_index][evict_way][i*DM +: DM];
                            end
                            r_dirty_array[w_sysbusin_index*A+evict_way] <= 1'b0;
                            r_sysbusin_ready <= 1'b1;
                        end else begin
                            r_sysbusin_ready <= 1'b0;
                        end
                    end else begin
                        r_sysbusin_ready <= 1'b1;
                    end
                    // Allocate a new entry
                    r_tag_array[w_sysbusin_index*A+evict_way] <= w_sysbusin_tag;
                    for (int j = 0; j < DM; j++) begin
                        if (r_sysbusin_dm[j]) begin
                            r_data_array[w_sysbusin_index][evict_way][w_sysbusin_offset*DW+j*8+:8] <= r_sysbusin_data[j*8+:8];
                            r_dm_array[w_sysbusin_index][evict_way][w_sysbusin_offset*DM+j] <= 1'b1;
                        end else begin
                            r_dm_array[w_sysbusin_index][evict_way][w_sysbusin_offset*DM+j] <= 1'b0;
                        end
                    end
                    r_valid_array[w_sysbusin_index][evict_way] <= 1'b1;
                    r_dirty_array[w_sysbusin_index][evict_way] <= 1'b1;
                    r_state_array[w_sysbusin_index][evict_way] <= StateM;
                    // Update PLRU bits for the allocated way
                    r_plru_bits[w_sysbusin_index] <= update_plru(r_plru_bits[w_sysbusin_index], evict_way);
                end
            end else begin
                r_sysbusin_ready <= 1'b0;
            end
            //////////////////////////////////////////////////////////////////////////////////////////////////////////////
            // Snoop request handling
            r_snoop_ready <= 1'b1;
            r_fifo_c2c_snp_valid <= 1'b0;
            if (r_snoop_valid) begin
                case (r_snoop_cmd)
                    CmdSnpRead: begin
                        // Snoop read request
                        if (o_snoop_hit) begin
                            // Snoop hit
                            for (int i = 0; i < A; i++) begin
                                o_snoop_data[i*DW +: DW] <= r_data_array[w_snoop_index][w_snoop_way_hit][i*DW +: DW];
                            end
                            o_snoop_dirty <= r_dirty_array[w_snoop_index*A+w_snoop_way_hit];
                            if (r_state_array[w_snoop_index][w_snoop_way_hit] == StateM ||
                                r_state_array[w_snoop_index][w_snoop_way_hit] == StateE) begin
                                // If the cache line is in the Modified or Exclusive state, initiate a C2C snoop transfer
                                if (r_fifo_c2c_snp_ready) begin
                                    r_fifo_c2c_snp_valid <= 1'b1;
                                    r_snoop_ready <= 1'b1;
                                    r_c2c_snp_addr <= {r_tag_array[w_snoop_index][w_snoop_way_hit], w_snoop_index, {OffsetWidth{1'b0}}};
                                    for (int i = 0; i < A; i++) begin
                                        r_c2c_snp_data[i*DW +: DW] <= r_data_array[w_snoop_index][w_snoop_way_hit][i*DW +: DW];
                                        r_c2c_snp_dm[i*DM +: DM] <= r_dm_array[w_snoop_index][w_snoop_way_hit][i*DM +: DM];
                                    end
                                end else begin
                                    // If the c2c_snp queue is not ready, wait for it to become ready
                                    r_snoop_ready <= 1'b0;
                                end
                                r_snoop_ready <= 1'b1;
                            end
                            if (r_state_array[w_snoop_index][w_snoop_way_hit] == StateM) begin
                                // If the cache line is in the Modified state, transition to Shared state
                                r_state_array[w_snoop_index][w_snoop_way_hit] <= StateS;
                            end
                        end else begin
                            // Snoop miss
                            o_snoop_data <= {DW{1'b0}};
                            o_snoop_dirty <= 1'b0;
                        end
                    end
                    CmdSnpRfo: begin
                        // Snoop read-for-ownership request
                        if (o_snoop_hit) begin
                            // Snoop hit
                            for (int i = 0; i < A; i++) begin
                                o_snoop_data[i*DW +: DW] <= r_data_array[w_snoop_index][w_snoop_way_hit][i*DW +: DW];
                            end
                            o_snoop_dirty <= r_dirty_array[w_snoop_index][w_snoop_way_hit];
                            if (r_dirty_array[w_snoop_index][w_snoop_way_hit]) begin
                                // If the cache line is dirty, write it back to memory
                                if (r_memout_ready) begin
                                    r_snoop_ready <= 1'b1;
                                    r_memout_valid <= 1'b1;
                                    r_memout_op_rdxwr <= 1'b1;
                                    r_memout_addr <= {r_tag_array[w_snoop_index][w_snoop_way_hit], w_snoop_index, {OffsetWidth{1'b0}}};
                                    for (int i = 0; i < A; i++) begin
                                        r_memout_data[i*DW +: DW] <= r_data_array[w_snoop_index][w_snoop_way_hit][i*DW +: DW];
                                        r_memout_dm[i*DM +: DM] <= r_dm_array[w_snoop_index][w_snoop_way_hit][i*DM +: DM];
                                    end
                                    r_dirty_array[w_snoop_index*A+w_snoop_way_hit] <= 1'b0;
                                end else begin
                                    // If the memory output interface is not ready, wait for it to become ready
                                    r_snoop_ready <= 1'b0;
                                end
                            end
                            // Invalidate the cache line
                            r_valid_array[w_snoop_index][w_snoop_way_hit] <= 1'b0;
                            r_state_array[w_snoop_index][w_snoop_way_hit] <= StateI;
                        end else begin
                            // Snoop miss
                            o_snoop_data <= {DW{1'b0}};
                            o_snoop_dirty <= 1'b0;
                        end
                    end
                    CmdSnpInv: begin
                        // Snoop invalidate request
                        if (o_snoop_hit) begin
                            // Snoop hit
                            if (r_dirty_array[w_snoop_index*A+w_snoop_way_hit]) begin
                                // If the cache line is dirty, write it back to memory
                                if (r_memout_ready) begin
                                    r_snoop_ready <= 1'b1;
                                    r_memout_valid <= 1'b1;
                                    r_memout_op_rdxwr <= 1'b1;
                                    r_memout_addr <= {r_tag_array[w_snoop_index][w_snoop_way_hit], w_snoop_index, {OffsetWidth{1'b0}}};
                                    for (int i = 0; i < A; i++) begin
                                        r_memout_data[i*DW +: DW] <= r_data_array[w_snoop_index][w_snoop_way_hit][i*DW +: DW];
                                        r_memout_dm[i*DM +: DM] <= r_dm_array[w_snoop_index][w_snoop_way_hit][i*DM +: DM];
                                    end
                                    r_dirty_array[w_snoop_index][w_snoop_way_hit] <= 1'b0;
                                end else begin
                                    // If the memory output interface is not ready, wait for it to become ready
                                    r_snoop_ready <= 1'b0;
                                end
                            end
                            // Invalidate the cache line
                            r_valid_array[w_snoop_index][w_snoop_way_hit] <= 1'b0;
                            r_state_array[w_snoop_index][w_snoop_way_hit] <= StateI;
                        end
                    end
                    default: begin
                        o_snoop_data <= {DW{1'b0}};
                        o_snoop_dirty <= 1'b0;
                    end
                endcase
            end
        end
    end

endmodule : cache_plru_mesi
