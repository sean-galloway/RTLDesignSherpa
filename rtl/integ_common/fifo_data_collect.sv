`timescale 1ns / 1ps

module fifo_data_collect #(
    parameter     INSTANCE_NAME = "DEADF1F0",  // verilog_lint: waive explicit-parameter-storage-type
    parameter int DATA_WIDTH = 8,
    parameter int ID_WIDTH = 4,
    parameter int OUTPUT_FIFO_DEPTH = 16,
    parameter int CHUNKS = 4,        // Number of data chunks to collect before sending to FIFO
    // Abbreviations for brevity
    parameter int DW = DATA_WIDTH,
    parameter int IDW = ID_WIDTH,
    parameter int LOG2_CHUNKS = $clog2(CHUNKS)
) (
    // Global Clock and Reset
    input  logic                     clk,
    input  logic                     rst_n,

    // Arbiter weights (0-15 for each channel)
    input  logic [3:0]               weight_a,
    input  logic [3:0]               weight_b,
    input  logic [3:0]               weight_c,
    input  logic [3:0]               weight_d,

    // Input Channel A
    input  logic                     a_write,
    output logic                     a_full,
    input  logic [DW-1:0]            a_data,
    input  logic [IDW-1:0]           a_id,

    // Input Channel B
    input  logic                     b_write,
    output logic                     b_full,
    input  logic [DW-1:0]            b_data,
    input  logic [IDW-1:0]           b_id,

    // Input Channel C
    input  logic                     c_write,
    output logic                     c_full,
    input  logic [DW-1:0]            c_data,
    input  logic [IDW-1:0]           c_id,

    // Input Channel D
    input  logic                     d_write,
    output logic                     d_full,
    input  logic [DW-1:0]            d_data,
    input  logic [IDW-1:0]           d_id,

    // Output Channel E (FIFO)
    input  logic                     e_read,
    output logic                     e_empty,
    output logic [IDW+CHUNKS*DW-1:0] e_data
);

    // ===========================================================================
    // Internal signals

    // fifo_sync outputs for channel A
    logic                   w_a_empty;
    logic                   w_a_read;
    logic [DW-1:0]          w_a_data;
    logic [IDW-1:0]         w_a_id;
    logic [IDW+DW-1:0]      w_a_combined_data;

    // fifo_sync outputs for channel B
    logic                   w_b_empty;
    logic                   w_b_read;
    logic [DW-1:0]          w_b_data;
    logic [IDW-1:0]         w_b_id;
    logic [IDW+DW-1:0]      w_b_combined_data;

    // fifo_sync outputs for channel C
    logic                   w_c_empty;
    logic                   w_c_read;
    logic [DW-1:0]          w_c_data;
    logic [IDW-1:0]         w_c_id;
    logic [IDW+DW-1:0]      w_c_combined_data;

    // fifo_sync outputs for channel D
    logic                   w_d_empty;
    logic                   w_d_read;
    logic [DW-1:0]          w_d_data;
    logic [IDW-1:0]         w_d_id;
    logic [IDW+DW-1:0]      w_d_combined_data;

    // Arbiter signals
    logic [3:0]             w_arb_req;
    logic                   w_arb_gnt_valid;
    logic [3:0]             w_arb_gnt;
    logic [1:0]             w_arb_gnt_id;

    // Weighted Round Robin Arbiter flattened weights (16 bits * 4 channels = 64 bits)
    logic [15:0]            w_arb_weights;
    assign w_arb_weights = {weight_d, weight_c, weight_b, weight_a};

    // Data collection buffer using vectors
    logic [IDW-1:0]         r_id;
    logic [CHUNKS*DW-1:0]   r_data;        // Vector of data chunks
    logic [CHUNKS-1:0]      r_valid;       // Vector of valid flags

    // Buffer control signals
    logic                   w_buffer_full;
    logic                   w_buffer_accept;
    logic                   w_output_write;
    logic                   w_slot_available;
    logic [LOG2_CHUNKS-1:0] w_next_slot_index;

    // Output FIFO signals
    logic                   w_output_full;
    logic [IDW+CHUNKS*DW-1:0] w_output_data;

    // ===========================================================================
    // Input FIFOs for each channel

    // Channel A FIFO
    fifo_sync #(
        .REGISTERED       (0),
        .DATA_WIDTH       (DW + IDW),
        .DEPTH            (2),
        .INSTANCE_NAME    ("FIFO_A")
    ) a_fifo (
        .clk            (clk),
        .rst_n          (rst_n),
        .write          (a_write),
        .wr_data        ({a_id, a_data}),
        .wr_full        (a_full),
        .wr_almost_full (),
        .read           (w_a_read),
        .rd_data        ({ w_a_id, w_a_data}),
        .rd_empty       (w_a_empty),
        .rd_almost_empty()
    );

    // Channel B FIFO
    fifo_sync #(
        .REGISTERED       (0),
        .DATA_WIDTH       (DW + IDW),
        .DEPTH            (2),
        .INSTANCE_NAME    ("FIFO_B")
    ) b_fifo (
        .clk            (clk),
        .rst_n          (rst_n),
        .write          (b_write),
        .wr_data        ({b_id, b_data}),
        .wr_full        (b_full),
        .wr_almost_full (),
        .read           (w_b_read),
        .rd_data        ({ w_b_id, w_b_data}),
        .rd_empty       (w_b_empty),
        .rd_almost_empty()
    );

    // Channel C FIFO
    fifo_sync #(
        .REGISTERED       (0),
        .DATA_WIDTH       (DW + IDW),
        .DEPTH            (2),
        .INSTANCE_NAME    ("FIFO_C")
    ) c_fifo (
        .clk            (clk),
        .rst_n          (rst_n),
        .write          (c_write),
        .wr_data        ({c_id, c_data}),
        .wr_full        (c_full),
        .wr_almost_full (),
        .read           (w_c_read),
        .rd_data        ({ w_c_id, w_c_data}),
        .rd_empty       (w_c_empty),
        .rd_almost_empty()
    );

    // Channel D FIFO
    fifo_sync #(
        .REGISTERED       (0),
        .DATA_WIDTH       (DW + IDW),
        .DEPTH            (2),
        .INSTANCE_NAME    ("FIFO_D")
    ) d_fifo (
        .clk            (clk),
        .rst_n          (rst_n),
        .write          (d_write),
        .wr_data        ({d_id, d_data}),
        .wr_full        (d_full),
        .wr_almost_full (),
        .read           (w_d_read),
        .rd_data        ({ w_d_id, w_d_data}),
        .rd_empty       (w_d_empty),
        .rd_almost_empty()
    );

    // ===========================================================================
    // Weighted Round Robin Arbiter

    // Request vector from FIFO empty signals (inverted since request is active high)
    assign w_arb_req = {!w_d_empty, !w_c_empty, !w_b_empty, !w_a_empty};

    // Block arbitration when buffer is full, being written to output, or when we have a valid grant
    // This ensures the arbiter stays locked to the current agent until data is written to output
    logic                   r_arb_locked;  // Register to hold arbiter locked state

    // Locked agent identification (persists during locked state)
    logic [1:0]             r_locked_agent_id;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_arb_locked <= 1'b0;
            r_locked_agent_id <= '0;
        end else begin
            if (w_output_write) begin
                // Release arbiter lock when data is written to output
                r_arb_locked <= 1'b0;
            end else if (w_arb_gnt_valid && !r_arb_locked) begin
                // Lock arbiter when we choose the next agent
                r_arb_locked <= 1'b1;
                r_locked_agent_id <= w_arb_gnt_id;
            end
        end
    end

    arbiter_round_robin_weighted #(
        .MAX_THRESH    (16),             // Weight range 0-15
        .CLIENTS       (4),              // 4 input channels
        .WAIT_GNT_ACK  (0)               // No grant acknowledge mechanism
    ) inst_arbiter (
        .clk         (clk),
        .rst_n       (rst_n),
        .block_arb   (r_arb_locked),
        .max_thresh  (w_arb_weights),  // Weights for all channels
        .req         (w_arb_req),      // Valid signals from all input FIFOs
        .gnt_valid  (w_arb_gnt_valid),
        .gnt        (w_arb_gnt),      // One-hot grant signal
        .gnt_id     (w_arb_gnt_id),   // Binary grant ID
        .gnt_ack     (4'b0)            // Not using ack mechanism
    );

    // Buffer full detection - all slots filled
    assign w_buffer_full = &r_valid;  // Reduction AND of all valid bits

    // Buffer ready condition
    logic w_buffer_ready;
    assign w_buffer_ready = !w_buffer_full && r_arb_locked;

    // ===========================================================================
    // Data Collection Logic
    // Read control signals for each FIFO based on arbiter lock and buffer ready
    always_comb begin
        // Default values
        w_a_read = 1'b0;
        w_b_read = 1'b0;
        w_c_read = 1'b0;
        w_d_read = 1'b0;
        w_buffer_accept = 1'b0;

        // Only read from the selected channel if locked and buffer is ready
        if (r_arb_locked && w_buffer_ready) begin
            casez (r_locked_agent_id)
                2'b00: begin
                    w_a_read = !w_a_empty;
                    w_buffer_accept = !w_a_empty;
                end
                2'b01: begin
                    w_b_read = !w_b_empty;
                    w_buffer_accept = !w_b_empty;
                end
                2'b10: begin
                    w_c_read = !w_c_empty;
                    w_buffer_accept = !w_c_empty;
                end
                2'b11: begin
                    w_d_read = !w_d_empty;
                    w_buffer_accept = !w_d_empty;
                end
                default: begin
                    // Default values
                    w_a_read = 1'b0;
                    w_b_read = 1'b0;
                    w_c_read = 1'b0;
                    w_d_read = 1'b0;
                    w_buffer_accept = 1'b0;
                end
            endcase
        end
    end

    // Data selector signals
    logic [DW-1:0]          w_data;
    logic [IDW-1:0]         w_id;

    // Data selector mux based on locked agent
    always_comb begin
        w_data = '0;
        w_id = '0;
        // Use locked agent ID to select data
        casez (r_locked_agent_id)
            2'b00: begin
                w_data = w_a_data;
                w_id = w_a_id;
            end
            2'b01: begin
                w_data = w_b_data;
                w_id = w_b_id;
            end
            2'b10: begin
                w_data = w_c_data;
                w_id = w_c_id;
            end
            2'b11: begin
                w_data = w_d_data;
                w_id = w_d_id;
            end
            default: begin
                w_data = '0;
                w_id = '0;
            end
        endcase
    end

    // Output write control - write when buffer is full and output FIFO is not full
    assign w_output_write = w_buffer_full && !w_output_full;

    // Create output data by concatenating ID and all data chunks
    // ID is in the most significant bits (uppermost), followed by data chunks
    assign w_output_data = {r_id, r_data};

    // Buffer control logic - collect data chunks and track their valid status
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_valid <= '0;
            r_data <= '0;
            r_id <= '0;
        end else begin
            // Clear valid flags when data is written to output
            if (w_output_write) begin
                r_id <= 'b0;
                r_valid <= '0;
                r_data <= 'b0;
            end
            // Accept new data if available and there's an open slot
            else if (w_buffer_accept) begin
                // Shift the data in
                r_valid <= {1'b1, r_valid[CHUNKS-1:1]};
                r_data <= {w_data, r_data[CHUNKS*DW-1:DW]};
                // Always use the ID from the most recent data
                r_id <= w_id;
            end
        end
    end

    // ===========================================================================
    // Output FIFO

    fifo_sync #(
        .REGISTERED       (0),
        .DATA_WIDTH       (IDW + CHUNKS*DW),
        .DEPTH            (OUTPUT_FIFO_DEPTH),
        .INSTANCE_NAME    ("FIFO_OUT")
    ) output_fifo (
        .clk            (clk),
        .rst_n          (rst_n),
        .write          (w_output_write),
        .wr_data        (w_output_data),
        .wr_full        (w_output_full),
        .wr_almost_full (),
        .read           (e_read),
        .rd_data        (e_data),
        .rd_empty       (e_empty),
        .rd_almost_empty()
    );

endmodule : fifo_data_collect