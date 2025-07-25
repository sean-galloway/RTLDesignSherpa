`timescale 1ns / 1ps

module gaxi_data_collect #(
    parameter int REGISTERED = 0,  // 0 = mux mode, 1 = flop mode
    parameter int DATA_WIDTH = 8,
    parameter int ID_WIDTH = 4,
    parameter int OUTPUT_FIFO_DEPTH = 16,
    parameter int SKID_DEPTH = 2,
    parameter int CHUNKS = 4,        // Number of data chunks to collect before sending to FIFO
    // Abbreviations for brevity
    parameter int DW = DATA_WIDTH,
    parameter int IDW = ID_WIDTH,
    parameter int LOG2_CHUNKS = $clog2(CHUNKS)
) (
    // Global Clock and Reset
    input  logic                    axi_aclk,
    input  logic                    axi_aresetn,

    // Arbiter weights (0-15 for each channel)
    input  logic [3:0]              weight_a,
    input  logic [3:0]              weight_b,
    input  logic [3:0]              weight_c,
    input  logic [3:0]              weight_d,

    // Input Channel A
    input  logic                    a_valid,
    output logic                    a_ready,
    input  logic [DW-1:0]           a_data,
    input  logic [IDW-1:0]          a_id,

    // Input Channel B
    input  logic                    b_valid,
    output logic                    b_ready,
    input  logic [DW-1:0]           b_data,
    input  logic [IDW-1:0]          b_id,

    // Input Channel C
    input  logic                    c_valid,
    output logic                    c_ready,
    input  logic [DW-1:0]           c_data,
    input  logic [IDW-1:0]          c_id,

    // Input Channel D
    input  logic                    d_valid,
    output logic                    d_ready,
    input  logic [DW-1:0]           d_data,
    input  logic [IDW-1:0]          d_id,

    // Output Channel E (FIFO)
    output logic                    e_valid,
    input  logic                    e_ready,
    output logic [IDW+CHUNKS*DW-1:0] e_data
);

    // ===========================================================================
    // Internal signals

    // Skid buffer outputs for channel A
    logic                   w_a_skid_valid;
    logic                   w_a_skid_ready;
    logic [DW-1:0]          w_a_skid_data;
    logic [IDW-1:0]         w_a_skid_id;

    // Skid buffer outputs for channel B
    logic                   w_b_skid_valid;
    logic                   w_b_skid_ready;
    logic [DW-1:0]          w_b_skid_data;
    logic [IDW-1:0]         w_b_skid_id;

    // Skid buffer outputs for channel C
    logic                   w_c_skid_valid;
    logic                   w_c_skid_ready;
    logic [DW-1:0]          w_c_skid_data;
    logic [IDW-1:0]         w_c_skid_id;

    // Skid buffer outputs for channel D
    logic                   w_d_skid_valid;
    logic                   w_d_skid_ready;
    logic [DW-1:0]          w_d_skid_data;
    logic [IDW-1:0]         w_d_skid_id;

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
    logic                   w_fifo_write;
    logic                   w_slot_available;
    logic [LOG2_CHUNKS-1:0] w_next_slot_index;

    // FIFO signals
    logic                   w_fifo_wr_valid;
    logic                   w_fifo_wr_ready;
    logic [IDW+CHUNKS*DW-1:0] w_fifo_wr_data;

    // ===========================================================================
    // Skid Buffers for each input channel

    // Channel A Skid Buffer
    gaxi_skid_buffer #(
        .DATA_WIDTH(DW + IDW),
        .DEPTH(SKID_DEPTH)
    ) a_skid_buffer (
        .axi_aclk    (axi_aclk),
        .axi_aresetn (axi_aresetn),
        .wr_valid    (a_valid),
        .wr_ready    (a_ready),
        .wr_data     ({a_id, a_data}),
        .rd_valid    (w_a_skid_valid),
        .rd_ready    (w_a_skid_ready),
        .rd_data     ({w_a_skid_id, w_a_skid_data}),
        .count      (),
        .rd_count    ()
    );

    // Channel B Skid Buffer
    gaxi_skid_buffer #(
        .DATA_WIDTH(DW + IDW),
        .DEPTH(SKID_DEPTH)
    ) b_skid_buffer (
        .axi_aclk    (axi_aclk),
        .axi_aresetn (axi_aresetn),
        .wr_valid    (b_valid),
        .wr_ready    (b_ready),
        .wr_data     ({b_id, b_data}),
        .rd_valid    (w_b_skid_valid),
        .rd_ready    (w_b_skid_ready),
        .rd_data     ({w_b_skid_id, w_b_skid_data}),
        .count      (),
        .rd_count    ()
    );

    // Channel C Skid Buffer
    gaxi_skid_buffer #(
        .DATA_WIDTH(DW + IDW),
        .DEPTH(SKID_DEPTH)
    ) c_skid_buffer (
        .axi_aclk    (axi_aclk),
        .axi_aresetn (axi_aresetn),
        .wr_valid    (c_valid),
        .wr_ready    (c_ready),
        .wr_data     ({c_id, c_data}),
        .rd_valid    (w_c_skid_valid),
        .rd_ready    (w_c_skid_ready),
        .rd_data     ({w_c_skid_id, w_c_skid_data}),
        .count      (),
        .rd_count    ()
    );

    // Channel D Skid Buffer
    gaxi_skid_buffer #(
        .DATA_WIDTH(DW + IDW),
        .DEPTH(SKID_DEPTH)
    ) d_skid_buffer (
        .axi_aclk    (axi_aclk),
        .axi_aresetn (axi_aresetn),
        .wr_valid    (d_valid),
        .wr_ready    (d_ready),
        .wr_data     ({d_id, d_data}),
        .rd_valid    (w_d_skid_valid),
        .rd_ready    (w_d_skid_ready),
        .rd_data     ({w_d_skid_id, w_d_skid_data}),
        .count      (),
        .rd_count    ()
    );

    // ===========================================================================
    // Weighted Round Robin Arbiter

    // Request vector from skid buffer valid signals
    assign w_arb_req = {w_d_skid_valid, w_c_skid_valid, w_b_skid_valid, w_a_skid_valid};

    // Block arbitration when buffer is full, being written to FIFO, or when we have a valid grant
    // This ensures the arbiter stays locked to the current agent until data is written to FIFO
    logic                   r_arb_locked;  // Register to hold arbiter locked state

    // Locked agent identification (persists during locked state)
    logic [1:0]             r_locked_agent_id;

    always_ff @(posedge axi_aclk or negedge axi_aresetn) begin
        if (!axi_aresetn) begin
            r_arb_locked <= 1'b0;
            r_locked_agent_id <= '0;
        end else begin
            if (w_fifo_write) begin
                // Release arbiter lock when data is written to FIFO
                r_arb_locked <= 1'b0;
            end else if (w_arb_gnt_valid && !r_arb_locked) begin
                // Lock arbiter when we choose the next agent
                r_arb_locked <= 1'b1;
                r_locked_agent_id <= w_arb_gnt_id;
            end
        end
    end

    arbiter_round_robin_weighted #(
        .MAX_THRESH(16),       // Weight range 0-15
        .CLIENTS(4),           // 4 input channels
        .WAIT_GNT_ACK(0)       // No grant acknowledge mechanism
    ) inst_arbiter (
        .clk         (axi_aclk),
        .rst_n       (axi_aresetn),
        .block_arb   (r_arb_locked),
        .max_thresh  (w_arb_weights),  // Weights for all channels
        .req         (w_arb_req),      // Valid signals from all skid buffers
        .gnt_valid  (w_arb_gnt_valid),
        .gnt        (w_arb_gnt),      // One-hot grant signal
        .gnt_id     (w_arb_gnt_id),   // Binary grant ID
        .gnt_ack     (4'b0)          // Not using ack mechanism
    );

    // Buffer full detection - all slots filled
    assign w_buffer_full = &r_valid;  // Reduction AND of all valid bits

    // Buffer ready condition
    logic w_buffer_ready;
    assign w_buffer_ready = !w_buffer_full && r_arb_locked;

    // ===========================================================================
    // Data Collection Logic
    // Only assert ready when arbiter grant is valid or we're locked to an agent
    // Determine if we can accept data from the selected or locked agent
    
    // Fix for latch issue - initialize all signals
    always_comb begin
        // Default assignments to prevent latches
        w_a_skid_ready = 1'b0;
        w_b_skid_ready = 1'b0;
        w_c_skid_ready = 1'b0;
        w_d_skid_ready = 1'b0;
        w_buffer_accept = 1'b0;
        
        // Only set ready for the selected channel
        if (r_arb_locked) begin
            case (r_locked_agent_id)
                2'b00: begin
                    w_a_skid_ready = w_buffer_ready;
                    w_buffer_accept = w_a_skid_valid && w_buffer_ready;
                end
                2'b01: begin
                    w_b_skid_ready = w_buffer_ready;
                    w_buffer_accept = w_b_skid_valid && w_buffer_ready;
                end
                2'b10: begin
                    w_c_skid_ready = w_buffer_ready;
                    w_buffer_accept = w_c_skid_valid && w_buffer_ready;
                end
                2'b11: begin
                    w_d_skid_ready = w_buffer_ready;
                    w_buffer_accept = w_d_skid_valid && w_buffer_ready;
                end
                default: begin
                    // Already assigned default values
                end
            endcase
        end
    end

    // Data selector signals
    logic [DW-1:0]          w_data;
    logic [IDW-1:0]         w_id;

    // Data selector mux based on arbiter grant or locked agent
    always_comb begin
        w_data = '0;
        w_id = '0;
        // Locked to a specific agent - use locked agent ID
        case (r_locked_agent_id)
            2'b00: begin
                w_data = w_a_skid_data;
                w_id = w_a_skid_id;
            end
            2'b01: begin
                w_data = w_b_skid_data;
                w_id = w_b_skid_id;
            end
            2'b10: begin
                w_data = w_c_skid_data;
                w_id = w_c_skid_id;
            end
            2'b11: begin
                w_data = w_d_skid_data;
                w_id = w_d_skid_id;
            end
            default: begin
                w_data = '0;
                w_id = '0;
            end
        endcase
    end

    // FIFO write control - write when buffer is full and FIFO is ready
    assign w_fifo_write = w_buffer_full && w_fifo_wr_ready;
    assign w_fifo_wr_valid = w_buffer_full;

    // Create FIFO data by concatenating ID and all data chunks
    // ID is in the most significant bits (uppermost), followed by data3, data2, data1, data0
    assign w_fifo_wr_data = {r_id, r_data};

    // Buffer control logic - collect data chunks and track their valid status
    always_ff @(posedge axi_aclk or negedge axi_aresetn) begin
        if (!axi_aresetn) begin
            r_valid <= '0;
            r_data <= '0;
            r_id <= '0;
        end else begin
            // Clear valid flags when data is written to FIFO
            if (w_fifo_write) begin
                r_id <= 'b0;
                r_valid <= '0;
                r_data <= 'b0;
            end
            // Accept new data if available and there's an open slot
            else if (w_buffer_accept) begin
                // Store in the next available slot
                r_valid <= {1'b1, r_valid[3:1]};
                r_data <= {w_data, r_data[CHUNKS*DW-1:DW]};

                // Flop the ID to keep it with the data
                r_id <= w_id;

            end
        end
    end

    // ===========================================================================
    // Output FIFO

    gaxi_fifo_sync #(
        .REGISTERED(REGISTERED),
        .DATA_WIDTH(IDW + CHUNKS*DW),
        .DEPTH(OUTPUT_FIFO_DEPTH)
    ) output_fifo (
        .axi_aclk     (axi_aclk),
        .axi_aresetn  (axi_aresetn),
        .wr_valid     (w_fifo_wr_valid),
        .wr_ready     (w_fifo_wr_ready),
        .wr_data      (w_fifo_wr_data),
        .rd_valid     (e_valid),
        .rd_data      (e_data),
        .rd_ready     (e_ready),
        .count       ()
    );

endmodule : gaxi_data_collect
