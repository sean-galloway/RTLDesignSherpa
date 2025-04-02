`timescale 1ns / 1ps

module axi_master_wr_splitter
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    // FIFO depth
    parameter int SPLIT_FIFO_DEPTH  = 4,
    // short names
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Alignment mask signal (12-bit)
    input  logic [11:0] alignment_mask,

    // Master AXI Interface
    // Write address channel (AW)
    output logic [IW-1:0]              m_axi_awid,
    output logic [AW-1:0]              m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // Write data channel (W)
    output logic [DW-1:0]              m_axi_wdata,
    output logic [DW/8-1:0]            m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    // Slave AXI Interface
    // Write address channel (AW)
    input  logic [IW-1:0]              fub_awid,
    input  logic [AW-1:0]              fub_awaddr,
    input  logic [7:0]                 fub_awlen,
    input  logic [2:0]                 fub_awsize,
    input  logic [1:0]                 fub_awburst,
    input  logic                       fub_awlock,
    input  logic [3:0]                 fub_awcache,
    input  logic [2:0]                 fub_awprot,
    input  logic [3:0]                 fub_awqos,
    input  logic [3:0]                 fub_awregion,
    input  logic [UW-1:0]              fub_awuser,
    input  logic                       fub_awvalid,
    output logic                       fub_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              fub_wdata,
    input  logic [DW/8-1:0]            fub_wstrb,
    input  logic                       fub_wlast,
    input  logic [UW-1:0]              fub_wuser,
    input  logic                       fub_wvalid,
    output logic                       fub_wready,

    // Write response channel (B)
    output logic [IW-1:0]              fub_bid,
    output logic [1:0]                 fub_bresp,
    output logic [UW-1:0]              fub_buser,
    output logic                       fub_bvalid,
    input  logic                       fub_bready,

    // Output split information
    output logic [AW-1:0]              fub_split_addr,
    output logic [IW-1:0]              fub_split_id,
    output logic [7:0]                 fub_split_cnt,
    output logic                       fub_split_valid,
    input  logic                       fub_split_ready
);

    //===========================================================================
    // State definitions
    //===========================================================================
    typedef enum logic [2:0] {
        IDLE       = 3'b001,
        SPLITTING  = 3'b010,
        LAST_SPLIT = 3'b100
    } split_state_t;

    split_state_t r_split_state;
    split_state_t r_w_state;      // State for data channel

    //===========================================================================
    // Internal wires and registers
    //===========================================================================

    // Transaction control signals
    logic [AW-1:0]  r_next_addr;
    logic [7:0]     r_remaining_len;
    logic [7:0]     r_current_len;   // Length for current split
    logic [7:0]     r_data_counter;  // Track data beats
    logic           r_need_wlast;    // Flag for last beat generation

    // Split tracking
    logic [AW-1:0]  r_split_addr;
    logic [IW-1:0]  r_split_id;
    logic [7:0]     r_num_splits;
    logic           r_split_fifo_valid;

    //===========================================================================
    // Transaction Splitting Logic - All combinational calculations
    //===========================================================================

    // Select current address based on splitting state
    logic [AW-1:0]  w_current_addr;
    logic [7:0]     w_current_len;

    assign w_current_addr = (r_split_state != IDLE) ? r_next_addr : fub_awaddr;
    assign w_current_len = (r_split_state != IDLE) ? r_remaining_len : fub_awlen;

    // Create boundary mask based on alignment_mask
    logic [AW-1:0] w_boundary_mask;
    assign w_boundary_mask = alignment_mask;

    // Calculate end address for current transaction
    logic [AW-1:0] w_end_addr;
    assign w_end_addr = w_current_addr + ((w_current_len + 1) << fub_awsize) - 1;

    // Calculate current boundary address
    logic [AW-1:0] w_curr_boundary;
    assign w_curr_boundary = (w_current_addr & ~w_boundary_mask) + (w_boundary_mask + 1);

    // Check if transaction crosses boundary
    logic w_split_required;
    assign w_split_required = ((w_current_addr & ~w_boundary_mask) !=
                                (w_end_addr & ~w_boundary_mask));

    // Calculate distance to boundary in bytes
    logic [31:0] w_dist_to_boundary;
    assign w_dist_to_boundary = w_curr_boundary - w_current_addr;

    // Calculate max beats that fit before boundary
    logic [7:0] w_split_awlen;
    assign w_split_awlen = w_split_required ?
                            ((w_dist_to_boundary >> fub_awsize) - 1) :
                            w_current_len;

    // New split detection signal
    logic w_new_split_needed;
    assign w_new_split_needed = fub_awvalid && (r_split_state == IDLE) && w_split_required;

    // Ready signal control logic
    logic w_no_split_in_progress;
    logic w_final_split_complete;

    assign w_no_split_in_progress = !w_split_required && (r_split_state == IDLE);
    assign w_final_split_complete = (r_split_state == LAST_SPLIT);

    //===========================================================================
    // State Management
    //===========================================================================

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            // Reset all state
            r_split_state <= IDLE;
            r_w_state <= IDLE;
            r_next_addr <= '0;
            r_remaining_len <= '0;
            r_current_len <= '0;
            r_data_counter <= '0;
            r_need_wlast <= 1'b0;

            // Split info port
            r_split_addr <= '0;
            r_split_id <= '0;
            r_num_splits <= '0;
            r_split_fifo_valid <= 1'b0;

        end else begin
            // Clear r_split_fifo_valid by default (will be set if needed)
            r_split_fifo_valid <= 1'b0;

            // Handle transaction acceptance - this happens when handshaking with slave side
            if (fub_awvalid && fub_awready) begin
                // Always record split info for FIFO
                r_split_addr <= fub_awaddr;
                r_split_id <= fub_awid;

                // Signal to send info to FIFO
                r_split_fifo_valid <= 1'b1;

                // If no split needed, set data counter for simple passthrough
                if (!w_split_required) begin
                    r_data_counter <= fub_awlen + 1;
                    r_need_wlast <= 1'b0;
                end
            end

            // State machine for address channel split handling
            case (r_split_state)
                IDLE: begin
                    // Check for new split transaction
                    if (w_new_split_needed && m_axi_awready) begin
                        // Start new split
                        r_split_state <= SPLITTING;
                        r_next_addr <= w_curr_boundary;
                        r_remaining_len <= fub_awlen - w_split_awlen;
                        r_num_splits <= 8'd2; // Initial transaction + first split
                        r_current_len <= w_split_awlen;

                        // Setup data counter for this split
                        r_data_counter <= w_split_awlen + 1;
                        r_need_wlast <= 1'b1;

                        // Save request information for FIFO
                        r_split_addr <= fub_awaddr;
                        r_split_id <= fub_awid;
                    end else if (fub_awvalid && fub_awready && !w_split_required) begin
                        // No split needed
                        r_num_splits <= 8'd1;
                        r_split_state <= IDLE;
                    end
                end

                SPLITTING: begin
                    // Process ongoing splits
                    if (m_axi_awready && m_axi_awvalid) begin
                        if (w_split_required) begin
                            // More splits needed
                            r_next_addr <= w_curr_boundary;
                            r_remaining_len <= r_remaining_len - w_split_awlen;
                            r_num_splits <= r_num_splits + 8'd1;
                            r_current_len <= w_split_awlen;

                            // Setup data counter for this split
                            r_data_counter <= w_split_awlen + 1;
                            r_need_wlast <= 1'b1;
                        end else begin
                            // This is the last split
                            r_split_state <= LAST_SPLIT;
                            r_current_len <= r_remaining_len;

                            // Setup data counter for final split
                            r_data_counter <= r_remaining_len + 1;
                            r_need_wlast <= 1'b1;
                        end
                    end
                end

                LAST_SPLIT: begin
                    // Wait for the last split to complete
                    if (m_axi_awready && m_axi_awvalid) begin
                        // Will transition to IDLE when fub_awready asserts
                        r_split_state <= IDLE;
                    end
                end

                default: r_split_state <= IDLE;
            endcase

            // Manage data counter for WLAST generation
            if (m_axi_wvalid && m_axi_wready && r_need_wlast) begin
                if (r_data_counter > 0) begin
                    r_data_counter <= r_data_counter - 1;
                end
            end
        end
    end

    //===========================================================================
    // Data Channel Management - Handles data for ongoing splits
    //===========================================================================

    // Fixed version of WLAST signal
    logic w_modified_wlast;

    // WLAST is generated for split bursts
    assign w_modified_wlast = r_need_wlast ? (r_data_counter == 1) : fub_wlast;

    //===========================================================================
    // AXI Signal Assignments
    //===========================================================================

    // AW Channel - Master side
    always_comb begin
        // Address is always based on the current state
        m_axi_awaddr = w_current_addr;

        // Length is based on whether splitting is needed
        m_axi_awlen = w_split_required ? w_split_awlen : w_current_len;

        // Pass through other AW signals directly
        m_axi_awid = fub_awid;
        m_axi_awsize = fub_awsize;
        m_axi_awburst = fub_awburst;
        m_axi_awlock = fub_awlock;
        m_axi_awcache = fub_awcache;
        m_axi_awprot = fub_awprot;
        m_axi_awqos = fub_awqos;
        m_axi_awregion = fub_awregion;
        m_axi_awuser = fub_awuser;

        // Control valid signal based on state
        if (r_split_state == IDLE) begin
            // Pass through slave valid for initial transaction
            m_axi_awvalid = fub_awvalid;
        end else begin
            // For split transactions, always assert valid
            m_axi_awvalid = 1'b1;
        end
    end

    // AW Channel - Slave side
    assign fub_awready = (w_no_split_in_progress || w_final_split_complete) && m_axi_awready;

    // W Channel
    assign m_axi_wdata = fub_wdata;
    assign m_axi_wstrb = fub_wstrb;
    assign m_axi_wuser = fub_wuser;
    assign m_axi_wlast = w_modified_wlast;
    assign m_axi_wvalid = fub_wvalid;
    assign fub_wready = m_axi_wready;

    // B Channel - passes responses from master to slave
    assign fub_bid = m_axi_bid;
    assign fub_bresp = m_axi_bresp;
    assign fub_buser = m_axi_buser;
    assign fub_bvalid = m_axi_bvalid;
    assign m_axi_bready = fub_bready;

    //===========================================================================
    // Split information FIFO
    //===========================================================================

    // Pack the split info for the FIFO
    logic [AW+IW+8-1:0] split_fifo_din;
    assign split_fifo_din = {r_split_addr, r_split_id, r_num_splits};

    // Instantiate the FIFO for split information
    gaxi_fifo_sync #(
        .DATA_WIDTH(AW + IW + 8),
        .DEPTH(SPLIT_FIFO_DEPTH),
        .INSTANCE_NAME("SPLIT_FIFO")
    ) inst_split_info_fifo (
        .i_axi_aclk(aclk),
        .i_axi_aresetn(aresetn),
        .i_wr_valid(r_split_fifo_valid),
        .o_wr_ready(),  // Not used
        .i_wr_data(split_fifo_din),
        .i_rd_ready(fub_split_ready),
        .o_rd_valid(fub_split_valid),
        .ow_rd_data({fub_split_addr, fub_split_id, fub_split_cnt}),
        .o_rd_data(),  // Not used
        .ow_count()    // Not used
    );

endmodule : axi_master_wr_splitter
