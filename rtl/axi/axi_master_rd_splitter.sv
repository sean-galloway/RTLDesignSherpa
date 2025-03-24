`timescale 1ns / 1ps

module axi_master_rd_splitter
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

    // Alignment boundary signal (12-bit)
    input  logic [11:0] alignment_boundary,

    // Master AXI Interface
    // Read address channel (AR)
    output logic [IW-1:0]              m_axi_arid,
    output logic [AW-1:0]              m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]              m_axi_rid,
    input  logic [DW-1:0]              m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [UW-1:0]              m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

    // Slave AXI Interface
    // Read address channel (AR)
    input  logic [IW-1:0]              s_axi_arid,
    input  logic [AW-1:0]              s_axi_araddr,
    input  logic [7:0]                 s_axi_arlen,
    input  logic [2:0]                 s_axi_arsize,
    input  logic [1:0]                 s_axi_arburst,
    input  logic                       s_axi_arlock,
    input  logic [3:0]                 s_axi_arcache,
    input  logic [2:0]                 s_axi_arprot,
    input  logic [3:0]                 s_axi_arqos,
    input  logic [3:0]                 s_axi_arregion,
    input  logic [UW-1:0]              s_axi_aruser,
    input  logic                       s_axi_arvalid,
    output logic                       s_axi_arready,

    // Read data channel (R)
    output logic [IW-1:0]              s_axi_rid,
    output logic [DW-1:0]              s_axi_rdata,
    output logic [1:0]                 s_axi_rresp,
    output logic                       s_axi_rlast,
    output logic [UW-1:0]              s_axi_ruser,
    output logic                       s_axi_rvalid,
    input  logic                       s_axi_rready,
    input  logic                       s_split_ready,

    // Output split information
    output logic [AW-1:0]              s_split_addr,
    output logic [IW-1:0]              s_split_id,
    output logic [7:0]                 s_split_num_splits,
    output logic                       s_split_valid
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

    //===========================================================================
    // Internal wires and registers
    //===========================================================================

    // Transaction control signals
    logic [AW-1:0]  r_next_addr;
    logic [7:0]     r_remaining_len;

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

    assign w_current_addr = (r_split_state != IDLE) ? r_next_addr : s_axi_araddr;
    assign w_current_len = (r_split_state != IDLE) ? r_remaining_len : s_axi_arlen;

    // Create boundary mask based on alignment_boundary
    logic [AW-1:0] w_boundary_mask;
    assign w_boundary_mask = alignment_boundary;

    // Calculate end address for current transaction
    logic [AW-1:0] w_end_addr;
    assign w_end_addr = w_current_addr + ((w_current_len + 1) << s_axi_arsize) - 1;

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
    logic [7:0] w_split_arlen;
    assign w_split_arlen = w_split_required ?
                            ((w_dist_to_boundary >> s_axi_arsize) - 1) :
                            w_current_len;

    // New split detection signal
    logic w_new_split_needed;
    assign w_new_split_needed = s_axi_arvalid && (r_split_state == IDLE) && w_split_required;

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
            r_next_addr <= '0;
            r_remaining_len <= '0;

            // Split info port
            r_split_addr <= '0;
            r_split_id <= '0;
            r_num_splits <= '0;
            r_split_fifo_valid <= 1'b0;

        end else begin
            // Clear r_split_fifo_valid by default (will be set if needed)
            r_split_fifo_valid <= 1'b0;

            // Handle transaction acceptance - this happens when handshaking with slave side
            if (s_axi_arvalid && s_axi_arready) begin
                // Always record split info for FIFO
                r_split_addr <= s_axi_araddr;
                r_split_id <= s_axi_arid;

                // Signal to send info to FIFO
                r_split_fifo_valid <= 1'b1;

                // Reset state
                r_split_state <= IDLE;
            end

            // State machine for split handling
            case (r_split_state)
                IDLE: begin
                    // Check for new split transaction
                    if (w_new_split_needed && m_axi_arready) begin
                        // Start new split
                        r_split_state <= SPLITTING;
                        r_next_addr <= w_curr_boundary;
                        r_remaining_len <= s_axi_arlen - w_split_arlen;
                        r_num_splits <= 8'd2; // Initial transaction + first split

                        // Save request information for FIFO
                        r_split_addr <= s_axi_araddr;
                        r_split_id <= s_axi_arid;
                    end else if (s_axi_arvalid && s_axi_arready && !w_split_required) begin
                        // No split needed
                        r_num_splits <= 8'd1;
                    end
                end

                SPLITTING: begin
                    // Process ongoing splits
                    if (m_axi_arready && m_axi_arvalid) begin
                        if (w_split_required) begin
                            // More splits needed
                            r_next_addr <= w_curr_boundary;
                            r_remaining_len <= r_remaining_len - w_split_arlen;
                            r_num_splits <= r_num_splits + 8'd1;
                        end else begin
                            // This is the last split
                            r_split_state <= LAST_SPLIT;
                        end
                    end
                end

                LAST_SPLIT: begin
                    // Wait for the last split to complete
                    if (m_axi_arready && m_axi_arvalid) begin
                        // Will transition to IDLE when s_axi_arready asserts
                    end
                end

                default: r_split_state <= IDLE;
            endcase
        end
    end

    //===========================================================================
    // AXI Signal Assignments
    //===========================================================================

    // AR Channel - Master side
    always_comb begin
        // Address is always based on the current state
        m_axi_araddr = w_current_addr;

        // Length is based on whether splitting is needed
        m_axi_arlen = w_split_required ? w_split_arlen : w_current_len;

        // Pass through other AR signals directly
        m_axi_arid = s_axi_arid;
        m_axi_arsize = s_axi_arsize;
        m_axi_arburst = s_axi_arburst;
        m_axi_arlock = s_axi_arlock;
        m_axi_arcache = s_axi_arcache;
        m_axi_arprot = s_axi_arprot;
        m_axi_arqos = s_axi_arqos;
        m_axi_arregion = s_axi_arregion;
        m_axi_aruser = s_axi_aruser;

        // Control valid signal based on state
        if (r_split_state == IDLE) begin
            // Pass through slave valid for initial transaction
            m_axi_arvalid = s_axi_arvalid;
        end else begin
            // For split transactions, always assert valid
            m_axi_arvalid = 1'b1;
        end
    end

    // AR Channel - Slave side
    assign s_axi_arready = (w_no_split_in_progress || w_final_split_complete) && m_axi_arready;

    // R Channel - Slave side
    // Pass through all R channel signals
    assign s_axi_rid = m_axi_rid;
    assign s_axi_rdata = m_axi_rdata;
    assign s_axi_rresp = m_axi_rresp;
    assign s_axi_ruser = m_axi_ruser;
    assign s_axi_rvalid = m_axi_rvalid;
    assign s_axi_rlast = m_axi_rlast;  // Let user handle RLAST

    // R Channel - Master side
    assign m_axi_rready = s_axi_rready;

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
        .i_rd_ready(s_split_ready),
        .o_rd_valid(s_split_valid),
        .ow_rd_data({s_split_addr, s_split_id, s_split_num_splits}),
        .o_rd_data(),  // Not used
        .ow_count()    // Not used
    );

endmodule : axi_master_rd_splitter
