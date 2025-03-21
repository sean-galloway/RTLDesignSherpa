`timescale 1ns / 1ps

module axi_master_rd_splitter
#(
    // Alignment parameters
    parameter int ALIGNMENT_WIDTH = 3,  // 0:8b, 1:16b, 2:32b, 3:64b, 4:128b, 5:256b, 6:512b

    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Alignment boundary signal (12-bit)
    input  logic [11:0] alignment_boundary,

    // Master AXI Interface
    // Read address channel (AR)
    output logic [AXI_ID_WIDTH-1:0]    m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]  m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0]  m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0]  m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [AXI_USER_WIDTH-1:0]  m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

    // Slave AXI Interface
    // Read address channel (AR)
    input  logic [AXI_ID_WIDTH-1:0]    s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]  s_axi_araddr,
    input  logic [7:0]                 s_axi_arlen,
    input  logic [2:0]                 s_axi_arsize,
    input  logic [1:0]                 s_axi_arburst,
    input  logic                       s_axi_arlock,
    input  logic [3:0]                 s_axi_arcache,
    input  logic [2:0]                 s_axi_arprot,
    input  logic [3:0]                 s_axi_arqos,
    input  logic [3:0]                 s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]  s_axi_aruser,
    input  logic                       s_axi_arvalid,
    output logic                       s_axi_arready,

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]    s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]  s_axi_rdata,
    output logic [1:0]                 s_axi_rresp,
    output logic                       s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]  s_axi_ruser,
    output logic                       s_axi_rvalid,
    input  logic                       s_axi_rready,

    // Output split information
    output logic [AXI_ADDR_WIDTH-1:0]  s_split_addr,
    output logic [AXI_ID_WIDTH-1:0]    s_split_id,
    output logic [7:0]                 s_split_num_splits,
    output logic                       s_split_valid,

    // Performance metrics
    output logic [31:0]                rd_transaction_count,
    output logic [31:0]                rd_byte_count,
    output logic [31:0]                rd_latency_sum      // Sum of read latencies (cycles)
);

    //===========================================================================
    // Internal wires and registers
    //===========================================================================

    // Transaction control signals
    logic r_splitting_active;
    logic [AXI_ADDR_WIDTH-1:0] r_next_addr;
    logic [7:0] r_remaining_len;
    logic r_is_last_split;
    logic r_split_ongoing;  // New flag to track when a split transaction is in progress

    // Performance tracking
    logic [31:0] r_cycle_counter;
    logic [31:0] r_rd_start_time;
    logic [AXI_ID_WIDTH-1:0] r_curr_id;
    logic r_read_in_progress;

    //===========================================================================
    // Transaction Splitting Logic - All combinational calculations
    //===========================================================================

    // Select current address based on splitting state
    logic [AXI_ADDR_WIDTH-1:0] w_current_addr;
    logic [7:0] w_current_len;

    assign w_current_addr = r_splitting_active ? r_next_addr : s_axi_araddr;
    assign w_current_len = r_splitting_active ? r_remaining_len : s_axi_arlen;

    // Create boundary mask based on alignment_boundary
    logic [AXI_ADDR_WIDTH-1:0] w_boundary_mask;
    assign w_boundary_mask = (1 << alignment_boundary) - 1;

    // Calculate end address for current transaction
    logic [AXI_ADDR_WIDTH-1:0] w_end_addr;
    assign w_end_addr = w_current_addr + ((w_current_len + 1) << s_axi_arsize) - 1;

    // Calculate current boundary address
    logic [AXI_ADDR_WIDTH-1:0] w_curr_boundary;
    assign w_curr_boundary = (w_current_addr & ~w_boundary_mask) + (1 << alignment_boundary);

    // Check if transaction crosses boundary - KEY SIGNAL
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

    //===========================================================================
    // State Management
    //===========================================================================

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            // Control signals
            r_splitting_active <= 1'b0;
            r_next_addr <= '0;
            r_remaining_len <= '0;
            r_is_last_split <= 1'b0;
            r_split_ongoing <= 1'b0;

            // Split info port
            s_split_addr <= '0;
            s_split_id <= '0;
            s_split_num_splits <= '0;
            s_split_valid <= 1'b0;

            // Performance counters
            rd_transaction_count <= '0;
            rd_byte_count <= '0;
            rd_latency_sum <= '0;
            r_cycle_counter <= '0;
            r_rd_start_time <= '0;
            r_curr_id <= '0;
            r_read_in_progress <= 1'b0;
        end else begin
            // Clear s_split_valid by default (will be set if needed)
            s_split_valid <= 1'b0;

            // Always increment cycle counter
            r_cycle_counter <= r_cycle_counter + 1;

            // Update transaction counter when AR transaction occurs
            if (m_axi_arvalid && m_axi_arready) begin
                rd_transaction_count <= rd_transaction_count + 1;
                rd_byte_count <= rd_byte_count + ((m_axi_arlen + 1) << m_axi_arsize);

                // Record start time for non-split transactions or first transaction in a split
                if (!r_read_in_progress) begin
                    r_rd_start_time <= r_cycle_counter;
                    r_curr_id <= m_axi_arid;
                    r_read_in_progress <= 1'b1;
                end
            end

            // Handle initial transaction acceptance from slave
            if (s_axi_arvalid && s_axi_arready) begin
                // Check if splitting is needed
                if (w_split_required) begin
                    // Set up split state
                    r_splitting_active <= 1'b1;
                    r_next_addr <= w_curr_boundary;
                    r_remaining_len <= s_axi_arlen - w_split_arlen;
                    r_is_last_split <= 1'b0;
                    r_split_ongoing <= 1'b1;

                    // Output information to split port
                    s_split_addr <= s_axi_araddr;
                    s_split_id <= s_axi_arid;
                    s_split_num_splits <= 8'd1; // Start with 1 (will increment)
                    s_split_valid <= 1'b1;
                end else begin
                    // No split needed
                    r_splitting_active <= 1'b0;
                    r_split_ongoing <= 1'b0;
                end
            end

            // Handle split transactions in progress
            if (r_splitting_active && m_axi_arready && m_axi_arvalid) begin
                // Increment split count for each split sent
                s_split_num_splits <= s_split_num_splits + 8'd1;

                // Check if more splits are needed
                if (w_split_required) begin
                    // Update for next split
                    r_next_addr <= w_curr_boundary;
                    r_remaining_len <= r_remaining_len - w_split_arlen;
                    r_is_last_split <= 1'b0;
                end else begin
                    // This will be the last split
                    r_is_last_split <= 1'b1;

                    // Keep splitting active until the handshake completes
                    if (m_axi_arready) begin
                        r_splitting_active <= 1'b0;
                        // Leave r_split_ongoing set until all responses are processed
                    end
                end
            end

            // Track completion for performance metrics
            if (m_axi_rvalid && m_axi_rready && m_axi_rlast) begin
                // For the last response (in case of split transactions) or for non-split transactions
                if ((r_split_ongoing && r_is_last_split) || !r_split_ongoing) begin
                    // Check if this is for our transaction
                    if (m_axi_rid == r_curr_id) begin
                        // Update latency metrics
                        rd_latency_sum <= rd_latency_sum + (r_cycle_counter - r_rd_start_time);
                        r_read_in_progress <= 1'b0;

                        // Clear split state when last response received
                        if (r_split_ongoing) begin
                            r_split_ongoing <= 1'b0;
                        end
                    end
                end
            end
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
        if (!r_splitting_active) begin
            // Pass through slave valid for initial transaction
            m_axi_arvalid = s_axi_arvalid;
        end else begin
            // For split transactions, always assert valid
            m_axi_arvalid = 1'b1;
        end
    end

    // AR Channel - Slave side
    // For non-split transactions, pass through m_axi_arready directly
    // For split transactions, only assert s_axi_arready after the last split is sent
    assign s_axi_arready = ((!w_split_required) || (r_is_last_split)) && m_axi_arready;

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

endmodule : axi_master_rd_splitter
