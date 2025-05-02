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

    // Alignment mask signal (12-bit)
    input  logic [11:0] alignment_mask,

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

    // Block ready from the errmon
    input  logic                       block_ready,

    // Slave AXI Interface
    // Read address channel (AR)
    input  logic [IW-1:0]              fub_arid,
    input  logic [AW-1:0]              fub_araddr,
    input  logic [7:0]                 fub_arlen,
    input  logic [2:0]                 fub_arsize,
    input  logic [1:0]                 fub_arburst,
    input  logic                       fub_arlock,
    input  logic [3:0]                 fub_arcache,
    input  logic [2:0]                 fub_arprot,
    input  logic [3:0]                 fub_arqos,
    input  logic [3:0]                 fub_arregion,
    input  logic [UW-1:0]              fub_aruser,
    input  logic                       fub_arvalid,
    output logic                       fub_arready,

    // Read data channel (R)
    output logic [IW-1:0]              fub_rid,
    output logic [DW-1:0]              fub_rdata,
    output logic [1:0]                 fub_rresp,
    output logic                       fub_rlast,
    output logic [UW-1:0]              fub_ruser,
    output logic                       fub_rvalid,
    input  logic                       fub_rready,

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

    //===========================================================================
    // Internal wires and registers
    //===========================================================================

    // Transaction control signals
    logic [AW-1:0]  r_next_addr;
    logic [7:0]     r_remaining_len;
    logic [7:0]     r_current_len;   // Length for current split

    // Split tracking
    logic [7:0]     r_num_splits;

    //===========================================================================
    // Transaction Splitting Logic - All combinational calculations
    //===========================================================================

    // Select current address based on splitting state
    logic [AW-1:0]  w_current_addr;
    logic [7:0]     w_current_len;

    assign w_current_addr = (r_split_state != IDLE) ? r_next_addr : fub_araddr;
    assign w_current_len = (r_split_state != IDLE) ? r_remaining_len : fub_arlen;

    // Create boundary mask based on alignment_mask
    logic [AW-1:0] w_boundary_mask;
    assign w_boundary_mask = {{(AW-12){1'b0}}, alignment_mask};

    // Calculate end address for current transaction
    logic [AW-1:0] w_end_addr;
    assign w_end_addr = w_current_addr + (({24'b0, w_current_len} + 1) << fub_arsize) - 1;

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
                            8'(((w_dist_to_boundary >> fub_arsize) - 1)) :
                            w_current_len;

    // New split detection signal
    logic w_new_split_needed;
    assign w_new_split_needed = fub_arvalid && (r_split_state == IDLE) && w_split_required;

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
            r_split_state <= IDLE;
            r_next_addr <= '0;
            r_remaining_len <= '0;
            r_current_len <= '0;
            r_num_splits <= 8'd1;
        end else begin

            // State machine for split handling
            casez (r_split_state)
                IDLE: begin
                    r_num_splits <= 8'd1;
                    // Check for new split transaction
                    if (w_new_split_needed && m_axi_arready) begin
                        // Start new split
                        r_split_state <= SPLITTING;
                        r_next_addr <= w_curr_boundary;
                        r_remaining_len <= fub_arlen - w_split_arlen;
                        r_current_len <= w_split_arlen;
                        r_num_splits <= 8'd2; // Initial transaction + first split
                    end
                end

                SPLITTING: begin
                    // Process ongoing splits
                    if (m_axi_arready && m_axi_arvalid) begin
                        if (w_split_required) begin
                            // More splits needed
                            r_next_addr <= w_curr_boundary;
                            r_remaining_len <= r_remaining_len - w_split_arlen;
                            r_current_len <= w_split_arlen;
                            r_num_splits <= r_num_splits + 8'd1;
                        end else begin
                            // This is the last split
                            r_split_state <= LAST_SPLIT;
                            r_current_len <= r_remaining_len;
                        end
                    end
                end

                LAST_SPLIT: begin
                    // Wait for the last split to complete
                    if (fub_arvalid && fub_arready) begin
                        r_split_state <= IDLE;
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
        m_axi_arid = fub_arid;
        m_axi_arsize = fub_arsize;
        m_axi_arburst = fub_arburst;
        m_axi_arlock = fub_arlock;
        m_axi_arcache = fub_arcache;
        m_axi_arprot = fub_arprot;
        m_axi_arqos = fub_arqos;
        m_axi_arregion = fub_arregion;
        m_axi_aruser = fub_aruser;

        // Control valid signal based on state
        if (r_split_state == IDLE) begin
            // Pass through slave valid for initial transaction
            m_axi_arvalid = fub_arvalid;
        end else begin
            // For split transactions, always assert valid
            m_axi_arvalid = 1'b1;
        end
    end

    // AR Channel - Slave side
    assign fub_arready = (w_no_split_in_progress || w_final_split_complete)
                            && m_axi_arready && !block_ready;

    // R Channel - Slave side
    // Pass through all R channel signals
    assign fub_rid = m_axi_rid;
    assign fub_rdata = m_axi_rdata;
    assign fub_rresp = m_axi_rresp;
    assign fub_ruser = m_axi_ruser;
    assign fub_rvalid = m_axi_rvalid;
    assign fub_rlast = m_axi_rlast;  // Let user handle RLAST

    // R Channel - Master side
    assign m_axi_rready = fub_rready;

    //===========================================================================
    // Split information FIFO
    //===========================================================================

    // Pack the split info for the FIFO
    logic [AW+IW+8-1:0] split_fifo_din;
    logic w_split_fifo_valid;
    assign split_fifo_din = {fub_araddr, fub_arid, r_num_splits};
    assign w_split_fifo_valid = (fub_arvalid && fub_arready);

    // Instantiate the FIFO for split information
    gaxi_fifo_sync #(
        .DATA_WIDTH(AW + IW + 8),
        .DEPTH(SPLIT_FIFO_DEPTH),
        .INSTANCE_NAME("SPLIT_FIFO")
    ) inst_split_info_fifo (
        .i_axi_aclk(aclk),
        .i_axi_aresetn(aresetn),
        .i_wr_valid(w_split_fifo_valid),
        .o_wr_ready(),  // Not used
        .i_wr_data(split_fifo_din),
        .i_rd_ready(fub_split_ready),
        .o_rd_valid(fub_split_valid),
        .ow_rd_data({fub_split_addr, fub_split_id, fub_split_cnt}),
        .o_rd_data(),  // Not used
        .ow_count()    // Not used
    );

endmodule : axi_master_rd_splitter
