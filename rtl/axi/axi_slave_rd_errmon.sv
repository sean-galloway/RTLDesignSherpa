`timescale 1ns / 1ps

module axi_slave_rd_errmon
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AR       = 1000,  // Read address channel timeout
    parameter int TIMEOUT_R        = 1000,  // Read data channel timeout

    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH = 2
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // AXI interface to monitor
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]  m_axi_araddr,
    input  logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    input  logic [AXI_ID_WIDTH-1:0]    m_axi_rid,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rvalid,
    input  logic                       m_axi_rready,
    input  logic                       m_axi_rlast,

    // Error outputs FIFO interface
    output logic                       error_valid,
    input  logic                       error_ready,
    output logic [3:0]                 error_type,    // Error type flags (bit0: AR timeout, bit1: R timeout, bit2: response error)
    output logic [AXI_ADDR_WIDTH-1:0]  error_addr,    // Address associated with error
    output logic [AXI_ID_WIDTH-1:0]    error_id       // ID associated with error
);

    // Error type definitions
    localparam AR_TIMEOUT = 4'b0001;  // Bit 0: Address Read timeout
    localparam R_TIMEOUT  = 4'b0010;  // Bit 1: Data Read timeout
    localparam R_ERROR    = 4'b0100;  // Bit 2: Read response error (SLVERR, DECERR)

    // State definitions for transaction tracking
    typedef enum logic [1:0] {
        IDLE        = 2'b00,
        AR_ACTIVE   = 2'b01,
        R_ACTIVE    = 2'b10,
        R_COMPLETE  = 2'b11
    } rd_state_t;

    // Transaction tracking structures
    typedef struct packed {
        logic [AXI_ID_WIDTH-1:0]    id;
        logic [AXI_ADDR_WIDTH-1:0]  addr;
        logic [31:0]                ar_timer;
        logic [31:0]                r_timer;
        rd_state_t                  state;
    } rd_trans_t;

    // Transaction tracking FIFO depth (should match max outstanding transactions)
    localparam TRANS_FIFO_DEPTH = 8;

    // Error information FIFO
    typedef struct packed {
        logic [3:0]                 type;
        logic [AXI_ADDR_WIDTH-1:0]  addr;
        logic [AXI_ID_WIDTH-1:0]    id;
    } error_info_t;

    // Tracking registers for active transactions
    rd_trans_t rd_trans_list [TRANS_FIFO_DEPTH-1:0];
    logic [$clog2(TRANS_FIFO_DEPTH)-1:0] rd_trans_count;

    // Error FIFO
    error_info_t error_fifo [ERROR_FIFO_DEPTH-1:0];
    logic [$clog2(ERROR_FIFO_DEPTH):0] error_fifo_count;
    logic [$clog2(ERROR_FIFO_DEPTH)-1:0] error_fifo_wr_ptr;
    logic [$clog2(ERROR_FIFO_DEPTH)-1:0] error_fifo_rd_ptr;

    // Internal error signals
    logic int_error_valid;
    logic [3:0] int_error_type;
    logic [AXI_ADDR_WIDTH-1:0] int_error_addr;
    logic [AXI_ID_WIDTH-1:0] int_error_id;

    // Flow control
    logic error_fifo_full;
    logic error_fifo_empty;

    // Transaction tracking logic
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            // Reset all transaction tracking
            for (int i = 0; i < TRANS_FIFO_DEPTH; i++) begin
                rd_trans_list[i].id <= '0;
                rd_trans_list[i].addr <= '0;
                rd_trans_list[i].ar_timer <= '0;
                rd_trans_list[i].r_timer <= '0;
                rd_trans_list[i].state <= IDLE;
            end
            rd_trans_count <= '0;
            int_error_valid <= 1'b0;
            int_error_type <= '0;
            int_error_addr <= '0;
            int_error_id <= '0;
        end else begin
            // Transaction Tracking Logic
            
            // Clear error signal by default
            int_error_valid <= 1'b0;
            
            // AR Channel monitoring: Add new transactions
            if (m_axi_arvalid && m_axi_arready) begin
                // Record new transaction
                if (rd_trans_count < TRANS_FIFO_DEPTH) begin
                    rd_trans_list[rd_trans_count].id <= m_axi_arid;
                    rd_trans_list[rd_trans_count].addr <= m_axi_araddr;
                    rd_trans_list[rd_trans_count].ar_timer <= '0;
                    rd_trans_list[rd_trans_count].r_timer <= '0;
                    rd_trans_list[rd_trans_count].state <= AR_ACTIVE;
                    rd_trans_count <= rd_trans_count + 1;
                end
            end
            
            // R Channel monitoring: Handle read responses
            if (m_axi_rvalid && m_axi_rready) begin
                for (int i = 0; i < TRANS_FIFO_DEPTH; i++) begin
                    if (rd_trans_list[i].state == AR_ACTIVE && rd_trans_list[i].id == m_axi_rid) begin
                        // Update state for this transaction
                        rd_trans_list[i].state <= m_axi_rlast ? R_COMPLETE : R_ACTIVE;
                        rd_trans_list[i].r_timer <= '0;
                        
                        // Check for response errors
                        if (m_axi_rresp != 2'b00) begin
                            // SLVERR or DECERR detected
                            int_error_valid <= 1'b1;
                            int_error_type <= R_ERROR;
                            int_error_addr <= rd_trans_list[i].addr;
                            int_error_id <= rd_trans_list[i].id;
                        end
                    end else if (rd_trans_list[i].state == R_ACTIVE && rd_trans_list[i].id == m_axi_rid) begin
                        // Continued burst transaction
                        rd_trans_list[i].state <= m_axi_rlast ? R_COMPLETE : R_ACTIVE;
                        rd_trans_list[i].r_timer <= '0;
                        
                        // Check for response errors
                        if (m_axi_rresp != 2'b00) begin
                            // SLVERR or DECERR detected
                            int_error_valid <= 1'b1;
                            int_error_type <= R_ERROR;
                            int_error_addr <= rd_trans_list[i].addr;
                            int_error_id <= rd_trans_list[i].id;
                        end
                    end
                end
            end
            
            // Cleanup completed transactions
            for (int i = 0; i < TRANS_FIFO_DEPTH; i++) begin
                if (rd_trans_list[i].state == R_COMPLETE) begin
                    // Remove this transaction by shifting all entries down
                    for (int j = i; j < TRANS_FIFO_DEPTH-1; j++) begin
                        rd_trans_list[j] <= rd_trans_list[j+1];
                    end
                    // Clear the last entry
                    rd_trans_list[TRANS_FIFO_DEPTH-1].state <= IDLE;
                    // Decrement count
                    rd_trans_count <= rd_trans_count - 1;
                end
            end
            
            // Timeout monitoring
            for (int i = 0; i < TRANS_FIFO_DEPTH; i++) begin
                // AR_ACTIVE state timeout check
                if (rd_trans_list[i].state == AR_ACTIVE) begin
                    rd_trans_list[i].ar_timer <= rd_trans_list[i].ar_timer + 1;
                    if (rd_trans_list[i].ar_timer >= TIMEOUT_AR) begin
                        // AR timeout detected
                        int_error_valid <= 1'b1;
                        int_error_type <= AR_TIMEOUT;
                        int_error_addr <= rd_trans_list[i].addr;
                        int_error_id <= rd_trans_list[i].id;
                        // Mark as complete to remove from tracking
                        rd_trans_list[i].state <= R_COMPLETE;
                    end
                end
                
                // R_ACTIVE state timeout check
                if (rd_trans_list[i].state == R_ACTIVE) begin
                    rd_trans_list[i].r_timer <= rd_trans_list[i].r_timer + 1;
                    if (rd_trans_list[i].r_timer >= TIMEOUT_R) begin
                        // R timeout detected
                        int_error_valid <= 1'b1;
                        int_error_type <= R_TIMEOUT;
                        int_error_addr <= rd_trans_list[i].addr;
                        int_error_id <= rd_trans_list[i].id;
                        // Mark as complete to remove from tracking
                        rd_trans_list[i].state <= R_COMPLETE;
                    end
                end
            end
        end
    end

    // Error FIFO management
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            error_fifo_count <= '0;
            error_fifo_wr_ptr <= '0;
            error_fifo_rd_ptr <= '0;
            error_valid <= 1'b0;
            error_type <= '0;
            error_addr <= '0;
            error_id <= '0;
        end else begin
            // Write to FIFO when error detected and FIFO not full
            if (int_error_valid && !error_fifo_full) begin
                error_fifo[error_fifo_wr_ptr].type <= int_error_type;
                error_fifo[error_fifo_wr_ptr].addr <= int_error_addr;
                error_fifo[error_fifo_wr_ptr].id <= int_error_id;
                error_fifo_wr_ptr <= (error_fifo_wr_ptr + 1) % ERROR_FIFO_DEPTH;
                error_fifo_count <= error_fifo_count + 1;
            end
            
            // Read from FIFO when consumer ready and FIFO not empty
            if (error_valid && error_ready) begin
                error_valid <= 1'b0;
                error_fifo_rd_ptr <= (error_fifo_rd_ptr + 1) % ERROR_FIFO_DEPTH;
                error_fifo_count <= error_fifo_count - 1;
            end
            
            // Present next error if available and not already presenting one
            if (!error_valid && !error_fifo_empty) begin
                error_valid <= 1'b1;
                error_type <= error_fifo[error_fifo_rd_ptr].type;
                error_addr <= error_fifo[error_fifo_rd_ptr].addr;
                error_id <= error_fifo[error_fifo_rd_ptr].id;
            end
        end
    end

    // FIFO status tracking
    assign error_fifo_full = (error_fifo_count == ERROR_FIFO_DEPTH);
    assign error_fifo_empty = (error_fifo_count == 0);

endmodule : axi_slave_rd_errmon
