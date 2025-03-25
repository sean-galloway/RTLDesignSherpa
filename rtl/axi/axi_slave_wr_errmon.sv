`timescale 1ns / 1ps

module axi_slave_wr_errmon
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AW       = 1000,  // Write address channel timeout
    parameter int TIMEOUT_W        = 1000,  // Write data channel timeout
    parameter int TIMEOUT_B        = 1000,  // Write response channel timeout

    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH = 2
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // AXI interface to monitor
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]  m_axi_awaddr,
    input  logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    input  logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,
    input  logic                       m_axi_wlast,

    input  logic [AXI_ID_WIDTH-1:0]    m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic                       m_axi_bvalid,
    input  logic                       m_axi_bready,

    // Error outputs FIFO interface
    output logic                       error_valid,
    input  logic                       error_ready,
    output logic [3:0]                 error_type,    // Error type flags (bit0: AW timeout, bit1: W timeout, bit2: B timeout, bit3: response error)
    output logic [AXI_ADDR_WIDTH-1:0]  error_addr,    // Address associated with error
    output logic [AXI_ID_WIDTH-1:0]    error_id       // ID associated with error
);

    // Error type definitions
    localparam AW_TIMEOUT = 4'b0001;  // Bit 0: Address Write timeout
    localparam W_TIMEOUT  = 4'b0010;  // Bit 1: Data Write timeout
    localparam B_TIMEOUT  = 4'b0100;  // Bit 2: Response timeout
    localparam B_ERROR    = 4'b1000;  // Bit 3: Write response error (SLVERR, DECERR)

    // State definitions for transaction tracking
    typedef enum logic [2:0] {
        IDLE        = 3'b000,
        AW_ACTIVE   = 3'b001,
        W_ACTIVE    = 3'b010,
        AW_W_ACTIVE = 3'b011,
        B_WAIT      = 3'b100,
        B_COMPLETE  = 3'b101
    } wr_state_t;

    // Transaction tracking structures
    typedef struct packed {
        logic [AXI_ID_WIDTH-1:0]    id;
        logic [AXI_ADDR_WIDTH-1:0]  addr;
        logic [31:0]                aw_timer;
        logic [31:0]                w_timer;
        logic [31:0]                b_timer;
        logic                       w_last_seen;
        wr_state_t                  state;
    } wr_trans_t;

    // Transaction tracking FIFO depth (should match max outstanding transactions)
    localparam TRANS_FIFO_DEPTH = 8;

    // Error information FIFO
    typedef struct packed {
        logic [3:0]                 type;
        logic [AXI_ADDR_WIDTH-1:0]  addr;
        logic [AXI_ID_WIDTH-1:0]    id;
    } error_info_t;

    // Tracking registers for active transactions
    wr_trans_t wr_trans_list [TRANS_FIFO_DEPTH-1:0];
    logic [$clog2(TRANS_FIFO_DEPTH)-1:0] wr_trans_count;

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
                wr_trans_list[i].id <= '0;
                wr_trans_list[i].addr <= '0;
                wr_trans_list[i].aw_timer <= '0;
                wr_trans_list[i].w_timer <= '0;
                wr_trans_list[i].b_timer <= '0;
                wr_trans_list[i].w_last_seen <= 1'b0;
                wr_trans_list[i].state <= IDLE;
            end
            wr_trans_count <= '0;
            int_error_valid <= 1'b0;
            int_error_type <= '0;
            int_error_addr <= '0;
            int_error_id <= '0;
        end else begin
            // Transaction Tracking Logic
            
            // Clear error signal by default
            int_error_valid <= 1'b0;
            
            // AW Channel monitoring: Add new transactions
            if (m_axi_awvalid && m_axi_awready) begin
                logic transaction_added = 1'b0;
                
                // Check if there's already an active W channel waiting for AW
                for (int i = 0; i < TRANS_FIFO_DEPTH; i++) begin
                    if (wr_trans_list[i].state == W_ACTIVE && wr_trans_list[i].id == m_axi_awid) begin
                        // Match found, update the transaction
                        wr_trans_list[i].addr <= m_axi_awaddr;
                        wr_trans_list[i].aw_timer <= '0;
                        wr_trans_list[i].state <= AW_W_ACTIVE;
                        transaction_added = 1'b1;
                        break;
                    end
                end
                
                // If no matching W transaction found, add new AW transaction
                if (!transaction_added && wr_trans_count < TRANS_FIFO_DEPTH) begin
                    wr_trans_list[wr_trans_count].id <= m_axi_awid;
                    wr_trans_list[wr_trans_count].addr <= m_axi_awaddr;
                    wr_trans_list[wr_trans_count].aw_timer <= '0;
                    wr_trans_list[wr_trans_count].w_timer <= '0;
                    wr_trans_list[wr_trans_count].b_timer <= '0;
                    wr_trans_list[wr_trans_count].w_last_seen <= 1'b0;
                    wr_trans_list[wr_trans_count].state <= AW_ACTIVE;
                    wr_trans_count <= wr_trans_count + 1;
                end
            end
            
            // W Channel monitoring: Track write data beats
            if (m_axi_wvalid && m_axi_wready) begin
                logic transaction_found = 1'b0;
                
                // First, try to find a matching AW transaction
                for (int i = 0; i < TRANS_FIFO_DEPTH; i++) begin
                    if (wr_trans_list[i].state == AW_ACTIVE) begin
                        // Add write data to this transaction
                        wr_trans_list[i].w_timer <= '0;
                        wr_trans_list[i].w_last_seen <= m_axi_wlast;
                        wr_trans_list[i].state <= m_axi_wlast ? B_WAIT : AW_W_ACTIVE;
                        transaction_found = 1'b1;
                        break;
                    end
                end
                
                // If no AW transaction found, create a new W transaction 
                if (!transaction_found && wr_trans_count < TRANS_FIFO_DEPTH) begin
                    // This is a data-before-address situation
                    wr_trans_list[wr_trans_count].id <= '0; // ID will be filled when AW arrives
                    wr_trans_list[wr_trans_count].addr <= '0; // Addr will be filled when AW arrives
                    wr_trans_list[wr_trans_count].aw_timer <= '0;
                    wr_trans_list[wr_trans_count].w_timer <= '0;
                    wr_trans_list[wr_trans_count].b_timer <= '0;
                    wr_trans_list[wr_trans_count].w_last_seen <= m_axi_wlast;
                    wr_trans_list[wr_trans_count].state <= W_ACTIVE;
                    wr_trans_count <= wr_trans_count + 1;
                end
                
                // For active AW+W transactions, check for wlast
                for (int i = 0; i < TRANS_FIFO_DEPTH; i++) begin
                    if (wr_trans_list[i].state == AW_W_ACTIVE) begin
                        wr_trans_list[i].w_timer <= '0;
                        if (m_axi_wlast) begin
                            wr_trans_list[i].w_last_seen <= 1'b1;
                            wr_trans_list[i].state <= B_WAIT;
                            wr_trans_list[i].b_timer <= '0;
                        end
                    end
                end
            end
            
            // B Channel monitoring: Handle write responses
            if (m_axi_bvalid && m_axi_bready) begin
                for (int i = 0; i < TRANS_FIFO_DEPTH; i++) begin
                    if ((wr_trans_list[i].state == B_WAIT || wr_trans_list[i].state == AW_W_ACTIVE) && 
                        wr_trans_list[i].id == m_axi_bid) begin
                        // Mark this transaction as complete
                        wr_trans_list[i].state <= B_COMPLETE;
                        
                        // Check for response errors
                        if (m_axi_bresp != 2'b00) begin
                            // SLVERR or DECERR detected
                            int_error_valid <= 1'b1;
                            int_error_type <= B_ERROR;
                            int_error_addr <= wr_trans_list[i].addr;
                            int_error_id <= wr_trans_list[i].id;
                        end
                    end
                end
            end
            
            // Cleanup completed transactions
            for (int i = 0; i < TRANS_FIFO_DEPTH; i++) begin
                if (wr_trans_list[i].state == B_COMPLETE) begin
                    // Remove this transaction by shifting all entries down
                    for (int j = i; j < TRANS_FIFO_DEPTH-1; j++) begin
                        wr_trans_list[j] <= wr_trans_list[j+1];
                    end
                    // Clear the last entry
                    wr_trans_list[TRANS_FIFO_DEPTH-1].state <= IDLE;
                    // Decrement count
                    wr_trans_count <= wr_trans_count - 1;
                end
            end
            
            // Timeout monitoring for different states
            for (int i = 0; i < TRANS_FIFO_DEPTH; i++) begin
                // AW_ACTIVE state timeout check
                if (wr_trans_list[i].state == AW_ACTIVE) begin
                    wr_trans_list[i].aw_timer <= wr_trans_list[i].aw_timer + 1;
                    if (wr_trans_list[i].aw_timer >= TIMEOUT_AW) begin
                        // AW timeout detected (waiting for W)
                        int_error_valid <= 1'b1;
                        int_error_type <= AW_TIMEOUT;
                        int_error_addr <= wr_trans_list[i].addr;
                        int_error_id <= wr_trans_list[i].id;
                        // Mark as complete to remove from tracking
                        wr_trans_list[i].state <= B_COMPLETE;
                    end
                end
                
                // W_ACTIVE state timeout check
                if (wr_trans_list[i].state == W_ACTIVE) begin
                    wr_trans_list[i].w_timer <= wr_trans_list[i].w_timer + 1;
                    if (wr_trans_list[i].w_timer >= TIMEOUT_W) begin
                        // W timeout detected (waiting for AW)
                        int_error_valid <= 1'b1;
                        int_error_type <= W_TIMEOUT;
                        int_error_addr <= wr_trans_list[i].addr; // Will be 0
                        int_error_id <= wr_trans_list[i].id; // Will be 0
                        // Mark as complete to remove from tracking
                        wr_trans_list[i].state <= B_COMPLETE;
                    end
                end
                
                // AW_W_ACTIVE state timeout check
                if (wr_trans_list[i].state == AW_W_ACTIVE) begin
                    wr_trans_list[i].w_timer <= wr_trans_list[i].w_timer + 1;
                    if (wr_trans_list[i].w_timer >= TIMEOUT_W) begin
                        // W timeout detected (waiting for wlast)
                        int_error_valid <= 1'b1;
                        int_error_type <= W_TIMEOUT;
                        int_error_addr <= wr_trans_list[i].addr;
                        int_error_id <= wr_trans_list[i].id;
                        // Mark as complete to remove from tracking
                        wr_trans_list[i].state <= B_COMPLETE;
                    end
                end
                
                // B_WAIT state timeout check
                if (wr_trans_list[i].state == B_WAIT) begin
                    wr_trans_list[i].b_timer <= wr_trans_list[i].b_timer + 1;
                    if (wr_trans_list[i].b_timer >= TIMEOUT_B) begin
                        // B timeout detected
                        int_error_valid <= 1'b1;
                        int_error_type <= B_TIMEOUT;
                        int_error_addr <= wr_trans_list[i].addr;
                        int_error_id <= wr_trans_list[i].id;
                        // Mark as complete to remove from tracking
                        wr_trans_list[i].state <= B_COMPLETE;
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

endmodule : axi_slave_wr_errmon