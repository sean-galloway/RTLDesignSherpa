`timescale 1ns / 1ps

module axi_wr_error_monitor
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AW       = 1000,  // Write address channel timeout
    parameter int TIMEOUT_W        = 1000,  // Write data channel timeout
    parameter int TIMEOUT_B        = 1000,  // Write response channel timeout

    // Short params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // AXI Interface to monitor
    // Write address channel (AW)
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]  m_axi_awaddr,
    input  logic [7:0]                 m_axi_awlen,
    input  logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // Write data channel (W)
    input  logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,
    input  logic                       m_axi_wlast,

    // Write response channel (B)
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic                       m_axi_bvalid,
    input  logic                       m_axi_bready,

    // Error outputs
    output logic                       error_timeout_aw,
    output logic                       error_timeout_w,
    output logic                       error_timeout_b,
    output logic                       error_resp_write,  // SLVERR or DECERR on B channel

    // Error address tracking
    output logic [AXI_ADDR_WIDTH-1:0]  error_addr_aw,
    output logic [AXI_ID_WIDTH-1:0]    error_id_aw,

    // Status registers
    output logic [31:0]                error_count_timeout,
    output logic [31:0]                error_count_resp
);

    // Instead of using a struct array, we'll use separate arrays for each field
    logic [2**AXI_ID_WIDTH-1:0]                   aw_transaction_valid;
    logic [2**AXI_ID_WIDTH-1:0][AXI_ID_WIDTH-1:0] aw_transaction_id;
    logic [2**AXI_ID_WIDTH-1:0][AXI_ADDR_WIDTH-1:0] aw_transaction_addr;
    logic [2**AXI_ID_WIDTH-1:0][31:0]             aw_transaction_timer;
    logic [2**AXI_ID_WIDTH-1:0][7:0]              aw_transaction_len;
    logic [2**AXI_ID_WIDTH-1:0]                   aw_data_phase_active;

    // Pending write data tracking (registered)
    logic [31:0] r_w_data_timer;
    logic r_w_data_pending;
    logic r_w_last_received;
    logic [AXI_ID_WIDTH-1:0] r_current_write_id;

    // Pending response tracking (registered)
    logic [31:0] r_b_resp_timer;
    logic r_b_resp_pending;
    logic [AXI_ID_WIDTH-1:0] r_b_pending_id;

    // Error counters (registered)
    logic [31:0] r_timeout_count;
    logic [31:0] r_resp_error_count;

    // Initialize error counters
    initial begin
        r_timeout_count = '0;
        r_resp_error_count = '0;
    end

    // Track AW transactions
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            for (int i = 0; i < 2**AXI_ID_WIDTH; i++) begin
                aw_transaction_valid[i] <= 1'b0;
                aw_transaction_timer[i] <= '0;
                aw_transaction_id[i] <= '0;
                aw_transaction_addr[i] <= '0;
                aw_transaction_len[i] <= '0;
                aw_data_phase_active[i] <= 1'b0;
            end
            error_timeout_aw <= 1'b0;
            error_addr_aw <= '0;
            error_id_aw <= '0;
            r_w_last_received <= 1'b0;
            r_current_write_id <= '0;
        end else begin
            // Reset error flag
            error_timeout_aw <= 1'b0;

            // Process new AW transactions
            if (m_axi_awvalid && m_axi_awready) begin
                aw_transaction_valid[m_axi_awid] <= 1'b1;
                aw_transaction_id[m_axi_awid] <= m_axi_awid;
                aw_transaction_addr[m_axi_awid] <= m_axi_awaddr;
                aw_transaction_len[m_axi_awid] <= m_axi_awlen;
                aw_transaction_timer[m_axi_awid] <= '0;
                aw_data_phase_active[m_axi_awid] <= 1'b1;
                r_current_write_id <= m_axi_awid;
            end

            // Process W data (completion on WLAST)
            if (m_axi_wvalid && m_axi_wready) begin
                if (m_axi_wlast) begin
                    // Mark data phase as complete
                    aw_data_phase_active[r_current_write_id] <= 1'b0;
                    r_w_last_received <= 1'b1;
                    
                    // Start waiting for B response
                    r_b_resp_pending <= 1'b1;
                    r_b_resp_timer <= '0;
                    r_b_pending_id <= r_current_write_id;
                end
            end else begin
                r_w_last_received <= 1'b0;
            end
            
            // Process B responses
            if (m_axi_bvalid && m_axi_bready) begin
                // Clear transaction tracking
                aw_transaction_valid[m_axi_bid] <= 1'b0;
                
                // Clear response pending
                if (r_b_pending_id == m_axi_bid) begin
                    r_b_resp_pending <= 1'b0;
                    r_b_resp_timer <= '0;
                end
            end

            // Update timers and check for timeouts
            for (int i = 0; i < 2**AXI_ID_WIDTH; i++) begin
                if (aw_transaction_valid[i]) begin
                    aw_transaction_timer[i] <= aw_transaction_timer[i] + 1;

                    // Check for timeout on address phase
                    if (aw_transaction_timer[i] >= TIMEOUT_AW && aw_data_phase_active[i]) begin
                        error_timeout_aw <= 1'b1;
                        error_addr_aw <= aw_transaction_addr[i];
                        error_id_aw <= aw_transaction_id[i];
                        r_timeout_count <= r_timeout_count + 1;
                    end
                end
            end
        end
    end

    // Track write data channel for timeouts
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_w_data_pending <= 1'b0;
            r_w_data_timer <= '0;
            error_timeout_w <= 1'b0;
        end else begin
            // Reset error flags
            error_timeout_w <= 1'b0;

            // Start tracking after an address write request is sent
            if (m_axi_awvalid && m_axi_awready) begin
                r_w_data_pending <= 1'b1;
                r_w_data_timer <= '0;
            end

            // Stop tracking after the last write data is sent
            if (m_axi_wvalid && m_axi_wready && m_axi_wlast) begin
                r_w_data_pending <= 1'b0;
                r_w_data_timer <= '0;
            end

            // Update timer and check for timeout
            if (r_w_data_pending) begin
                r_w_data_timer <= r_w_data_timer + 1;

                if (r_w_data_timer >= TIMEOUT_W) begin
                    error_timeout_w <= 1'b1;
                    r_timeout_count <= r_timeout_count + 1;
                end
            end
        end
    end
    
    // Track response channel for timeouts and error responses
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            error_timeout_b <= 1'b0;
            error_resp_write <= 1'b0;
        end else begin
            // Reset error flags
            error_timeout_b <= 1'b0;
            error_resp_write <= 1'b0;
            
            // Check for response timeouts
            if (r_b_resp_pending) begin
                r_b_resp_timer <= r_b_resp_timer + 1;
                
                if (r_b_resp_timer >= TIMEOUT_B) begin
                    error_timeout_b <= 1'b1;
                    r_timeout_count <= r_timeout_count + 1;
                end
            end
            
            // Check for error response
            if (m_axi_bvalid && m_axi_bready && m_axi_bresp != 2'b00) begin
                error_resp_write <= 1'b1;
                r_resp_error_count <= r_resp_error_count + 1;
            end
        end
    end

    // Assign error counters to outputs
    assign error_count_timeout = r_timeout_count;
    assign error_count_resp = r_resp_error_count;