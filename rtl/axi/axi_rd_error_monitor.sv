`timescale 1ns / 1ps

module axi_rd_error_monitor
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AR       = 1000,  // Read address channel timeout
    parameter int TIMEOUT_R        = 1000,  // Read data channel timeout

    // Short params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int UW       = AXI_USER_WIDTH
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // AXI Interface to monitor
    // Read address channel (AR)
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]  m_axi_araddr,
    input  logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_rid,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rvalid,
    input  logic                       m_axi_rready,
    input  logic                       m_axi_rlast,

    // Error outputs
    output logic                       error_timeout_ar,
    output logic                       error_timeout_r,
    output logic                       error_resp_read,   // SLVERR or DECERR on R channel

    // Error address tracking
    output logic [AXI_ADDR_WIDTH-1:0]  error_addr_ar,
    output logic [AXI_ID_WIDTH-1:0]    error_id_ar,

    // Status registers
    output logic [31:0]                error_count_timeout,
    output logic [31:0]                error_count_resp
);

    // Instead of using a struct array, we'll use separate arrays for each field
    logic [2**AXI_ID_WIDTH-1:0]                   ar_transaction_valid;
    logic [2**AXI_ID_WIDTH-1:0][AXI_ID_WIDTH-1:0] ar_transaction_id;
    logic [2**AXI_ID_WIDTH-1:0][AXI_ADDR_WIDTH-1:0] ar_transaction_addr;
    logic [2**AXI_ID_WIDTH-1:0][31:0]             ar_transaction_timer;

    // Pending response tracking (registered)
    logic [31:0] r_r_resp_timer;
    logic r_r_resp_pending;
    logic r_r_last_received;

    // Error counters (registered)
    logic [31:0] r_timeout_count;
    logic [31:0] r_resp_error_count;

    // Initialize error counters
    initial begin
        r_timeout_count = '0;
        r_resp_error_count = '0;
    end

    // Track AR transactions
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            for (int i = 0; i < 2**AXI_ID_WIDTH; i++) begin
                ar_transaction_valid[i] <= 1'b0;
                ar_transaction_timer[i] <= '0;
                ar_transaction_id[i] <= '0;
                ar_transaction_addr[i] <= '0;
            end
            error_timeout_ar <= 1'b0;
            error_addr_ar <= '0;
            error_id_ar <= '0;
            r_r_last_received <= 1'b0;
        end else begin
            // Reset error flag
            error_timeout_ar <= 1'b0;

            // Process new AR transactions
            if (m_axi_arvalid && m_axi_arready) begin
                ar_transaction_valid[m_axi_arid] <= 1'b1;
                ar_transaction_id[m_axi_arid] <= m_axi_arid;
                ar_transaction_addr[m_axi_arid] <= m_axi_araddr;
                ar_transaction_timer[m_axi_arid] <= '0;
            end

            // Process R responses (completion on RLAST)
            if (m_axi_rvalid && m_axi_rready) begin
                if (m_axi_rlast) begin
                    ar_transaction_valid[m_axi_rid] <= 1'b0;
                    r_r_last_received <= 1'b1;
                end
            end else begin
                r_r_last_received <= 1'b0;
            end

            // Update timers and check for timeouts
            for (int i = 0; i < 2**AXI_ID_WIDTH; i++) begin
                if (ar_transaction_valid[i]) begin
                    ar_transaction_timer[i] <= ar_transaction_timer[i] + 1;

                    // Check for timeout
                    if (ar_transaction_timer[i] >= TIMEOUT_AR) begin
                        error_timeout_ar <= 1'b1;
                        error_addr_ar <= ar_transaction_addr[i];
                        error_id_ar <= ar_transaction_id[i];
                        r_timeout_count <= r_timeout_count + 1;
                    end
                end
            end
        end
    end

    // Track read data channel for timeouts and error responses
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_r_resp_pending <= 1'b0;
            r_r_resp_timer <= '0;
            error_timeout_r <= 1'b0;
            error_resp_read <= 1'b0;
        end else begin
            // Reset error flags
            error_timeout_r <= 1'b0;
            error_resp_read <= 1'b0;

            // Start tracking after an address read request is sent
            if (m_axi_arvalid && m_axi_arready) begin
                r_r_resp_pending <= 1'b1;
                r_r_resp_timer <= '0;
            end

            // Stop tracking after the last read data is received
            if (m_axi_rvalid && m_axi_rready && m_axi_rlast) begin
                r_r_resp_pending <= 1'b0;
                r_r_resp_timer <= '0;
            end

            // Check for error response
            if (m_axi_rvalid && m_axi_rready && m_axi_rresp != 2'b00) begin
                error_resp_read <= 1'b1;
                r_resp_error_count <= r_resp_error_count + 1;
            end

            // Update timer and check for timeout
            if (r_r_resp_pending) begin
                r_r_resp_timer <= r_r_resp_timer + 1;

                if (r_r_resp_timer >= TIMEOUT_R) begin
                    error_timeout_r <= 1'b1;
                    r_timeout_count <= r_timeout_count + 1;
                end
            end
        end
    end

    // Assign error counters to outputs
    assign error_count_timeout = r_timeout_count;
    assign error_count_resp = r_resp_error_count;

endmodule : axi_rd_error_monitor
