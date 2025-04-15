`timescale 1ns / 1ps

module axil_master_rd_errmon
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,
    parameter int AXIL_PROT_WIDTH    = 3,   // Fixed for AXI-Lite
    
    // Channel parameter
    parameter int CHANNELS           = 1,   // AXI-Lite doesn't support IDs, so only one channel
    
    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AR         = 1000,  // Read address channel timeout
    parameter int TIMEOUT_R          = 1000,  // Read data channel timeout
    
    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH   = 4,     // Depth of error reporting FIFO
    parameter int ADDR_FIFO_DEPTH    = 4,     // Depth of address tracking FIFO
    
    // Short params
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int PW       = AXIL_PROT_WIDTH,
    parameter int EFD      = ERROR_FIFO_DEPTH,
    parameter int AFD      = ADDR_FIFO_DEPTH,
    parameter int ETW      = 4               // Error type width
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,
    
    // AXI-Lite Interface to monitor
    // Read address channel (AR)
    input  logic [AW-1:0]            m_axil_araddr,
    input  logic [PW-1:0]            m_axil_arprot,
    input  logic                     m_axil_arvalid,
    input  logic                     m_axil_arready,
    
    // Read data channel (R)
    input  logic [DW-1:0]            m_axil_rdata,
    input  logic [1:0]               m_axil_rresp,
    input  logic                     m_axil_rvalid,
    input  logic                     m_axil_rready,
    
    // Error outputs FIFO interface
    output logic                     fub_error_valid,
    input  logic                     fub_error_ready,
    // 4'b0001: AR timeout, 4'b0010: R timeout, 4'b0100: R response error
    output logic [ETW-1:0]           fub_error_type,
    output logic [AW-1:0]            fub_error_addr,
    
    // Flow control output
    output logic                     block_ready
);

    // Error types
    localparam logic [ETW-1:0] ErrorARTimeout = 4'b0001;
    localparam logic [ETW-1:0] ErrorRTimeout  = 4'b0010;
    localparam logic [ETW-1:0] ErrorRResp     = 4'b1000;
    
    // Total Error Data Width
    localparam int TEDW = AW + ETW;
    
    // -------------------------------------------------------------------------
    // Direct timeout monitoring
    // -------------------------------------------------------------------------
    
    // AR channel timeout monitoring
    logic           r_ar_active;     // AR transaction in progress
    logic [31:0]    r_ar_timer;      // AR timeout counter
    logic           r_ar_timeout;    // AR timeout detected
    
    // R channel timeout monitoring
    logic           r_r_active;      // R transaction in progress
    logic [31:0]    r_r_timer;       // R timeout counter
    logic           r_r_timeout;     // R timeout detected
    
    // -------------------------------------------------------------------------
    // Address FIFO
    // -------------------------------------------------------------------------
    
    // Address FIFO signals
    logic                     w_addr_fifo_wr_valid;
    logic                     w_addr_fifo_wr_ready;
    logic [AW-1:0]            w_addr_fifo_wr_data;
    logic                     w_addr_fifo_rd_valid;
    logic                     w_addr_fifo_rd_ready;
    logic [AW-1:0]            w_addr_fifo_rd_data;
    
    // Error reporting signals
    logic                     r_error_fifo_valid;
    logic [TEDW-1:0]          r_error_fifo_wr_data;
    logic                     r_error_fifo_ready;
    
    logic                     r_error_flag_arto;
    logic [TEDW-1:0]          r_error_flag_arto_data;
    logic                     r_error_flag_rto;
    logic [TEDW-1:0]          r_error_flag_rto_data;
    
    // -------------------------------------------------------------------------
    // Address FIFO Instantiation
    // -------------------------------------------------------------------------
    
    // FIFO for address tracking
    gaxi_fifo_sync #(
        .DATA_WIDTH(AW),
        .DEPTH(AFD),
        .INSTANCE_NAME("ADDR_FIFO")
    ) i_addr_fifo (
        .i_axi_aclk(aclk),
        .i_axi_aresetn(aresetn),
        .i_wr_valid(w_addr_fifo_wr_valid),
        .o_wr_ready(w_addr_fifo_wr_ready),
        .i_wr_data(w_addr_fifo_wr_data),
        .i_rd_ready(w_addr_fifo_rd_ready),
        .o_rd_valid(w_addr_fifo_rd_valid),
        .ow_rd_data(w_addr_fifo_rd_data),
        .o_rd_data(),
        .ow_count()
    );
    
    // Error FIFO - reports detected errors
    gaxi_fifo_sync #(
        .DATA_WIDTH(TEDW),
        .DEPTH(EFD),
        .INSTANCE_NAME("ERROR_FIFO")
    ) i_error_fifo (
        .i_axi_aclk(aclk),
        .i_axi_aresetn(aresetn),
        .i_wr_valid(r_error_fifo_valid),
        .o_wr_ready(r_error_fifo_ready),
        .i_wr_data(r_error_fifo_wr_data),
        .i_rd_ready(fub_error_ready),
        .o_rd_valid(fub_error_valid),
        .ow_rd_data({fub_error_type, fub_error_addr}),
        .o_rd_data(),
        .ow_count()
    );
    
    // -------------------------------------------------------------------------
    // Address FIFO Control Logic
    // -------------------------------------------------------------------------
    
    // Write to the address FIFO when a read address is accepted
    assign w_addr_fifo_wr_valid = m_axil_arvalid && m_axil_arready;
    assign w_addr_fifo_wr_data = m_axil_araddr;
    
    // Read from the address FIFO when a read response is received
    assign w_addr_fifo_rd_ready = m_axil_rvalid && m_axil_rready;
    
    // Flow control
    assign block_ready = !w_addr_fifo_wr_ready;
    
    // -------------------------------------------------------------------------
    // AR Channel Timeout Monitor
    // -------------------------------------------------------------------------
    
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_ar_active <= 1'b0;
            r_ar_timer <= '0;
            r_ar_timeout <= 1'b0;
        end else begin
            // Clear timeout flag by default
            r_ar_timeout <= 1'b0;
            
            // Monitor AR channel
            if (m_axil_arvalid && !m_axil_arready) begin
                // AR transaction is waiting for ready
                if (!r_ar_active) begin
                    // Start monitoring
                    r_ar_active <= 1'b1;
                    r_ar_timer <= '0;
                end else begin
                    // Continue monitoring
                    r_ar_timer <= r_ar_timer + 1;
                    
                    // Check for timeout
                    if (r_ar_timer >= TIMEOUT_AR) begin
                        r_ar_timeout <= 1'b1;
                        r_ar_active <= 1'b0; // Reset for next time
                    end
                end
            end else if (m_axil_arvalid && m_axil_arready) begin
                // Successful handshake
                r_ar_active <= 1'b0;
                r_ar_timer <= '0;
            end else if (!m_axil_arvalid) begin
                // No transaction present
                r_ar_active <= 1'b0;
                r_ar_timer <= '0;
            end
        end
    end
    
    // -------------------------------------------------------------------------
    // R Channel Monitor
    // -------------------------------------------------------------------------
    
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_r_active <= 1'b0;
            r_r_timer <= '0;
            r_r_timeout <= 1'b0;
        end else begin
            // Clear timeout flag by default
            r_r_timeout <= 1'b0;
            
            // Monitor R channel
            if (m_axil_rvalid && !m_axil_rready) begin
                // R transaction is waiting for ready
                if (!r_r_active) begin
                    // Start monitoring
                    r_r_active <= 1'b1;
                    r_r_timer <= '0;
                end else begin
                    // Continue monitoring
                    r_r_timer <= r_r_timer + 1;
                    
                    // Check for timeout
                    if (r_r_timer >= TIMEOUT_R) begin
                        r_r_timeout <= 1'b1;
                        r_r_active <= 1'b0; // Reset for next time
                    end
                end
            end else if (m_axil_rvalid && m_axil_rready) begin
                // Successful handshake
                r_r_active <= 1'b0;
                r_r_timer <= '0;
            end else if (!m_axil_rvalid) begin
                // No transaction present
                r_r_active <= 1'b0;
                r_r_timer <= '0;
            end
        end
    end
    
    // -------------------------------------------------------------------------
    // Error Detection and Reporting Logic
    // -------------------------------------------------------------------------
    
    logic w_resp_error;
    logic w_arto_error;
    logic w_rto_error;
    
    assign w_resp_error = m_axil_rvalid && m_axil_rready && m_axil_rresp[1];
    assign w_arto_error = (r_ar_timeout || r_error_flag_arto) && ~w_resp_error;
    assign w_rto_error  = (r_r_timeout  || r_error_flag_rto)  && ~w_resp_error && ~w_arto_error;
    
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_error_fifo_valid <= 1'b0;
            r_error_fifo_wr_data <= '0;
            
            r_error_flag_arto <= 'b0;
            r_error_flag_arto_data <= 'b0;
            
            r_error_flag_rto <= 'b0;
            r_error_flag_rto_data <= 'b0;
            
        end else begin
            // Default value
            r_error_fifo_valid <= 1'b0;
            
            // R response error (SLVERR or DECERR)
            if (w_resp_error) begin
                r_error_fifo_valid <= 1'b1;
                // Use the address from the FIFO for response errors
                r_error_fifo_wr_data <= {ErrorRResp, w_addr_fifo_rd_data};
            end
            
            // AR timeout error
            if (w_arto_error) begin
                r_error_fifo_valid <= 1'b1;
                r_error_fifo_wr_data <= r_ar_timeout ?
                    {ErrorARTimeout, m_axil_araddr} : r_error_flag_arto_data;
                r_error_flag_arto <= 'b0;
                r_error_flag_arto_data <= 'b0;
            end else if (r_ar_timeout) begin
                r_error_flag_arto <= 'b1;
                r_error_flag_arto_data <= {ErrorARTimeout, m_axil_araddr};
            end
            
            // R timeout error
            if (w_rto_error) begin
                r_error_fifo_valid <= 1'b1;
                // Use address from FIFO for R timeout
                r_error_fifo_wr_data <= {ErrorRTimeout, w_addr_fifo_rd_data};
                r_error_flag_rto <= 'b0;
                r_error_flag_rto_data <= 'b0;
            end else if (r_r_timeout) begin
                r_error_flag_rto <= 'b1;
                r_error_flag_rto_data <= {ErrorRTimeout, w_addr_fifo_rd_data};
            end
        end
    end

endmodule : axil_master_rd_errmon