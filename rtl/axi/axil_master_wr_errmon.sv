`timescale 1ns / 1ps

module axil_master_wr_errmon
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,
    parameter int AXIL_PROT_WIDTH    = 3,    // Fixed for AXI-Lite
    
    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AW        = 1000,  // Write address channel timeout
    parameter int TIMEOUT_W         = 1000,  // Write data channel timeout
    parameter int TIMEOUT_B         = 1000,  // Write response channel timeout
    
    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH  = 4,     // Depth of error reporting FIFO
    parameter int ADDR_FIFO_DEPTH   = 4,     // Depth of address tracking FIFO
    
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
    // Write address channel (AW)
    input  logic [AW-1:0]            m_axil_awaddr,
    input  logic [PW-1:0]            m_axil_awprot,
    input  logic                     m_axil_awvalid,
    input  logic                     m_axil_awready,
    
    // Write data channel (W)
    input  logic [DW-1:0]            m_axil_wdata,
    input  logic [DW/8-1:0]          m_axil_wstrb,
    input  logic                     m_axil_wvalid,
    input  logic                     m_axil_wready,
    
    // Write response channel (B)
    input  logic [1:0]               m_axil_bresp,
    input  logic                     m_axil_bvalid,
    input  logic                     m_axil_bready,
    
    // Error outputs FIFO interface
    output logic                     fub_error_valid,
    input  logic                     fub_error_ready,
    // 4'b0001: AW timeout, 4'b0010: W timeout, 4'b0100: B timeout, 4'b1000: B response error
    output logic [ETW-1:0]           fub_error_type,
    output logic [AW-1:0]            fub_error_addr,
    
    // Flow control output
    output logic                     block_ready
);

    // Error types
    localparam logic [ETW-1:0] ErrorAWTimeout = 4'b0001;
    localparam logic [ETW-1:0] ErrorWTimeout  = 4'b0010;
    localparam logic [ETW-1:0] ErrorBTimeout  = 4'b0100;
    localparam logic [ETW-1:0] ErrorBResp     = 4'b1000;
    
    // Total Error Data Width
    localparam int TEDW = AW + ETW;
    
    // -------------------------------------------------------------------------
    // Direct timeout monitoring
    // -------------------------------------------------------------------------
    
    // AW channel timeout monitoring
    logic           r_aw_active;    // AW transaction in progress
    logic [31:0]    r_aw_timer;     // AW timeout counter
    logic           r_aw_timeout;   // AW timeout detected
    
    // W channel timeout monitoring
    logic           r_w_active;     // W transaction in progress
    logic [31:0]    r_w_timer;      // W timeout counter
    logic           r_w_timeout;    // W timeout detected
    
    // B channel timeout monitoring
    logic           r_b_active;     // B transaction in progress
    logic [31:0]    r_b_timer;      // B timeout counter
    logic           r_b_timeout;    // B timeout detected
    
    // Address FIFO signals
    logic                     w_addr_fifo_wr_valid;
    logic                     w_addr_fifo_wr_ready;
    logic [AW-1:0]            w_addr_fifo_wr_data;
    logic                     w_addr_fifo_rd_valid;
    logic                     w_addr_fifo_rd_ready;
    logic [AW-1:0]            w_addr_fifo_rd_data;
    
    // Error reporting signals
    logic               r_error_fifo_valid;
    logic [TEDW-1:0]    r_error_fifo_wr_data;
    logic               w_error_fifo_ready;
    
    logic               r_error_flag_awto;
    logic [TEDW-1:0]    r_error_flag_awto_data;
    logic               r_error_flag_wto;
    logic [TEDW-1:0]    r_error_flag_wto_data;
    logic               r_error_flag_bto;
    logic [TEDW-1:0]    r_error_flag_bto_data;
    
    // -------------------------------------------------------------------------
    // FIFO Instantiations
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
        .o_wr_ready(w_error_fifo_ready),
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
    
    // Write to the address FIFO when a write address is accepted
    assign w_addr_fifo_wr_valid = m_axil_awvalid && m_axil_awready;
    assign w_addr_fifo_wr_data = m_axil_awaddr;
    
    // Read from the address FIFO when a write response is received
    assign w_addr_fifo_rd_ready = m_axil_bvalid && m_axil_bready;
    
    // Flow control
    assign block_ready = !w_addr_fifo_wr_ready;
    
    // -------------------------------------------------------------------------
    // AW Channel Timeout Monitor
    // -------------------------------------------------------------------------
    
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_aw_active <= 1'b0;
            r_aw_timer <= '0;
            r_aw_timeout <= 1'b0;
        end else begin
            // Clear timeout flag by default
            r_aw_timeout <= 1'b0;
            
            // Monitor AW channel
            if (m_axil_awvalid && !m_axil_awready) begin
                // AW transaction is waiting for ready
                if (!r_aw_active) begin
                    // Start monitoring
                    r_aw_active <= 1'b1;
                    r_aw_timer <= '0;
                end else begin
                    // Continue monitoring
                    r_aw_timer <= r_aw_timer + 1;
                    
                    // Check for timeout
                    if (r_aw_timer >= TIMEOUT_AW) begin
                        r_aw_timeout <= 1'b1;
                        r_aw_active <= 1'b0; // Reset for next time
                    end
                end
            end else if (m_axil_awvalid && m_axil_awready) begin
                // Successful handshake
                r_aw_active <= 1'b0;
                r_aw_timer <= '0;
            end else if (!m_axil_awvalid) begin
                // No transaction present
                r_aw_active <= 1'b0;
                r_aw_timer <= '0;
            end
        end
    end
    
    // -------------------------------------------------------------------------
    // W Channel Timeout Monitor
    // -------------------------------------------------------------------------
    
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_w_active <= 1'b0;
            r_w_timer <= '0;
            r_w_timeout <= 1'b0;
        end else begin
            // Clear timeout flag by default
            r_w_timeout <= 1'b0;
            
            // Monitor W channel
            if (m_axil_wvalid && !m_axil_wready) begin
                // W transaction is waiting for ready
                if (!r_w_active) begin
                    // Start monitoring
                    r_w_active <= 1'b1;
                    r_w_timer <= '0;
                end else begin
                    // Continue monitoring
                    r_w_timer <= r_w_timer + 1;
                    
                    // Check for timeout
                    if (r_w_timer >= TIMEOUT_W) begin
                        r_w_timeout <= 1'b1;
                        r_w_active <= 1'b0; // Reset for next time
                    end
                end
            end else if (m_axil_wvalid && m_axil_wready) begin
                // Successful handshake
                r_w_active <= 1'b0;
                r_w_timer <= '0;
            end else if (!m_axil_wvalid) begin
                // No transaction present
                r_w_active <= 1'b0;
                r_w_timer <= '0;
            end
        end
    end
    
    // -------------------------------------------------------------------------
    // B Channel Timeout Monitor
    // -------------------------------------------------------------------------
    
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_b_active <= 1'b0;
            r_b_timer <= '0;
            r_b_timeout <= 1'b0;
        end else begin
            // Clear timeout flag by default
            r_b_timeout <= 1'b0;
            
            // Monitor B channel
            if (m_axil_bvalid && !m_axil_bready) begin
                // B transaction is waiting for ready
                if (!r_b_active) begin
                    // Start monitoring
                    r_b_active <= 1'b1;
                    r_b_timer <= '0;
                end else begin
                    // Continue monitoring
                    r_b_timer <= r_b_timer + 1;
                    
                    // Check for timeout
                    if (r_b_timer >= TIMEOUT_B) begin
                        r_b_timeout <= 1'b1;
                        r_b_active <= 1'b0; // Reset for next time
                    end
                end
            end else if (m_axil_bvalid && m_axil_bready) begin
                // Successful handshake
                r_b_active <= 1'b0;
                r_b_timer <= '0;
            end else if (!m_axil_bvalid) begin
                // No transaction present
                r_b_active <= 1'b0;
                r_b_timer <= '0;
            end
        end
    end
    
    // -------------------------------------------------------------------------
    // Error Detection and Reporting Logic
    // -------------------------------------------------------------------------
    
    logic w_resp_error;
    logic w_awto_error;
    logic w_wto_error;
    logic w_bto_error;
    
    assign w_resp_error = m_axil_bvalid && m_axil_bready && m_axil_bresp[1];
    assign w_awto_error = (r_aw_timeout || r_error_flag_awto) && ~w_resp_error;
    assign w_wto_error  = (r_w_timeout  || r_error_flag_wto)  && ~w_resp_error && ~w_awto_error;
    assign w_bto_error  = (r_b_timeout  || r_error_flag_bto)  && ~w_resp_error && ~w_awto_error && ~w_wto_error;
    
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_error_fifo_valid <= 1'b0;
            r_error_fifo_wr_data <= '0;
            
            r_error_flag_awto <= 'b0;
            r_error_flag_awto_data <= 'b0;
            
            r_error_flag_wto <= 'b0;
            r_error_flag_wto_data <= 'b0;
            
            r_error_flag_bto <= 'b0;
            r_error_flag_bto_data <= 'b0;
            
        end else begin
            // Default value
            r_error_fifo_valid <= 1'b0;
            
            // B response error (SLVERR or DECERR)
            if (w_resp_error) begin
                r_error_fifo_valid <= 1'b1;
                // Use the address from the FIFO for response errors
                r_error_fifo_wr_data <= {ErrorBResp, w_addr_fifo_rd_data};
            end
            
            // AW timeout error
            if (w_awto_error) begin
                r_error_fifo_valid <= 1'b1;
                r_error_fifo_wr_data <= r_aw_timeout ?
                    {ErrorAWTimeout, m_axil_awaddr} : r_error_flag_awto_data;
                r_error_flag_awto <= 'b0;
                r_error_flag_awto_data <= 'b0;
            end else if (r_aw_timeout) begin
                r_error_flag_awto <= 'b1;
                r_error_flag_awto_data <= {ErrorAWTimeout, m_axil_awaddr};
            end
            
            // W timeout error
            if (w_wto_error) begin
                r_error_fifo_valid <= 1'b1;
                // Use address from FIFO for W timeout if available
                r_error_fifo_wr_data <= {ErrorWTimeout, w_addr_fifo_rd_data};
                r_error_flag_wto <= 'b0;
                r_error_flag_wto_data <= 'b0;
            end else if (r_w_timeout) begin
                r_error_flag_wto <= 'b1;
                r_error_flag_wto_data <= {ErrorWTimeout, w_addr_fifo_rd_data};
            end
            
            // B timeout error
            if (w_bto_error) begin
                r_error_fifo_valid <= 1'b1;
                // Use address from FIFO for B timeout if available
                r_error_fifo_wr_data <= {ErrorBTimeout, w_addr_fifo_rd_data};
                r_error_flag_bto <= 'b0;
                r_error_flag_bto_data <= 'b0;
            end else if (r_b_timeout) begin
                r_error_flag_bto <= 'b1;
                r_error_flag_bto_data <= {ErrorBTimeout, w_addr_fifo_rd_data};
            end
        end
    end

endmodule : axil_master_wr_errmon