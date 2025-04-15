`timescale 1ns / 1ps

module axi_master_wr_errmon
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
    parameter int ERROR_FIFO_DEPTH = 4,     // Depth of error reporting FIFO

    // Short params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int EFD      = ERROR_FIFO_DEPTH

)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // AXI Interface to monitor
    // Write address channel (AW)
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]  m_axi_awaddr,
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

    // Error outputs FIFO interface
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready,
    // 4'b0001: AW timeout, 4'b0010: W timeout, 4'b0100: B timeout, 4'b1000: B response error
    output logic [3:0]                 fub_error_type,
    output logic [AXI_ADDR_WIDTH-1:0]  fub_error_addr,
    output logic [AXI_ID_WIDTH-1:0]    fub_error_id
);

    // Error types
    localparam int             ErrorTypeWidth = 4;
    localparam int             ETW = ErrorTypeWidth;
    localparam int             TEDW = AW + IW + ETW;  // Total Error Data Width
    localparam logic [ETW-1:0] ErrorAWTimeout = 4'b0001;
    localparam logic [ETW-1:0] ErrorWTimeout  = 4'b0010;
    localparam logic [ETW-1:0] ErrorBTimeout  = 4'b0100;
    localparam logic [ETW-1:0] ErrorBResp     = 4'b1000;

    // -------------------------------------------------------------------------
    // Direct timeout monitoring
    // -------------------------------------------------------------------------

    // AW channel timeout monitoring
    logic           aw_active;     // AW transaction in progress
    logic [31:0]    aw_timer;      // AW timeout counter
    logic           aw_timeout;    // AW timeout detected

    // W channel timeout monitoring
    logic           w_active;      // W transaction in progress
    logic [31:0]    w_timer;       // W timeout counter
    logic           w_timeout;     // W timeout detected

    // B channel timeout monitoring
    logic           b_active;      // B transaction in progress
    logic [31:0]    b_timer;       // B timeout counter
    logic           b_timeout;     // B timeout detected

    // -------------------------------------------------------------------------
    // Error Reporting FIFO
    // -------------------------------------------------------------------------

    // Error reporting signals
    logic               r_error_fifo_valid;
    logic [TEDW-1:0]    r_error_fifo_wr_data;
    logic               r_error_fifo_ready;

    logic               r_error_flag_awto;
    logic [TEDW-1:0]    r_error_flag_awto_data;
    logic               r_error_flag_wto;
    logic [TEDW-1:0]    r_error_flag_wto_data;
    logic               r_error_flag_bto;
    logic [TEDW-1:0]    r_error_flag_bto_data;

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
        .ow_rd_data({fub_error_type, fub_error_id, fub_error_addr}),
        .o_rd_data(),
        .ow_count()
    );

    // -------------------------------------------------------------------------
    // AW Channel Timeout Monitor
    // -------------------------------------------------------------------------

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            aw_active <= 1'b0;
            aw_timer <= '0;
            aw_timeout <= 1'b0;
        end else begin
            // Clear timeout flag by default
            aw_timeout <= 1'b0;

            // Monitor AW channel
            if (m_axi_awvalid && !m_axi_awready) begin
                // AW transaction is waiting for ready
                if (!aw_active) begin
                    // Start monitoring
                    aw_active <= 1'b1;
                    aw_timer <= '0;
                end else begin
                    // Continue monitoring
                    aw_timer <= aw_timer + 1;

                    // Check for timeout
                    if (aw_timer >= TIMEOUT_AW) begin
                        aw_timeout <= 1'b1;
                        aw_active <= 1'b0; // Reset for next time
                    end
                end
            end else if (m_axi_awvalid && m_axi_awready) begin
                // Successful handshake
                aw_active <= 1'b0;
                aw_timer <= '0;
            end else if (!m_axi_awvalid) begin
                // No transaction present
                aw_active <= 1'b0;
                aw_timer <= '0;
            end
        end
    end

    // -------------------------------------------------------------------------
    // W Channel Timeout Monitor
    // -------------------------------------------------------------------------

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            w_active <= 1'b0;
            w_timer <= '0;
            w_timeout <= 1'b0;
        end else begin
            // Clear timeout flag by default
            w_timeout <= 1'b0;

            // Monitor W channel
            if (m_axi_wvalid && !m_axi_wready) begin
                // W transaction is waiting for ready
                if (!w_active) begin
                    // Start monitoring
                    w_active <= 1'b1;
                    w_timer <= '0;
                end else begin
                    // Continue monitoring
                    w_timer <= w_timer + 1;

                    // Check for timeout
                    if (w_timer >= TIMEOUT_W) begin
                        w_timeout <= 1'b1;
                        w_active <= 1'b0; // Reset for next time
                    end
                end
            end else if (m_axi_wvalid && m_axi_wready) begin
                // Successful handshake
                w_active <= 1'b0;
                w_timer <= '0;
            end else if (!m_axi_wvalid) begin
                // No transaction present
                w_active <= 1'b0;
                w_timer <= '0;
            end
        end
    end

    // -------------------------------------------------------------------------
    // B Channel Timeout Monitor
    // -------------------------------------------------------------------------

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            b_active <= 1'b0;
            b_timer <= '0;
            b_timeout <= 1'b0;
        end else begin
            // Clear timeout flag by default
            b_timeout <= 1'b0;

            // Monitor B channel
            if (m_axi_bvalid && !m_axi_bready) begin
                // B transaction is waiting for ready
                if (!b_active) begin
                    // Start monitoring
                    b_active <= 1'b1;
                    b_timer <= '0;
                end else begin
                    // Continue monitoring
                    b_timer <= b_timer + 1;

                    // Check for timeout
                    if (b_timer >= TIMEOUT_B) begin
                        b_timeout <= 1'b1;
                        b_active <= 1'b0; // Reset for next time
                    end
                end
            end else if (m_axi_bvalid && m_axi_bready) begin
                // Successful handshake
                b_active <= 1'b0;
                b_timer <= '0;
            end else if (!m_axi_bvalid) begin
                // No transaction present
                b_active <= 1'b0;
                b_timer <= '0;
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

    assign w_resp_error = m_axi_bvalid && m_axi_bready && m_axi_bresp[1];
    assign w_awto_error = (aw_timeout || r_error_flag_awto) && ~w_resp_error;
    assign w_wto_error  = (w_timeout  || r_error_flag_wto)  && ~w_resp_error && ~w_awto_error;
    assign w_bto_error  = (b_timeout  || r_error_flag_bto)  && ~w_resp_error &&
                            ~w_awto_error && ~w_wto_error;

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
                // No address for response errors, use bid
                r_error_fifo_wr_data <= {ErrorBResp, m_axi_bid, '0};
            end

            // AW timeout error
            if (w_awto_error) begin
                r_error_fifo_valid <= 1'b1;
                r_error_fifo_wr_data <= aw_timeout ?
                    {ErrorAWTimeout, m_axi_awid, m_axi_awaddr} : r_error_flag_awto_data;
                r_error_flag_awto <= 'b0;
                r_error_flag_awto_data <= 'b0;
            end else if (aw_timeout) begin
                r_error_flag_awto <= 'b1;
                r_error_flag_awto_data <= {ErrorAWTimeout, m_axi_awid, m_axi_awaddr};
            end

            // W timeout error
            if (w_wto_error) begin
                r_error_fifo_valid <= 1'b1;
                // No address for W timeout
                r_error_fifo_wr_data <= w_timeout ?
                    {ErrorWTimeout, m_axi_bid, '0} : r_error_flag_wto_data;
                r_error_flag_wto <= 'b0;
                r_error_flag_wto_data <= 'b0;
            end else if (w_timeout) begin
                r_error_flag_wto <= 'b1;
                r_error_flag_wto_data <= {ErrorWTimeout, m_axi_bid, '0};
            end

            // B timeout error
            if (w_bto_error) begin
                r_error_fifo_valid <= 1'b1;
                // No address for B timeout
                r_error_fifo_wr_data <= b_timeout ?
                    {ErrorBTimeout, m_axi_bid, '0} : r_error_flag_bto_data;
                r_error_flag_bto <= 'b0;
                r_error_flag_bto_data <= 'b0;
            end else if (b_timeout) begin
                r_error_flag_bto <= 'b1;
                r_error_flag_bto_data <= {ErrorBTimeout, m_axi_bid, '0};
            end
        end
    end

endmodule : axi_master_wr_errmon
