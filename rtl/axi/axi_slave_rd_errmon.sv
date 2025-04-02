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
    // Read address channel (AR)
    input  logic [IW-1:0]              fub_arid,
    input  logic [AW-1:0]              fub_araddr,
    input  logic                       fub_arvalid,
    input  logic                       fub_arready,

    // Read data channel (R)
    input  logic [IW-1:0]              fub_rid,
    input  logic [1:0]                 fub_rresp,
    input  logic                       fub_rvalid,
    input  logic                       fub_rready,
    input  logic                       fub_rlast,

    // Error outputs FIFO interface
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready,
    // 4'b0001: AR timeout, 4'b0010: R timeout, 4'b0100: R response error
    output logic [3:0]                 fub_error_type,
    output logic [AW-1:0]              fub_error_addr,
    output logic [IW-1:0]              fub_error_id
);

    // Error types
    localparam int             ErrorTypeWidth = 4;
    localparam int             ETW = ErrorTypeWidth;
    localparam int             TEDW = AW + IW + ETW;  // Total Error Data Width
    localparam logic [ETW-1:0] ErrorARTimeout = 4'b0001;
    localparam logic [ETW-1:0] ErrorRTimeout  = 4'b0010;
    localparam logic [ETW-1:0] ErrorRResp     = 4'b1000;

    // -------------------------------------------------------------------------
    // Direct timeout monitoring
    // -------------------------------------------------------------------------

    // AR channel timeout monitoring
    logic           ar_active;     // AR transaction in progress
    logic [31:0]    ar_timer;      // AR timeout counter
    logic           ar_timeout;    // AR timeout detected

    // R channel timeout monitoring
    logic           r_active;      // R transaction in progress
    logic [31:0]    r_timer;       // R timeout counter
    logic           r_timeout;     // R timeout detected

    // -------------------------------------------------------------------------
    // Error Reporting FIFO
    // -------------------------------------------------------------------------

    // Error reporting signals
    logic               r_error_fifo_valid;
    logic [TEDW-1:0]    r_error_fifo_wr_data;
    logic               r_error_fifo_ready;

    logic               r_error_flag_arto;
    logic [TEDW-1:0]    r_error_flag_arto_data;
    logic               r_error_flag_rto;
    logic [TEDW-1:0]    r_error_flag_rto_data;

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
    // AR Channel Timeout Monitor
    // -------------------------------------------------------------------------

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            ar_active <= 1'b0;
            ar_timer <= '0;
            ar_timeout <= 1'b0;
        end else begin
            // Clear timeout flag by default
            ar_timeout <= 1'b0;

            // Monitor AR channel
            if (fub_arvalid && !fub_arready) begin
                // AR transaction is waiting for ready
                if (!ar_active) begin
                    // Start monitoring
                    ar_active <= 1'b1;
                    ar_timer <= '0;
                end else begin
                    // Continue monitoring
                    ar_timer <= ar_timer + 1;

                    // Check for timeout
                    if (ar_timer >= TIMEOUT_AR) begin
                        ar_timeout <= 1'b1;
                        ar_active <= 1'b0; // Reset for next time
                    end
                end
            end else if (fub_arvalid && fub_arready) begin
                // Successful handshake
                ar_active <= 1'b0;
                ar_timer <= '0;
            end else if (!fub_arvalid) begin
                // No transaction present
                ar_active <= 1'b0;
                ar_timer <= '0;
            end
        end
    end

    // -------------------------------------------------------------------------
    // R Channel Monitor
    // -------------------------------------------------------------------------

    // Only monitor R timeout if we get a valid but not ready
    // No need to track by ID since we only care about the handshake

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_active <= 1'b0;
            r_timer <= '0;
            r_timeout <= 1'b0;
        end else begin
            // Clear timeout flag by default
            r_timeout <= 1'b0;

            // Monitor R channel
            if (fub_rvalid && !fub_rready) begin
                // R transaction is waiting for ready
                if (!r_active) begin
                    // Start monitoring
                    r_active <= 1'b1;
                    r_timer <= '0;
                end else begin
                    // Continue monitoring
                    r_timer <= r_timer + 1;

                    // Check for timeout
                    if (r_timer >= TIMEOUT_R) begin
                        r_timeout <= 1'b1;
                        r_active <= 1'b0; // Reset for next time
                    end
                end
            end else if (fub_rvalid && fub_rready) begin
                // Successful handshake
                r_active <= 1'b0;
                r_timer <= '0;
            end else if (!fub_rvalid) begin
                // No transaction present
                r_active <= 1'b0;
                r_timer <= '0;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Error Detection and Reporting Logic
    // -------------------------------------------------------------------------

    logic w_resp_error;
    logic w_arto_error;
    logic w_rto_error;

    assign w_resp_error = fub_rvalid && fub_rready && fub_rresp[1];
    assign w_arto_error = (ar_timeout || r_error_flag_arto) && ~w_resp_error;
    assign w_rto_error  = (r_timeout  || r_error_flag_rto)  && ~w_resp_error && ~w_arto_error;

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
                // No address for response errors
                r_error_fifo_wr_data <= {ErrorRResp, fub_rid, '0};
            end

            // AR timeout error
            if (w_arto_error) begin
                r_error_fifo_valid <= 1'b1;
                r_error_fifo_wr_data <= ar_timeout ?
                    {ErrorARTimeout, fub_arid, fub_araddr} : r_error_flag_arto_data;
                r_error_flag_arto <= 'b0;
                r_error_flag_arto_data <= 'b0;
            end else if (ar_timeout) begin
                r_error_flag_arto <= 'b1;
                r_error_flag_arto_data <= {ErrorARTimeout, fub_arid, fub_araddr};
            end

            // R timeout error
            if (w_rto_error) begin
                r_error_fifo_valid <= 1'b1;
                // No address for R timeout
                r_error_fifo_wr_data <= r_timeout ?
                    {ErrorRTimeout, fub_rid, '0} : r_error_flag_rto_data;
                r_error_flag_rto <= 'b0;
                r_error_flag_rto_data <= 'b0;
            end else if (r_timeout) begin
                r_error_flag_rto <= 'b1;
                r_error_flag_rto_data <= {ErrorRTimeout, fub_rid, '0};
            end

        end
    end

endmodule : axi_slave_rd_errmon
