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
    parameter int ERROR_FIFO_DEPTH = 2,

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

    // AXI interface to monitor
    input  logic [IW-1:0]              fub_awid,
    input  logic [AW-1:0]              fub_awaddr,
    input  logic                       fub_awvalid,
    input  logic                       fub_awready,

    input  logic                       fub_wvalid,
    input  logic                       fub_wready,
    input  logic                       fub_wlast,

    input  logic [IW-1:0]              fub_bid,
    input  logic [1:0]                 fub_bresp,
    input  logic                       fub_bvalid,
    input  logic                       fub_bready,

    // Error outputs FIFO interface
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready,
    output logic [3:0]                 fub_error_type,    // Error type flags (bit0: AW timeout, bit1: W timeout, bit2: B timeout, bit3: response error)
    output logic [AW-1:0]              fub_error_addr,    // Address associated with error
    output logic [IW-1:0]              fub_error_id       // ID associated with error
);

    // Error types
    localparam int             ErrorTypeWidth = 4;
    localparam int             ETW = ErrorTypeWidth;
    localparam int             TEDW = AW + IW + ETW;  // Total Error Data Width
    localparam logic [ETW-1:0] ErrorAWTimeout = 4'b0001;  // Bit 0: Address Write timeout
    localparam logic [ETW-1:0] ErrorWTimeout  = 4'b0010;  // Bit 1: Data Write timeout
    localparam logic [ETW-1:0] ErrorBTimeout  = 4'b0100;  // Bit 2: Response timeout
    localparam logic [ETW-1:0] ErrorBResp     = 4'b1000;  // Bit 3: Write response error (SLVERR, DECERR)

    // -------------------------------------------------------------------------
    // Direct timeout monitoring
    // -------------------------------------------------------------------------

    // AW channel timeout monitoring
    logic           r_aw_active;     // AW transaction in progress
    logic [31:0]    r_aw_timer;      // AW timeout counter
    logic           r_aw_timeout;    // AW timeout detected

    // W channel timeout monitoring
    logic           r_w_active;      // W transaction in progress
    logic [31:0]    r_w_timer;       // W timeout counter
    logic           r_w_timeout;     // W timeout detected

    // B channel timeout monitoring
    logic           r_b_active;      // B transaction in progress
    logic [31:0]    r_b_timer;       // B timeout counter
    logic           r_b_timeout;     // B timeout detected

    // -------------------------------------------------------------------------
    // Error Reporting FIFO
    // -------------------------------------------------------------------------

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
        .ow_rd_data({fub_error_type, fub_error_id, fub_error_addr}),
        .o_rd_data(),
        .ow_count()
    );

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
            if (fub_awvalid && !fub_awready) begin
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
            end else if (fub_awvalid && fub_awready) begin
                // Successful handshake
                r_aw_active <= 1'b0;
                r_aw_timer <= '0;
            end else if (!fub_awvalid) begin
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
            if (fub_wvalid && !fub_wready) begin
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
            end else if (fub_wvalid && fub_wready) begin
                // Successful handshake
                r_w_active <= 1'b0;
                r_w_timer <= '0;
            end else if (!fub_wvalid) begin
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
            if (fub_bvalid && !fub_bready) begin
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
            end else if (fub_bvalid && fub_bready) begin
                // Successful handshake
                r_b_active <= 1'b0;
                r_b_timer <= '0;
            end else if (!fub_bvalid) begin
                // No transaction present
                r_b_active <= 1'b0;
                r_b_timer <= '0;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Error Detection and Reporting Logic
    // -------------------------------------------------------------------------

    // Wire assignments for error detection
    wire w_resp_error;
    wire w_awto_error;
    wire w_wto_error;
    wire w_bto_error;

    assign w_resp_error = fub_bvalid && fub_bready && fub_bresp[1];
    assign w_awto_error = (r_aw_timeout || r_error_flag_awto) && ~w_resp_error;
    assign w_wto_error  = (r_w_timeout  || r_error_flag_wto)  && ~w_resp_error && ~w_awto_error;
    assign w_bto_error  = (r_b_timeout  || r_error_flag_bto)  && ~w_resp_error &&
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
                r_error_fifo_wr_data <= {ErrorBResp, fub_bid, '0};
            end

            // AW timeout error
            if (w_awto_error) begin
                r_error_fifo_valid <= 1'b1;
                r_error_fifo_wr_data <= r_aw_timeout ?
                    {ErrorAWTimeout, fub_awid, fub_awaddr} : r_error_flag_awto_data;
                r_error_flag_awto <= 'b0;
                r_error_flag_awto_data <= 'b0;
            end else if (r_aw_timeout) begin
                r_error_flag_awto <= 'b1;
                r_error_flag_awto_data <= {ErrorAWTimeout, fub_awid, fub_awaddr};
            end

            // W timeout error
            if (w_wto_error) begin
                r_error_fifo_valid <= 1'b1;
                // No address for W timeout
                r_error_fifo_wr_data <= r_w_timeout ?
                    {ErrorWTimeout, fub_bid, '0} : r_error_flag_wto_data;
                r_error_flag_wto <= 'b0;
                r_error_flag_wto_data <= 'b0;
            end else if (r_w_timeout) begin
                r_error_flag_wto <= 'b1;
                r_error_flag_wto_data <= {ErrorWTimeout, fub_bid, '0};
            end

            // B timeout error
            if (w_bto_error) begin
                r_error_fifo_valid <= 1'b1;
                // No address for B timeout
                r_error_fifo_wr_data <= r_b_timeout ?
                    {ErrorBTimeout, fub_bid, '0} : r_error_flag_bto_data;
                r_error_flag_bto <= 'b0;
                r_error_flag_bto_data <= 'b0;
            end else if (r_b_timeout) begin
                r_error_flag_bto <= 'b1;
                r_error_flag_bto_data <= {ErrorBTimeout, fub_bid, '0};
            end
        end
    end

endmodule : axi_slave_wr_errmon
