`timescale 1ns / 1ps

module axi_master_wr_errmon
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Channel parameter
    parameter int CHANNELS          = 32,  // New parameter for number of channels

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AW       = 1000,  // Write address channel timeout
    parameter int TIMEOUT_W        = 1000,  // Write data channel timeout
    parameter int TIMEOUT_B        = 1000,  // Write response channel timeout

    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH = 4,     // Depth of error reporting FIFO
    parameter int ADDR_FIFO_DEPTH  = 4,     // Depth of address tracking FIFO

    // Short params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int EFD      = ERROR_FIFO_DEPTH,
    parameter int AFD      = ADDR_FIFO_DEPTH
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
    output logic [AXI_ID_WIDTH-1:0]    fub_error_id,

    // Flow control output
    output logic                       block_ready
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

    // -------------------------------------------------------------------------
    // Channel Address FIFOs
    // -------------------------------------------------------------------------

    // Per-channel address FIFO signals
    logic [CHANNELS-1:0]                  w_addr_fifo_wr_valid;
    logic [CHANNELS-1:0]                  w_addr_fifo_wr_ready;
    logic [CHANNELS-1:0][AW-1:0]          w_addr_fifo_wr_data;
    logic [CHANNELS-1:0]                  w_addr_fifo_rd_valid;
    logic [CHANNELS-1:0]                  w_addr_fifo_rd_ready;
    logic [CHANNELS-1:0][AW-1:0]          w_addr_fifo_rd_data;

    // Flow control
    logic                                 w_block_ready;

    // -------------------------------------------------------------------------
    // Error Reporting FIFO
    // -------------------------------------------------------------------------

    // Error reporting signals
    logic               r_error_fifo_valid;
    logic [TEDW-1:0]    r_error_fifo_wr_data;
    logic               r_error_fifo_ready;
    logic [AW-1:0]      w_error_addr;

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
    // Channel Address FIFOs Instantiation
    // -------------------------------------------------------------------------

    genvar channel_idx;
    generate
        for (channel_idx = 0; channel_idx < CHANNELS; channel_idx++) begin : gen_addr_fifo
            // Only create FIFOs for valid IDs within the ID width
            if (channel_idx < (1 << IW)) begin : gen_valid_id
                gaxi_fifo_sync #(
                    .DATA_WIDTH(AW),
                    .DEPTH(AFD),
                    .INSTANCE_NAME($sformatf("ADDR_FIFO_%0d", channel_idx))
                ) i_addr_fifo (
                    .i_axi_aclk(aclk),
                    .i_axi_aresetn(aresetn),
                    .i_wr_valid(w_addr_fifo_wr_valid[channel_idx]),
                    .o_wr_ready(w_addr_fifo_wr_ready[channel_idx]),
                    .i_wr_data(w_addr_fifo_wr_data[channel_idx]),
                    .i_rd_ready(w_addr_fifo_rd_ready[channel_idx]),
                    .o_rd_valid(w_addr_fifo_rd_valid[channel_idx]),
                    .ow_rd_data(w_addr_fifo_rd_data[channel_idx]),
                    .o_rd_data(),
                    .ow_count()
                );
            end else begin : gen_unused_id
                // For unused IDs, just tie off the signals
                assign w_addr_fifo_wr_ready[channel_idx] = 1'b1;
                assign w_addr_fifo_rd_valid[channel_idx] = 1'b0;
                assign w_addr_fifo_rd_data[channel_idx] = '0;
            end
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Address FIFO Control Logic
    // -------------------------------------------------------------------------

    // Write to the address FIFO when a write address is accepted
    always_comb begin
        // Default values
        for (int i = 0; i < CHANNELS; i++) begin
            w_addr_fifo_wr_valid[i] = 1'b0;
            w_addr_fifo_wr_data[i] = '0;
        end

        // When AW transaction happens, write to the corresponding ID's FIFO
        if (m_axi_awvalid && m_axi_awready) begin
            w_addr_fifo_wr_valid[m_axi_awid] = 1'b1;
            w_addr_fifo_wr_data[m_axi_awid] = m_axi_awaddr;
        end
    end

    // Read from the address FIFO when a write response is received
    always_comb begin
        // Default values
        for (int i = 0; i < CHANNELS; i++) begin
            w_addr_fifo_rd_ready[i] = 1'b0;
        end

        // When B transaction completes, consume from the corresponding ID's FIFO
        if (m_axi_bvalid && m_axi_bready) begin
            w_addr_fifo_rd_ready[m_axi_bid] = 1'b1;
        end
    end

    // -------------------------------------------------------------------------
    // Flow Control Logic
    // -------------------------------------------------------------------------

    // Block ready if any of the address FIFOs is not ready
    always_comb begin
        w_block_ready = 1'b0;
        for (int i = 0; i < (1 << IW); i++) begin
            if (!w_addr_fifo_wr_ready[i]) begin
                w_block_ready = 1'b1;
                break;
            end
        end
    end

    // Register the block_ready output
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            block_ready <= 1'b0;
        end else begin
            block_ready <= w_block_ready;
        end
    end

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
            if (m_axi_awvalid && !m_axi_awready) begin
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
            end else if (m_axi_awvalid && m_axi_awready) begin
                // Successful handshake
                r_aw_active <= 1'b0;
                r_aw_timer <= '0;
            end else if (!m_axi_awvalid) begin
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
            if (m_axi_wvalid && !m_axi_wready) begin
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
            end else if (m_axi_wvalid && m_axi_wready) begin
                // Successful handshake
                r_w_active <= 1'b0;
                r_w_timer <= '0;
            end else if (!m_axi_wvalid) begin
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
            if (m_axi_bvalid && !m_axi_bready) begin
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
            end else if (m_axi_bvalid && m_axi_bready) begin
                // Successful handshake
                r_b_active <= 1'b0;
                r_b_timer <= '0;
            end else if (!m_axi_bvalid) begin
                // No transaction present
                r_b_active <= 1'b0;
                r_b_timer <= '0;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Address Selection for Error Reporting
    // -------------------------------------------------------------------------

    // Get the address from the corresponding FIFO for response errors
    assign w_error_addr = w_addr_fifo_rd_valid[m_axi_bid] ? w_addr_fifo_rd_data[m_axi_bid] : '0;

    // -------------------------------------------------------------------------
    // Error Detection and Reporting Logic
    // -------------------------------------------------------------------------

    logic w_resp_error;
    logic w_awto_error;
    logic w_wto_error;
    logic w_bto_error;

    assign w_resp_error = m_axi_bvalid && m_axi_bready && m_axi_bresp[1];
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
                // Use the address from the FIFO for response errors
                r_error_fifo_wr_data <= {ErrorBResp, m_axi_bid, w_error_addr};
            end

            // AW timeout error
            if (w_awto_error) begin
                r_error_fifo_valid <= 1'b1;
                r_error_fifo_wr_data <= r_aw_timeout ?
                    {ErrorAWTimeout, m_axi_awid, m_axi_awaddr} : r_error_flag_awto_data;
                r_error_flag_awto <= 'b0;
                r_error_flag_awto_data <= 'b0;
            end else if (r_aw_timeout) begin
                r_error_flag_awto <= 'b1;
                r_error_flag_awto_data <= {ErrorAWTimeout, m_axi_awid, m_axi_awaddr};
            end

            // W timeout error
            if (w_wto_error) begin
                r_error_fifo_valid <= 1'b1;
                // Get address from FIFO if available for W timeout
                r_error_fifo_wr_data <= {ErrorWTimeout, m_axi_bid,
                    w_addr_fifo_rd_valid[m_axi_bid] ? w_addr_fifo_rd_data[m_axi_bid] : '0};
                r_error_flag_wto <= 'b0;
                r_error_flag_wto_data <= 'b0;
            end else if (r_w_timeout) begin
                r_error_flag_wto <= 'b1;
                r_error_flag_wto_data <= {ErrorWTimeout, m_axi_bid,
                    w_addr_fifo_rd_valid[m_axi_bid] ? w_addr_fifo_rd_data[m_axi_bid] : '0};
            end

            // B timeout error
            if (w_bto_error) begin
                r_error_fifo_valid <= 1'b1;
                // Get address from FIFO if available for B timeout
                r_error_fifo_wr_data <= {ErrorBTimeout, m_axi_bid,
                    w_addr_fifo_rd_valid[m_axi_bid] ? w_addr_fifo_rd_data[m_axi_bid] : '0};
                r_error_flag_bto <= 'b0;
                r_error_flag_bto_data <= 'b0;
            end else if (r_b_timeout) begin
                r_error_flag_bto <= 'b1;
                r_error_flag_bto_data <= {ErrorBTimeout, m_axi_bid,
                    w_addr_fifo_rd_valid[m_axi_bid] ? w_addr_fifo_rd_data[m_axi_bid] : '0};
            end
        end
    end

endmodule : axi_master_wr_errmon
