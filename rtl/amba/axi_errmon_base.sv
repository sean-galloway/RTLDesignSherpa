`timescale 1ns / 1ps
/**
 * AXI Error Monitor Base Module
 *
 * This module monitors AXI/AXI-Lite read or write channels for protocol
 * violations and timeout conditions. It detects various error types including:
 * - Address channel timeouts
 * - Data channel timeouts
 * - Response channel timeouts (write only)
 * - Error responses
 *
 * Errors are reported through an AXI-Stream like FIFO interface with
 * the error type, ID, and address information.
 */
module axi_errmon_base
#(
    // Error Packet Identifiers
    parameter int UNIT_ID            = 99,
    parameter int AGENT_ID           = 99,

    // General parameters
    parameter int CHANNELS           = 1,    // Number of channels to monitor
    parameter int ADDR_WIDTH         = 32,   // Width of address bus
    parameter int ID_WIDTH           = 8,    // Width of ID bus (0 for AXIL)

    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH   = 4,    // Depth of error reporting FIFO
    parameter int ADDR_FIFO_DEPTH    = 4,    // Depth of address tracking FIFO

    // Configuration options
    /* verilator lint_off WIDTHTRUNC */
    parameter bit IS_READ            = 1,    // 1 for read, 0 for write
    parameter bit IS_AXI             = 1,    // 1 for AXI, 0 for AXI-Lite
    /* verilator lint_on WIDTHTRUNC */

    // Short params
    parameter int AW                 = ADDR_WIDTH,
    parameter int IW                 = ID_WIDTH,
    parameter int EFD                = ERROR_FIFO_DEPTH,
    parameter int AFD                = ADDR_FIFO_DEPTH,
    parameter int ETW                = 8                // Error type width (fixed)
)
(
    // Global Clock and Reset
    input  logic                     aclk,
    input  logic                     aresetn,

    // Command phase (AW/AR)
    input  logic [AW-1:0]            i_addr_addr,    // Address value
    input  logic [IW-1:0]            i_addr_id,      // Transaction ID
    input  logic                     i_addr_valid,   // Command valid
    input  logic                     i_addr_ready,   // Command ready

    // Data channel (W/R)
    input  logic [IW-1:0]            i_data_id,      // Data ID (read only)
    input  logic                     i_data_valid,   // Data valid
    input  logic                     i_data_ready,   // Data ready
    input  logic                     i_data_last,    // Last data flag
    input  logic [1:0]               i_data_resp,    // Response code (read only)

    // Response channel (B)
    input  logic [IW-1:0]            i_resp_id,      // Response ID (write only)
    input  logic [1:0]               i_resp,         // Response code
    input  logic                     i_resp_valid,   // Response valid
    input  logic                     i_resp_ready,   // Response ready

    // Timer configs
    input  logic [3:0]               i_cfg_freq_sel, // Frequency selection (configurable)
    input  logic [3:0]               i_cfg_addr_cnt, // ADDR match for a timeout
    input  logic [3:0]               i_cfg_data_cnt, // DATA match for a timeout
    input  logic [3:0]               i_cfg_resp_cnt, // RESP match for a timeout

    // Error outputs FIFO interface
    output logic                     o_error_valid,
    input  logic                     i_error_ready,
    output logic [ETW-1:0]           o_error_type,
    output logic [AW-1:0]            o_error_addr,
    output logic [IW-1:0]            o_error_id,
    output logic [7:0]               o_error_unit_id,
    output logic [7:0]               o_error_agent_id,

    // Flow control output
    output logic                     o_block_ready,
    output logic                     o_busy
);

    // Define the read/write-specific error types (one-hot encoding)
    localparam logic [ETW-1:0] ErrorAddrTimeout = 8'b00000001;  // AW/AR timeout
    localparam logic [ETW-1:0] ErrorDataTimeout = 8'b00000010;  // W/R timeout
    localparam logic [ETW-1:0] ErrorRespTimeout = 8'b00000100;  // B timeout (write only)
    localparam logic [ETW-1:0] ErrorRespError   = 8'b00001000;  // B/R response error

    // Total Error Data Width for FIFO
    localparam int TEDW = AW + IW + ETW;

    // count wiidth
    localparam int CW = $clog2(ADDR_FIFO_DEPTH+1);

    // -------------------------------------------------------------------------
    // Counter signals for timeout detection
    // -------------------------------------------------------------------------

    // Define counter instance outputs
    logic [CHANNELS-1:0][3:0]       w_addr_counter;    // Counter values from the counter modules
    logic [CHANNELS-1:0]            w_addr_tick;       // Tick signals from counter modules
    logic [CHANNELS-1:0][3:0]       w_data_counter;    // Counter values for data channels
    logic [CHANNELS-1:0]            w_data_tick;       // Data channel ticks
    logic [CHANNELS-1:0][3:0]       w_resp_counter;    // Counter values for response channels
    logic [CHANNELS-1:0]            w_resp_tick;       // Response channel ticks

    // Timeout detection signals
    logic [CHANNELS-1:0]            r_addr_timeout;    // Address timeout signals
    logic [CHANNELS-1:0]            r_data_timeout;    // Data timeout signals
    logic [CHANNELS-1:0]            r_resp_timeout;    // Response timeout signals (write only)

    // Timeout reported signals (to prevent multiple reports of the same timeout)
    logic [CHANNELS-1:0]            r_addr_timeout_reported;    // Address timeout already reported
    logic [CHANNELS-1:0]            r_data_timeout_reported;    // Data timeout already reported
    logic [CHANNELS-1:0]            r_resp_timeout_reported;    // Response timeout already reported

    // Active tracking signals
    logic                           r_addr_active;     // Address transaction in progress
    logic [IW-1:0]                  r_addr_current_id; // Current transaction ID

    // Store original IDs for each channel
    logic [CHANNELS-1:0][IW-1:0]    r_channel_id;     // Store ID per channel

    // -------------------------------------------------------------------------
    // Address FIFO tracking
    // -------------------------------------------------------------------------

    // Address FIFO signals - one per channel
    logic [CHANNELS-1:0]                   w_addr_fifo_wr_valid;
    logic [CHANNELS-1:0]                   w_addr_fifo_wr_ready;
    logic [CHANNELS-1:0][AW-1:0]           w_addr_fifo_wr_data;
    logic [CHANNELS-1:0]                   w_addr_fifo_rd_valid;
    logic [CHANNELS-1:0]                   w_addr_fifo_rd_ready;
    logic [CHANNELS-1:0][AW-1:0]           w_addr_fifo_rd_data;
    logic [CHANNELS-1:0][CW-1:0]           w_addr_fifo_count;

    // Add signals for a single write data FIFO (not per-channel)
    logic                                  w_wdata_fifo_wr_valid;
    logic                                  w_wdata_fifo_wr_ready;
    logic [AW+IW-1:0]                      w_wdata_fifo_wr_data;
    logic                                  w_wdata_fifo_rd_valid;
    logic                                  w_wdata_fifo_rd_ready;
    logic [AW+IW-1:0]                      w_wdata_fifo_rd_data;
    logic [CW-1:0]                         w_wdata_fifo_count;

    // Error reporting signals
    logic                                  r_error_fifo_valid;
    logic [TEDW-1:0]                       r_error_fifo_wr_data;
    logic                                  w_error_fifo_ready;

    // Error flag storage to prevent loss during processing
    logic [CHANNELS-1:0]                   r_error_flag_addr_to;
    logic [CHANNELS-1:0][TEDW-1:0]         r_error_flag_addr_to_data;
    logic [CHANNELS-1:0]                   r_error_flag_data_to;
    logic [CHANNELS-1:0][TEDW-1:0]         r_error_flag_data_to_data;
    logic [CHANNELS-1:0]                   r_error_flag_resp_to;
    logic [CHANNELS-1:0][TEDW-1:0]         r_error_flag_resp_to_data;

    // Frequency selection change detection
    logic [3:0]                            r_prev_freq_sel;
    logic                                  r_clear_pulse;

    // Error priority type for handling multiple errors
    typedef enum logic [2:0] {
        ERR_NONE      = 3'b000,
        ERR_RESP      = 3'b001,  // Highest priority
        ERR_ADDR_TO   = 3'b010,
        ERR_DATA_TO   = 3'b011,
        ERR_RESP_TO   = 3'b100   // Lowest priority
    } err_priority_t;

    // Variables for error detection
    err_priority_t current_err;
    logic [TEDW-1:0] current_err_data;
    logic error_found;

    // -------------------------------------------------------------------------
    // Determine channel index from ID - automatic function
    // -------------------------------------------------------------------------
    function automatic int get_channel_idx(logic [IW-1:0] id);
        /* verilator lint_off WIDTHEXPAND */
        return (IS_AXI) ? (int'(id) % CHANNELS) : 0;
        /* verilator lint_on WIDTHEXPAND */
    endfunction

    // -------------------------------------------------------------------------
    // sync reset signals
    // -------------------------------------------------------------------------
    logic [CHANNELS-1:0] w_addr_sync_reset_n;
    logic [CHANNELS-1:0] w_data_sync_reset_n;
    logic [CHANNELS-1:0] w_resp_sync_reset_n;

    // Set the sync reset signals
    always_comb begin
        for (int ch = 0; ch < CHANNELS; ch++) begin
            // Address channel sync reset
            w_addr_sync_reset_n[ch] = w_addr_fifo_rd_valid[ch] ||
                (i_addr_valid && get_channel_idx(i_addr_id) == ch);

            // Data channel sync reset
            if (IS_READ) begin
                w_data_sync_reset_n[ch] = w_addr_fifo_rd_valid[ch] ||
                    (i_addr_valid && get_channel_idx(i_addr_id) == ch);
            end else if (ch == 0) begin
                w_data_sync_reset_n[ch] = w_wdata_fifo_rd_valid ||
                    (i_addr_valid && get_channel_idx(i_addr_id) == ch);
            end else begin
                w_data_sync_reset_n[ch] = 1'b0; // Not used for write mode except channel 0
            end

            // Response channel sync reset (write only)
            if (!IS_READ) begin
                w_resp_sync_reset_n[ch] = (!r_clear_pulse && w_addr_fifo_rd_valid[ch]) ||
                                            (i_addr_valid && get_channel_idx(i_addr_id) == ch);
            end else begin
                w_resp_sync_reset_n[ch] = 1'b0; // Not used for read mode
            end
        end
    end

    // -------------------------------------------------------------------------
    // Frequency selection monitoring (not needed anymore with counter_freq_invariant)
    // -------------------------------------------------------------------------
    // The counter_freq_invariant module already handles frequency changes internally

    // -------------------------------------------------------------------------
    // Counter Module Instantiations - One for each type of timeout
    // -------------------------------------------------------------------------

    // Address channel counters (one per channel)
    genvar i;
    generate
        for (i = 0; i < CHANNELS; i++) begin : gen_addr_counters
            counter_freq_invariant #(
                .COUNTER_WIDTH(4),  // Using 4-bit counters as specified
                .PRESCALER_MAX(4096)
            ) i_addr_counter (
                .i_clk(aclk),
                .i_rst_n(aresetn),
                .i_sync_reset_n(w_addr_sync_reset_n[i]),
                .i_freq_sel(i_cfg_freq_sel),
                .o_counter(w_addr_counter[i]),
                .o_tick(w_addr_tick[i])
            );
        end
    endgenerate

    // Data channel counters (one per channel)
    generate
        for (i = 0; i < CHANNELS; i++) begin : gen_data_counters
            counter_freq_invariant #(
                .COUNTER_WIDTH(4),
                .PRESCALER_MAX(4096)
            ) i_data_counter (
                .i_clk(aclk),
                .i_rst_n(aresetn),
                .i_sync_reset_n(w_data_sync_reset_n[i]),
                .i_freq_sel(i_cfg_freq_sel),
                .o_counter(w_data_counter[i]),
                .o_tick(w_data_tick[i])
            );
        end
    endgenerate

    // Response channel counters (for write mode only)
    generate
        if (!IS_READ) begin : gen_resp_counters
            for (i = 0; i < CHANNELS; i++) begin : gen_resp_counter_inst
                counter_freq_invariant #(
                    .COUNTER_WIDTH(4),
                    .PRESCALER_MAX(4096)
                ) i_resp_counter (
                    .i_clk(aclk),
                    .i_rst_n(aresetn),
                    .i_sync_reset_n(w_resp_sync_reset_n[i]),
                    .i_freq_sel(i_cfg_freq_sel),
                    .o_counter(w_resp_counter[i]),
                    .o_tick(w_resp_tick[i])
                );
            end
        end else begin : gen_no_resp_counters
            // For read mode, tie signals to zero
            always_comb begin
                for (int j = 0; j < CHANNELS; j++) begin
                    w_resp_counter[j] = '0;
                    w_resp_tick[j] = '0;
                end
            end
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Timeout Detection Logic
    // -------------------------------------------------------------------------

    // Detect timeouts based on counter values
    always_comb begin
        // Default values
        r_addr_timeout = '0;
        r_data_timeout = '0;
        r_resp_timeout = '0;

        // Address timeout detection - only report if not already reported
        for (int ch = 0; ch < CHANNELS; ch++) begin
            if (i_addr_valid && !i_addr_ready && (get_channel_idx(i_addr_id) == ch) &&
                (w_addr_counter[ch] >= i_cfg_addr_cnt) && !r_addr_timeout_reported[ch]) begin
                r_addr_timeout[ch] = 1'b1;
            end
        end

        // Data timeout detection - only report if not already reported
        for (int ch = 0; ch < CHANNELS; ch++) begin
            if (IS_READ) begin
                // Read mode - all channels can have data timeouts
                if (w_addr_fifo_rd_valid[ch] && (w_data_counter[ch] >= i_cfg_data_cnt) &&
                    !r_data_timeout_reported[ch]) begin
                    r_data_timeout[ch] = 1'b1;
                end
            end else if (ch == 0) begin
                // Write mode - only channel 0 has data timeout
                if (i_data_valid && !i_data_ready && (w_data_counter[ch] >= i_cfg_data_cnt) &&
                    !r_data_timeout_reported[ch]) begin
                    r_data_timeout[ch] = 1'b1;
                end
            end
        end

        // Response timeout detection (write only) - only report if not already reported
        if (!IS_READ) begin
            for (int ch = 0; ch < CHANNELS; ch++) begin
                if (i_resp_valid && !i_resp_ready && (get_channel_idx(i_resp_id) == ch) &&
                    (w_resp_counter[ch] >= i_cfg_resp_cnt) && !r_resp_timeout_reported[ch]) begin
                    r_resp_timeout[ch] = 1'b1;
                end
            end
        end
    end

    // Track active transactions and IDs
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_addr_active <= 1'b0;
            r_addr_current_id <= '0;
            r_addr_timeout_reported <= '0;
            r_data_timeout_reported <= '0;
            r_resp_timeout_reported <= '0;

            // Initialize channel IDs
            for (int ch = 0; ch < CHANNELS; ch++) begin
                r_channel_id[ch] <= '0;
            end
        end else begin
            // Update command phase active state
            if (i_addr_valid && !i_addr_ready && !r_addr_active) begin
                r_addr_active <= 1'b1;
                r_addr_current_id <= i_addr_id;
            end else if ((i_addr_valid && i_addr_ready) || (!i_addr_valid && r_addr_active)) begin
                r_addr_active <= 1'b0;
            end

            // Store ID when command transaction occurs
            if (i_addr_valid && i_addr_ready) begin
                automatic int ch_idx;
                ch_idx = get_channel_idx(i_addr_id);
                r_channel_id[ch_idx] <= i_addr_id;

                // Clear timeout reported flags for this channel when a new transaction starts
                r_addr_timeout_reported[ch_idx] <= 1'b0;
                r_data_timeout_reported[ch_idx] <= 1'b0;
                r_resp_timeout_reported[ch_idx] <= 1'b0;
            end

            // Set timeout reported flags when timeouts are detected
            for (int ch = 0; ch < CHANNELS; ch++) begin
                // Set address timeout reported flag
                if (r_addr_timeout[ch]) begin
                    r_addr_timeout_reported[ch] <= 1'b1;
                end

                // Set data timeout reported flag
                if (r_data_timeout[ch]) begin
                    r_data_timeout_reported[ch] <= 1'b1;
                end

                // Set response timeout reported flag (write only)
                if (!IS_READ && r_resp_timeout[ch]) begin
                    r_resp_timeout_reported[ch] <= 1'b1;
                end
            end
        end
    end

    // -------------------------------------------------------------------------
    // FIFO Instantiations - Per Channel
    // -------------------------------------------------------------------------

    // Generate one address tracking FIFO per channel
    generate
        for (i = 0; i < CHANNELS; i++) begin : gen_channel_fifos
            // FIFO for address tracking
            gaxi_fifo_sync #(
                .DATA_WIDTH(AW),
                .DEPTH(AFD+1),
                .INSTANCE_NAME($sformatf("ADDR_FIFO_%0d", i))
            ) i_addr_fifo (
                .i_axi_aclk(aclk),
                .i_axi_aresetn(aresetn),
                .i_wr_valid(w_addr_fifo_wr_valid[i]),
                .o_wr_ready(w_addr_fifo_wr_ready[i]),
                .i_wr_data(w_addr_fifo_wr_data[i]),
                .i_rd_ready(w_addr_fifo_rd_ready[i]),
                .o_rd_valid(w_addr_fifo_rd_valid[i]),
                .ow_rd_data(w_addr_fifo_rd_data[i]),
                .o_rd_data(),
                .ow_count(w_addr_fifo_count[i])
            );
        end
    endgenerate

    // Create a single write data FIFO for tracking write data phases
    generate
        if (!IS_READ) begin : gen_write_data_fifo
            // Single FIFO for write data tracking
            gaxi_fifo_sync #(
                .DATA_WIDTH(AW+IW),
                .DEPTH(AFD+1),  // Same depth as address FIFO
                .INSTANCE_NAME("WDATA_FIFO")
            ) i_wdata_fifo (
                .i_axi_aclk(aclk),
                .i_axi_aresetn(aresetn),
                .i_wr_valid(w_wdata_fifo_wr_valid),
                .o_wr_ready(w_wdata_fifo_wr_ready),
                .i_wr_data(w_wdata_fifo_wr_data),
                .i_rd_ready(w_wdata_fifo_rd_ready),
                .o_rd_valid(w_wdata_fifo_rd_valid),
                .ow_rd_data(w_wdata_fifo_rd_data),
                .o_rd_data(),
                .ow_count(w_wdata_fifo_count)
            );
        end
    endgenerate

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
        .i_rd_ready(i_error_ready),
        .o_rd_valid(o_error_valid),
        .ow_rd_data({o_error_type, o_error_id, o_error_addr}),
        .o_rd_data(),
        .ow_count()
    );

    // -------------------------------------------------------------------------
    // Busy Generation Logic
    // -------------------------------------------------------------------------
    always_comb begin
        if (!IS_READ) begin
            o_busy = w_wdata_fifo_rd_valid || |w_addr_fifo_rd_valid;
        end else begin
            o_busy = |w_addr_fifo_rd_valid;
        end
    end

    // -------------------------------------------------------------------------
    // Address FIFO Control Logic
    // -------------------------------------------------------------------------

    logic w_block_ready;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn)
            o_block_ready <= 1'b0;
        else begin
            o_block_ready <= w_block_ready;
        end
    end

    // Address FIFO control - combinational logic
    /* verilator lint_off LATCH */
    /* verilator lint_off WIDTHEXPAND */
    always_comb begin
        // Flow control - block if any FIFO is almost full
        w_block_ready = 1'b0;
        for (int ch = 0; ch < CHANNELS; ch++) begin
            if (w_addr_fifo_count[ch] == AFD) begin
                w_block_ready = 1'b1;
            end
        end

        // For write mode, also check if write data FIFO is full
        if (!IS_READ && w_wdata_fifo_count == AFD) begin
            w_block_ready = 1'b1;
        end
    end
    /* verilator lint_on WIDTHEXPAND */

    always_comb begin
        // Initialize all signals and variables
        for (int ch = 0; ch < CHANNELS; ch++) begin
            w_addr_fifo_wr_valid[ch] = 1'b0;
            w_addr_fifo_wr_data[ch] = i_addr_addr;
            w_addr_fifo_rd_ready[ch] = 1'b0;
        end

        // Initialize write data FIFO signals
        if (!IS_READ) begin
            w_wdata_fifo_wr_valid = 1'b0;
            w_wdata_fifo_wr_data = {i_addr_addr, i_addr_id};  // Combined addr+id
            w_wdata_fifo_rd_ready = 1'b0;
        end

        // Determine which channel FIFO to write to for address
        if (i_addr_valid && i_addr_ready) begin
            automatic int ch_idx;
            ch_idx = get_channel_idx(i_addr_id);
            w_addr_fifo_wr_valid[ch_idx] = 1'b1;

            // For write mode, also write to the write data FIFO
            if (!IS_READ) begin
                w_wdata_fifo_wr_valid = 1'b1;
            end
        end

        // Address FIFO read control
        if (IS_READ) begin
            // Read response channel (R)
            if (i_data_valid && i_data_ready && i_data_last) begin
                automatic int ch_idx;
                ch_idx = get_channel_idx(i_data_id);
                if (w_addr_fifo_rd_valid[ch_idx])
                    w_addr_fifo_rd_ready[ch_idx] = 1'b1;
            end
        end else begin
            // Write response channel (B)
            if (i_resp_valid && i_resp_ready) begin
                automatic int ch_idx;
                ch_idx = get_channel_idx(i_resp_id);
                w_addr_fifo_rd_ready[ch_idx] = 1'b1;
            end

            // Write data FIFO read control - pop entry when data phase completes
            if (i_data_valid && i_data_ready && i_data_last) begin
                w_wdata_fifo_rd_ready = 1'b1;
            end
        end
    end
    /* verilator lint_on LATCH */

    // -------------------------------------------------------------------------
    // Generate response error signals
    // -------------------------------------------------------------------------

    logic [CHANNELS-1:0] w_resp_error;

    /* verilator lint_off LATCH */
    always_comb begin
        // Initialize to prevent latches
        for (int ch = 0; ch < CHANNELS; ch++) begin
            w_resp_error[ch] = 1'b0;
        end

        if (IS_READ) begin
            // Read response error
            if (i_data_valid && i_data_ready) begin
                automatic int ch_idx;
                ch_idx = get_channel_idx(i_data_id);

                // Check response code for errors (SLVERR or DECERR)
                w_resp_error[ch_idx] = i_data_resp[1];
            end
        end else begin
            // Write response error
            if (i_resp_valid && i_resp_ready) begin
                automatic int ch_idx;
                ch_idx = get_channel_idx(i_resp_id);

                // Check response code for errors (SLVERR or DECERR)
                w_resp_error[ch_idx] = i_resp[1];
            end
        end
    end
    /* verilator lint_on LATCH */

    // -------------------------------------------------------------------------
    // Error Detection and Priority Logic - Combinational
    // -------------------------------------------------------------------------

    // Combinational signals for error processing
    logic                           w_error_fifo_valid_next;
    logic [TEDW-1:0]                w_error_fifo_wr_data_next;
    logic [CHANNELS-1:0]            w_error_flag_addr_to_next;
    logic [CHANNELS-1:0][TEDW-1:0]  w_error_flag_addr_to_data_next;
    logic [CHANNELS-1:0]            w_error_flag_data_to_next;
    logic [CHANNELS-1:0][TEDW-1:0]  w_error_flag_data_to_data_next;
    logic [CHANNELS-1:0]            w_error_flag_resp_to_next;
    logic [CHANNELS-1:0][TEDW-1:0]  w_error_flag_resp_to_data_next;

    always_comb begin
        // Default values - keep current state
        w_error_fifo_valid_next = 1'b0;
        w_error_fifo_wr_data_next = r_error_fifo_wr_data;
        w_error_flag_addr_to_next = r_error_flag_addr_to;
        w_error_flag_addr_to_data_next = r_error_flag_addr_to_data;
        w_error_flag_data_to_next = r_error_flag_data_to;
        w_error_flag_data_to_data_next = r_error_flag_data_to_data;
        w_error_flag_resp_to_next = r_error_flag_resp_to;
        w_error_flag_resp_to_data_next = r_error_flag_resp_to_data;

        // Initialize error processing variables
        error_found = 1'b0;

        // Process errors by priority for each channel
        for (int ch = 0; ch < CHANNELS; ch++) begin
            // Skip this channel if we already found an error
            if (error_found)
                continue;

            // Reset for this channel
            current_err = ERR_NONE;
            current_err_data = '0;

            // Check response errors (highest priority)
            if (w_resp_error[ch]) begin
                current_err = ERR_RESP;
                if (IS_READ) begin
                    current_err_data = {ErrorRespError, i_data_id, w_addr_fifo_rd_data[ch]};
                end else begin
                    current_err_data = {ErrorRespError, i_resp_id, w_addr_fifo_rd_data[ch]};
                end
            end
            // Check address timeout
            else if ((r_addr_timeout[ch]) ||
                    r_error_flag_addr_to[ch]) begin
                current_err = ERR_ADDR_TO;
                current_err_data = (r_addr_timeout[ch]) ?
                    {ErrorAddrTimeout, r_addr_current_id, i_addr_addr} : r_error_flag_addr_to_data[ch];
            end
            // Check data timeout - only check channel 0 for write mode
            else if ((IS_READ && (r_data_timeout[ch] || r_error_flag_data_to[ch])) ||
                    (!IS_READ && ch == 0 && (r_data_timeout[ch] || r_error_flag_data_to[ch]))) begin
                current_err = ERR_DATA_TO;
                if (!IS_READ) begin
                    // For write mode, use the address/ID from the single write data FIFO
                    if (r_data_timeout[ch]) begin
                        // Only for channel 0 in write mode
                        if (w_wdata_fifo_rd_valid) begin
                            // Extract addr and id from the combined value
                            automatic logic [AW-1:0] addr;
                            automatic logic [IW-1:0] id;

                            addr = w_wdata_fifo_rd_data[AW+IW-1:IW];
                            id = w_wdata_fifo_rd_data[IW-1:0];
                            current_err_data = {ErrorDataTimeout, id, addr};
                        end else begin
                            // Fallback if FIFO is empty
                            current_err_data = {ErrorDataTimeout, IW'(0), {AW{1'b0}}};
                        end
                    end else begin
                        // Use stored error data
                        current_err_data = r_error_flag_data_to_data[ch];
                    end
                end else begin
                    // For read mode, use stored original ID for this channel
                    if (r_data_timeout[ch]) begin
                        // Use stored ID and address from FIFO
                        current_err_data[TEDW-1:TEDW-ETW] = ErrorDataTimeout;
                        current_err_data[TEDW-ETW-1:TEDW-ETW-IW] = r_channel_id[ch];

                        // Use address from FIFO if available, otherwise 0
                        if (w_addr_fifo_rd_valid[ch]) begin
                            current_err_data[TEDW-ETW-IW-1:0] = w_addr_fifo_rd_data[ch];
                        end else begin
                            current_err_data[TEDW-ETW-IW-1:0] = '0;
                        end
                    end else begin
                        // Use stored error data
                        current_err_data = r_error_flag_data_to_data[ch];
                    end
                end
            end
            // Check response timeout (write only)
            else if (!IS_READ && (r_resp_timeout[ch] || r_error_flag_resp_to[ch])) begin
                current_err = ERR_RESP_TO;
                current_err_data = r_resp_timeout[ch] ?
                    {ErrorRespTimeout, i_resp_id, w_addr_fifo_rd_data[ch]} :
                    r_error_flag_resp_to_data[ch];
            end

            // Process the current error if any
            if (current_err != ERR_NONE) begin
                error_found = 1'b1;  // Set flag to skip remaining channels

                if (w_error_fifo_ready) begin
                    // We can report the error immediately
                    w_error_fifo_valid_next = 1'b1;
                    w_error_fifo_wr_data_next = current_err_data;

                    // Clear any stored flags for this error
                    case (current_err)
                        ERR_ADDR_TO: begin
                            w_error_flag_addr_to_next[ch] = 1'b0;
                            w_error_flag_addr_to_data_next[ch] = '0;
                        end
                        ERR_DATA_TO: begin
                            w_error_flag_data_to_next[ch] = 1'b0;
                            w_error_flag_data_to_data_next[ch] = '0;
                        end
                        ERR_RESP_TO: begin
                            w_error_flag_resp_to_next[ch] = 1'b0;
                            w_error_flag_resp_to_data_next[ch] = '0;
                        end
                        default: ; // No stored flags for response errors
                    endcase
                end else begin
                    // Store for later if we can't report now
                    case (current_err)
                        ERR_ADDR_TO: begin
                            if (r_addr_timeout[ch]) begin
                                w_error_flag_addr_to_next[ch] = 1'b1;
                                w_error_flag_addr_to_data_next[ch] = current_err_data;
                            end
                        end
                        ERR_DATA_TO: begin
                            if (r_data_timeout[ch]) begin
                                w_error_flag_data_to_next[ch] = 1'b1;
                                w_error_flag_data_to_data_next[ch] = current_err_data;
                            end
                        end
                        ERR_RESP_TO: begin
                            if (r_resp_timeout[ch]) begin
                                w_error_flag_resp_to_next[ch] = 1'b1;
                                w_error_flag_resp_to_data_next[ch] = current_err_data;
                            end
                        end
                        default: ; // Can't store response errors, they'll be retried
                    endcase
                end
            end
        end
    end

    // -------------------------------------------------------------------------
    // Error Reporting Logic - Sequential
    // -------------------------------------------------------------------------

    // Register error signals from combinational logic
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_error_fifo_valid <= 1'b0;
            r_error_fifo_wr_data <= '0;
            r_error_flag_addr_to <= '0;
            r_error_flag_addr_to_data <= '0;
            r_error_flag_data_to <= '0;
            r_error_flag_data_to_data <= '0;
            r_error_flag_resp_to <= '0;
            r_error_flag_resp_to_data <= '0;
        end else begin
            r_error_fifo_valid <= w_error_fifo_valid_next;
            r_error_fifo_wr_data <= w_error_fifo_wr_data_next;
            r_error_flag_addr_to <= w_error_flag_addr_to_next;
            r_error_flag_addr_to_data <= w_error_flag_addr_to_data_next;
            r_error_flag_data_to <= w_error_flag_data_to_next;
            r_error_flag_data_to_data <= w_error_flag_data_to_data_next;
            r_error_flag_resp_to <= w_error_flag_resp_to_next;
            r_error_flag_resp_to_data <= w_error_flag_resp_to_data_next;
        end
    end

    assign o_error_unit_id = 8'(UNIT_ID);
    assign o_error_agent_id = 8'(AGENT_ID);

endmodule : axi_errmon_base
