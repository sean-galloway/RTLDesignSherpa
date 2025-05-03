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
    // General parameters
    parameter int CHANNELS           = 1,    // Number of channels to monitor
    parameter int ADDR_WIDTH         = 32,   // Width of address bus
    parameter int ID_WIDTH           = 8,    // Width of ID bus (0 for AXIL)

    // Timeout parameters (in clock cycles)
    parameter int TIMER_WIDTH        = 20,   // Width of timeout counters
    parameter int TIMEOUT_ADDR       = 1000, // Address channel timeout
    parameter int TIMEOUT_DATA       = 1000, // Data channel timeout
    parameter int TIMEOUT_RESP       = 1000, // Response channel timeout (only for write)

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
    parameter int ETW                = 4               // Error type width (fixed)
)
(
    // Global Clock and Reset
    input  logic                     aclk,
    input  logic                     aresetn,

    // Address channel (AW/AR)
    input  logic [AW-1:0]            i_addr,         // Address value
    input  logic [IW-1:0]            i_id,           // Transaction ID
    input  logic                     i_valid,        // Address valid
    input  logic                     i_ready,        // Address ready

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

    // Error outputs FIFO interface
    output logic                     o_error_valid,
    input  logic                     i_error_ready,
    output logic [ETW-1:0]           o_error_type,
    output logic [AW-1:0]            o_error_addr,
    output logic [IW-1:0]            o_error_id,

    // Flow control output
    output logic                     o_block_ready
);

    // Define the read/write-specific error types (one-hot encoding)
    localparam logic [ETW-1:0] ErrorAddrTimeout = 4'b0001;  // AW/AR timeout
    localparam logic [ETW-1:0] ErrorDataTimeout = 4'b0010;  // W/R timeout
    localparam logic [ETW-1:0] ErrorRespTimeout = 4'b0100;  // B timeout (write only)
    localparam logic [ETW-1:0] ErrorRespError   = 4'b1000;  // B/R response error

    // Total Error Data Width for FIFO
    localparam int TEDW = AW + IW + ETW;

    // -------------------------------------------------------------------------
    // Direct timeout monitoring signals - Optimized Timer Architecture
    // -------------------------------------------------------------------------

    // Address channel timeout monitoring (single timer)
    logic                       r_addr_active;    // Address transaction in progress
    logic [TIMER_WIDTH-1:0]     r_addr_timer;     // Address timeout counter
    logic                       r_addr_timeout;   // Address timeout detected
    logic [IW-1:0]              r_addr_current_id; // Current transaction ID

    // Data channel timeout monitoring (per-channel)
    logic [CHANNELS-1:0]        r_data_active;    // Data transaction in progress
    logic [CHANNELS-1:0][TIMER_WIDTH-1:0] r_data_timer; // Data timeout counter
    logic [CHANNELS-1:0]        r_data_timeout;   // Data timeout detected

    // Response channel timeout monitoring (write only, per-channel)
    logic [CHANNELS-1:0]        r_resp_active;    // Response transaction in progress
    logic [CHANNELS-1:0][TIMER_WIDTH-1:0] r_resp_timer; // Response timeout counter
    logic [CHANNELS-1:0]        r_resp_timeout;   // Response timeout detected

    // -------------------------------------------------------------------------
    // Address FIFO tracking
    // -------------------------------------------------------------------------

    // Address FIFO signals - one per channel
    logic [CHANNELS-1:0]            w_addr_fifo_wr_valid;
    logic [CHANNELS-1:0]            w_addr_fifo_wr_ready;
    logic [CHANNELS-1:0][AW-1:0]    w_addr_fifo_wr_data;
    logic [CHANNELS-1:0]            w_addr_fifo_rd_valid;
    logic [CHANNELS-1:0]            w_addr_fifo_rd_ready;
    logic [CHANNELS-1:0][AW-1:0]    w_addr_fifo_rd_data;

    // Add signals for a single write data FIFO (not per-channel)
    logic w_wdata_fifo_wr_valid;
    logic w_wdata_fifo_wr_ready;
    logic [AW+IW-1:0] w_wdata_fifo_wr_data;  // Combined addr+id for write data tracking
    logic w_wdata_fifo_rd_valid;
    logic w_wdata_fifo_rd_ready;
    logic [AW+IW-1:0] w_wdata_fifo_rd_data;  // Combined addr+id from FIFO

    // Error reporting signals
    logic                     r_error_fifo_valid;
    logic [TEDW-1:0]          r_error_fifo_wr_data;
    logic                     w_error_fifo_ready;

    // Error flag storage to prevent loss during processing
    logic [CHANNELS-1:0]         r_error_flag_addr_to;
    logic [CHANNELS-1:0][TEDW-1:0] r_error_flag_addr_to_data;
    logic [CHANNELS-1:0]         r_error_flag_data_to;
    logic [CHANNELS-1:0][TEDW-1:0] r_error_flag_data_to_data;
    logic [CHANNELS-1:0]         r_error_flag_resp_to;
    logic [CHANNELS-1:0][TEDW-1:0] r_error_flag_resp_to_data;

    // Intermediate signals for timeout detection
    logic                       w_addr_active_next;
    logic [TIMER_WIDTH-1:0]     w_addr_timer_next;
    logic                       w_addr_timeout_next;
    logic [IW-1:0]              w_addr_current_id_next;

    logic [CHANNELS-1:0]        w_data_active_next;
    logic [CHANNELS-1:0][TIMER_WIDTH-1:0] w_data_timer_next;
    logic [CHANNELS-1:0]        w_data_timeout_next;

    logic [CHANNELS-1:0]        w_resp_active_next;
    logic [CHANNELS-1:0][TIMER_WIDTH-1:0] w_resp_timer_next;
    logic [CHANNELS-1:0]        w_resp_timeout_next;

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
    // FIFO Instantiations - Per Channel
    // -------------------------------------------------------------------------

    // Generate one address tracking FIFO per channel
    genvar i;
    generate
        for (i = 0; i < CHANNELS; i++) begin : gen_channel_fifos
            // FIFO for address tracking
            gaxi_fifo_sync #(
                .DATA_WIDTH(AW),
                .DEPTH(AFD),
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
                .ow_count()
            );
        end
    endgenerate

    // Create a single write data FIFO for tracking write data phases
    generate
        if (!IS_READ) begin : gen_write_data_fifo
            // Single FIFO for write data tracking
            gaxi_fifo_sync #(
                .DATA_WIDTH(AW+IW),
                .DEPTH(AFD),  // Same depth as address FIFO
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
                .ow_count()
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
    // Address FIFO Control Logic
    // -------------------------------------------------------------------------

    // Address FIFO control - combinational logic
    /* verilator lint_off LATCH */
    always_comb begin
        // Initialize all signals and variables
        for (int ch = 0; ch < CHANNELS; ch++) begin
            w_addr_fifo_wr_valid[ch] = 1'b0;
            w_addr_fifo_wr_data[ch] = i_addr;
            w_addr_fifo_rd_ready[ch] = 1'b0;
        end

        // Initialize write data FIFO signals
        if (!IS_READ) begin
            w_wdata_fifo_wr_valid = 1'b0;
            w_wdata_fifo_wr_data = {i_addr, i_id};  // Combined addr+id
            w_wdata_fifo_rd_ready = 1'b0;
        end

        // Determine which channel FIFO to write to for address
        if (i_valid && i_ready) begin
            automatic int ch_idx;
            ch_idx = get_channel_idx(i_id);
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

        // Flow control - block if any FIFO is full
        o_block_ready = 1'b0;
        for (int ch = 0; ch < CHANNELS; ch++) begin
            if (!w_addr_fifo_wr_ready[ch]) begin
                o_block_ready = 1'b1;
                break;
            end
        end

        // For write mode, also check if write data FIFO is full
        if (!IS_READ && !w_wdata_fifo_wr_ready) begin
            o_block_ready = 1'b1;
        end
    end
    /* verilator lint_on LATCH */

    // -------------------------------------------------------------------------
    // Address Channel Timeout Monitor - Combinational Logic
    // -------------------------------------------------------------------------

    /* verilator lint_off LATCH */
    always_comb begin
        // Default: keep current state
        w_addr_active_next = r_addr_active;
        w_addr_timer_next = r_addr_timer;
        w_addr_timeout_next = 1'b0;  // Timeout is cleared each cycle by default
        w_addr_current_id_next = r_addr_current_id;

        // Check timeout conditions based on valid/ready
        if (i_valid && !i_ready) begin
            // Address transaction is waiting for ready
            if (!r_addr_active) begin
                // Start monitoring
                w_addr_active_next = 1'b1;
                w_addr_timer_next = '0;
                w_addr_current_id_next = i_id;  // Store the ID
            end else begin
                // Continue monitoring
                w_addr_timer_next = r_addr_timer + {{(TIMER_WIDTH-1){1'b0}}, 1'b1};

                // Check for timeout - use explicit cast to match widths
                if (r_addr_timer >= TIMER_WIDTH'(TIMEOUT_ADDR)) begin
                    w_addr_timeout_next = 1'b1;
                    w_addr_timer_next = 'b0;
                    w_addr_active_next = 1'b0; // Reset for next time
                end
            end
        end else if (i_valid && i_ready) begin
            // Successful handshake
            w_addr_active_next = 1'b0;
            w_addr_timer_next = '0;
        end else if (r_addr_active && !i_valid) begin
            // Transaction disappeared
            w_addr_active_next = 1'b0;
            w_addr_timer_next = '0;
        end
    end
    /* verilator lint_on LATCH */

    // Address Channel Timeout Monitor - Sequential Logic
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_addr_active <= 1'b0;
            r_addr_timer <= '0;
            r_addr_timeout <= 1'b0;
            r_addr_current_id <= '0;
        end else begin
            r_addr_active <= w_addr_active_next;
            r_addr_timer <= w_addr_timer_next;
            r_addr_timeout <= w_addr_timeout_next;
            r_addr_current_id <= w_addr_current_id_next;
        end
    end

    // -------------------------------------------------------------------------
    // Data Channel Timeout Monitor - Combinational Logic
    // -------------------------------------------------------------------------

    /* verilator lint_off LATCH */
    always_comb begin
        // Default: keep current state
        w_data_active_next = r_data_active;
        w_data_timer_next = r_data_timer;
        w_data_timeout_next = '0;  // Timeouts are cleared each cycle by default

        // First, handle new address transactions (reset timers)
        if (i_valid && i_ready) begin
            automatic int ch_idx;
            ch_idx = get_channel_idx(i_id);
            // Reset the data timer for this channel to 0 (starting state)
            w_data_timer_next[ch_idx] = '0;
            w_data_active_next[ch_idx] = 1'b0; // Not active yet
        end

        // Then handle data channel timing for each channel
        for (int ch = 0; ch < CHANNELS; ch++) begin
            if (IS_READ) begin
                // Read data channel - use channel index from data ID
                automatic int ch_idx;
                ch_idx = get_channel_idx(i_data_id);

                if (i_data_valid && !i_data_ready && (ch_idx == ch)) begin
                    // Data transaction is waiting for ready
                    if (!r_data_active[ch]) begin
                        // Start monitoring
                        w_data_active_next[ch] = 1'b1;
                    end

                    // Increment timer (count up from 0)
                    w_data_timer_next[ch] = r_data_timer[ch] + {{(TIMER_WIDTH-1){1'b0}}, 1'b1};

                    // Check for timeout - use explicit cast to match widths
                    if (r_data_timer[ch] >= TIMER_WIDTH'(TIMEOUT_DATA)) begin
                        w_data_timeout_next[ch] = 1'b1;
                        w_data_timer_next[ch] = 'b0;
                        w_data_active_next[ch] = 1'b0; // Reset for next time
                    end
                end else if (i_data_valid && i_data_ready && (ch_idx == ch)) begin
                    // Successful handshake
                    w_data_active_next[ch] = 1'b0;
                    // Reset timer to 0
                    w_data_timer_next[ch] = '0;
                end else if (r_data_active[ch] && !(i_data_valid && (ch_idx == ch))) begin
                    // Transaction disappeared
                    w_data_active_next[ch] = 1'b0;
                    // Reset timer to 0
                    w_data_timer_next[ch] = '0;
                end
            end else begin
                // Write data channel - ONLY USE CHANNEL 0
                if (ch == 0) begin  // Only monitor channel 0 for write data
                    if (i_data_valid && !i_data_ready) begin
                        // Data transaction is waiting for ready
                        if (!r_data_active[ch]) begin
                            // Start monitoring
                            w_data_active_next[ch] = 1'b1;
                        end

                        // Increment timer (count up from 0)
                        w_data_timer_next[ch] = r_data_timer[ch] + {{(TIMER_WIDTH-1){1'b0}}, 1'b1};

                        // Check for timeout - use explicit cast to match widths
                        if (r_data_timer[ch] >= TIMER_WIDTH'(TIMEOUT_DATA)) begin
                            w_data_timeout_next[ch] = 1'b1;
                            w_data_timer_next[ch] = 'b0;
                            w_data_active_next[ch] = 1'b0; // Reset for next time
                        end
                    end else if (i_data_valid && i_data_ready) begin
                        // Successful handshake
                        w_data_active_next[ch] = 1'b0;
                        // Reset timer to 0
                        w_data_timer_next[ch] = '0;
                    end else if (r_data_active[ch] && !i_data_valid) begin
                        // Transaction disappeared
                        w_data_active_next[ch] = 1'b0;
                        // Reset timer to 0
                        w_data_timer_next[ch] = '0;
                    end
                end else begin
                    // For all other channels in write mode, always reset data timers
                    w_data_active_next[ch] = 1'b0;
                    w_data_timer_next[ch] = '0;
                    w_data_timeout_next[ch] = 1'b0;
                end
            end
        end
    end
    /* verilator lint_on LATCH */

    // Data Channel Timeout Monitor - Sequential Logic
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_data_active <= '0;
            // Initialize timers to 0 (inactive state)
            for (int ch = 0; ch < CHANNELS; ch++) begin
                r_data_timer[ch] <= '0;
            end
            r_data_timeout <= '0;
        end else begin
            r_data_active <= w_data_active_next;
            r_data_timer <= w_data_timer_next;
            r_data_timeout <= w_data_timeout_next;
        end
    end

    // -------------------------------------------------------------------------
    // Response Channel Timeout Monitor (Write only) - Combinational Logic
    // -------------------------------------------------------------------------

    generate
        if (!IS_READ) begin : gen_write_resp_monitor_comb
            /* verilator lint_off LATCH */
            always_comb begin
                // Default: keep current state
                w_resp_active_next = r_resp_active;
                w_resp_timer_next = r_resp_timer;
                w_resp_timeout_next = '0;  // Timeouts are cleared each cycle by default

                // First, handle new address transactions
                if (i_valid && i_ready) begin
                    automatic int ch_idx;
                    ch_idx = get_channel_idx(i_id);
                    // Reset the response timer for this channel to 0 (starting state)
                    w_resp_timer_next[ch_idx] = '0;
                    w_resp_active_next[ch_idx] = 1'b0; // Not active yet
                end

                // Then handle response channel timing
                for (int ch = 0; ch < CHANNELS; ch++) begin
                    automatic int ch_idx;
                    ch_idx = get_channel_idx(i_resp_id);

                    if (i_resp_valid && !i_resp_ready && (ch_idx == ch)) begin
                        // Response transaction is waiting for ready
                        if (!r_resp_active[ch]) begin
                            // Start monitoring
                            w_resp_active_next[ch] = 1'b1;
                        end

                        // Increment timer (count up from 0)
                        w_resp_timer_next[ch] = r_resp_timer[ch] + {{(TIMER_WIDTH-1){1'b0}}, 1'b1};

                        // Check for timeout - use explicit cast to match widths
                        if (r_resp_timer[ch] >= TIMER_WIDTH'(TIMEOUT_RESP)) begin
                            w_resp_timeout_next[ch] = 1'b1;
                            w_resp_timer_next[ch] = 'b0;
                            w_resp_active_next[ch] = 1'b0; // Reset for next time
                        end
                    end else if (i_resp_valid && i_resp_ready && (ch_idx == ch)) begin
                        // Successful handshake
                        w_resp_active_next[ch] = 1'b0;
                        // Reset timer to 0
                        w_resp_timer_next[ch] = '0;
                    end else if (r_resp_active[ch] && !(i_resp_valid && (ch_idx == ch))) begin
                        // Transaction disappeared
                        w_resp_active_next[ch] = 1'b0;
                        // Reset timer to 0
                        w_resp_timer_next[ch] = '0;
                    end
                end
            end
            /* verilator lint_on LATCH */
        end
    endgenerate

    // Response Channel Timeout Monitor - Sequential Logic
    generate
        if (!IS_READ) begin : gen_write_resp_monitor_seq
            always_ff @(posedge aclk or negedge aresetn) begin
                if (!aresetn) begin
                    r_resp_active <= '0;
                    // Initialize timers to 0 (inactive state)
                    for (int ch = 0; ch < CHANNELS; ch++) begin
                        r_resp_timer[ch] <= '0;
                    end
                    r_resp_timeout <= '0;
                end else begin
                    r_resp_active <= w_resp_active_next;
                    r_resp_timer <= w_resp_timer_next;
                    r_resp_timeout <= w_resp_timeout_next;
                end
            end
        end else begin : gen_no_write_resp_monitor
            // Not used for read - tie to zeros
            always_comb begin
                r_resp_active = '0;
                r_resp_timeout = '0;
                w_resp_active_next = '0;
                w_resp_timer_next = '0;
                w_resp_timeout_next = '0;
            end
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Error Detection and Reporting Logic
    // -------------------------------------------------------------------------

    // Intermediate signals
    logic [CHANNELS-1:0] w_resp_error;

    // Generate response error signals
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
    logic w_error_fifo_valid_next;
    logic [TEDW-1:0] w_error_fifo_wr_data_next;
    logic [CHANNELS-1:0] w_error_flag_addr_to_next;
    logic [CHANNELS-1:0][TEDW-1:0] w_error_flag_addr_to_data_next;
    logic [CHANNELS-1:0] w_error_flag_data_to_next;
    logic [CHANNELS-1:0][TEDW-1:0] w_error_flag_data_to_data_next;
    logic [CHANNELS-1:0] w_error_flag_resp_to_next;
    logic [CHANNELS-1:0][TEDW-1:0] w_error_flag_resp_to_data_next;

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
            else if ((r_addr_timeout && (get_channel_idx(r_addr_current_id) == ch)) ||
                    r_error_flag_addr_to[ch]) begin
                current_err = ERR_ADDR_TO;
                current_err_data = (r_addr_timeout && (get_channel_idx(r_addr_current_id) == ch)) ?
                    {ErrorAddrTimeout, r_addr_current_id, i_addr} : r_error_flag_addr_to_data[ch];
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
                    // For read mode, keep using the original approach with data_id
                    current_err_data = r_data_timeout[ch] ?
                        {ErrorDataTimeout, i_data_id, w_addr_fifo_rd_data[ch]} :
                        r_error_flag_data_to_data[ch];
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
                            if (r_addr_timeout && (get_channel_idx(r_addr_current_id) == ch)) begin
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

endmodule : axi_errmon_base