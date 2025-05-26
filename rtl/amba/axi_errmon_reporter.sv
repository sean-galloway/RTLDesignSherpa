`timescale 1ns / 1ps

/**
 * AXI Interrupt Bus Reporter
 *
 * This module reports events and errors through a shared interrupt bus.
 * It detects conditions from the AXI transaction table and formats them into
 * standard 64-bit interrupt packet format for system-wide event notification.
 * Optionally tracks performance metrics when ENABLE_PERF_PACKETS is enabled.
 *
 * Updated with proper naming conventions: w_ for combo, r_ for flopped
 * Fixed for Verilator compatibility
 */
module axi_errmon_reporter
    import axi_errmon_types::*;
#(
    parameter int MAX_TRANSACTIONS    = 16,   // Maximum outstanding transactions
    parameter int ADDR_WIDTH          = 32,   // Width of address bus
    parameter int UNIT_ID             = 9,    // Unit identifier (4 bits used)
    parameter int AGENT_ID            = 99,   // Agent identifier (8 bits used)
    parameter bit IS_READ             = 1'b1,    // 1 for read, 0 for write
    parameter bit ENABLE_PERF_PACKETS = 1'b0,    // Enable performance metrics tracking
    parameter int INTR_FIFO_DEPTH     = 8     // interrupt fifo depth
)
(
    // Global Clock and Reset
    input  logic                     aclk,
    input  logic                     aresetn,

    // Transaction table (read-only access)
    input  axi_transaction_t [MAX_TRANSACTIONS-1:0] i_trans_table,

    // Configuration enables for different packet types
    input  logic                     i_cfg_error_enable,    // Enable error packets
    input  logic                     i_cfg_compl_enable,    // Enable completion packets
    input  logic                     i_cfg_threshold_enable,// Enable threshold packets
    input  logic                     i_cfg_timeout_enable,  // Enable timeout packets
    input  logic                     i_cfg_perf_enable,     // Enable performance packets
    input  logic                     i_cfg_debug_enable,    // Enable debug packets

    // Interrupt bus output interface
    input  logic                     i_intrbus_ready,  // Downstream ready
    output logic                     o_intrbus_valid,  // Interrupt valid
    output logic [63:0]              o_intrbus_packet, // Consolidated interrupt packet

    // Statistics output
    output logic [15:0]              o_event_count,    // Total event count

    // Performance metrics (only used when ENABLE_PERF_PACKETS=1)
    output logic [15:0]              o_perf_completed_count, // Number of completed transactions
    output logic [15:0]              o_perf_error_count,     // Number of error transactions

    // Performance metric thresholds
    input  logic [15:0]              i_active_trans_threshold,
    input  logic [31:0]              i_latency_threshold
);

    // Local version of transaction table for processing (flopped)
    axi_transaction_t r_trans_table_local[MAX_TRANSACTIONS];

    // Flag to track if event has been reported for each transaction (flopped)
    logic [MAX_TRANSACTIONS-1:0] r_event_reported;

    // Threshold crossing flags (flopped)
    logic r_active_threshold_crossed;
    logic r_latency_threshold_crossed;

    // Event count (flopped)
    logic [15:0] r_event_count;
    assign o_event_count = r_event_count;

    // Performance metrics counters (flopped)
    logic [15:0] r_perf_completed_count;
    logic [15:0] r_perf_error_count;

    // Assign performance metrics outputs
    assign o_perf_completed_count = r_perf_completed_count;
    assign o_perf_error_count = r_perf_error_count;

    // Performance report state machine (flopped)
    logic [2:0] r_perf_report_state;

    // Interrupt FIFO entry type
    typedef struct packed {
        logic [3:0]            packet_type;  // Packet type
        logic [3:0]            event_code;   // Event code or metric type
        logic [5:0]            channel;      // Channel information
        logic [37:0]           data;         // Address or metric value - fixed to 38 bits
    } intrbus_entry_t;

    // FIFO signals (combinational)
    logic                                 w_fifo_wr_valid;
    logic                                 w_fifo_wr_ready;
    intrbus_entry_t                       w_fifo_wr_data;
    logic                                 w_fifo_rd_valid;
    logic                                 w_fifo_rd_ready;
    intrbus_entry_t                       w_fifo_rd_data;
    logic [$clog2(INTR_FIFO_DEPTH):0]    w_fifo_count;  // Proper width calculation

    // Use gaxi_fifo_sync for the interrupt packet FIFO
    gaxi_fifo_sync #(
        .DATA_WIDTH($bits(intrbus_entry_t)),
        .DEPTH(INTR_FIFO_DEPTH),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1),
        .INSTANCE_NAME("INTR_FIFO")
    ) intr_fifo (
        .i_axi_aclk(aclk),
        .i_axi_aresetn(aresetn),
        .i_wr_valid(w_fifo_wr_valid),
        .o_wr_ready(w_fifo_wr_ready),
        .i_wr_data(w_fifo_wr_data),
        .i_rd_ready(w_fifo_rd_ready),
        .ow_count(w_fifo_count),
        .o_rd_valid(w_fifo_rd_valid),
        .ow_rd_data(w_fifo_rd_data),
        .o_rd_data()  // Not used
    );

    // Output registers (flopped)
    logic [3:0]  r_packet_type;
    logic [3:0]  r_event_code;
    logic [37:0] r_event_data;  // Fixed width to 38 bits for proper packet format
    logic [5:0]  r_event_channel;

    // Event detection signals - One for each type of event to report (combinational)
    logic [MAX_TRANSACTIONS-1:0] w_error_events_detected;
    logic [MAX_TRANSACTIONS-1:0] w_timeout_events_detected;
    logic [MAX_TRANSACTIONS-1:0] w_completion_events_detected;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] w_selected_error_idx;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] w_selected_timeout_idx;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] w_selected_completion_idx;
    logic w_has_error_event;
    logic w_has_timeout_event;
    logic w_has_completion_event;

    // Error event detection
    always_comb begin
        w_error_events_detected = '0;
        w_selected_error_idx = '0;
        w_has_error_event = 1'b0;

        // Scan for error events
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (r_trans_table_local[idx].valid && !r_event_reported[idx] &&
                    r_trans_table_local[idx].state == TRANS_ERROR && i_cfg_error_enable &&
                    !(i_cfg_timeout_enable &&
                    (r_trans_table_local[idx].error_code == EVT_ADDR_TIMEOUT ||
                        r_trans_table_local[idx].error_code == EVT_DATA_TIMEOUT ||
                        r_trans_table_local[idx].error_code == EVT_RESP_TIMEOUT))) begin
                w_error_events_detected[idx] = 1'b1;
            end
        end

        // Priority encoder to select the first detected error
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (w_error_events_detected[idx] && !w_has_error_event) begin
                /* verilator lint_off WIDTHTRUNC */
                w_selected_error_idx = idx[$clog2(MAX_TRANSACTIONS)-1:0];
                /* verilator lint_on WIDTHTRUNC */
                w_has_error_event = 1'b1;
            end
        end
    end

    // Timeout event detection
    always_comb begin
        w_timeout_events_detected = '0;
        w_selected_timeout_idx = '0;
        w_has_timeout_event = 1'b0;

        // Scan for timeout events
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (r_trans_table_local[idx].valid && !r_event_reported[idx] &&
                r_trans_table_local[idx].state == TRANS_ERROR && i_cfg_timeout_enable &&
                (r_trans_table_local[idx].error_code == EVT_ADDR_TIMEOUT ||
                    r_trans_table_local[idx].error_code == EVT_DATA_TIMEOUT ||
                    r_trans_table_local[idx].error_code == EVT_RESP_TIMEOUT)) begin
                w_timeout_events_detected[idx] = 1'b1;
            end
        end

        // Priority encoder to select the first detected timeout
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (w_timeout_events_detected[idx] && !w_has_timeout_event) begin
                /* verilator lint_off WIDTHTRUNC */
                w_selected_timeout_idx = idx[$clog2(MAX_TRANSACTIONS)-1:0];
                /* verilator lint_on WIDTHTRUNC */
                w_has_timeout_event = 1'b1;
            end
        end
    end

    // Completion event detection
    always_comb begin
        w_completion_events_detected = '0;
        w_selected_completion_idx = '0;
        w_has_completion_event = 1'b0;

        // Scan for completion events
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (r_trans_table_local[idx].valid && !r_event_reported[idx] &&
                r_trans_table_local[idx].state == TRANS_COMPLETE && i_cfg_compl_enable) begin
                w_completion_events_detected[idx] = 1'b1;
            end
        end

        // Priority encoder to select the first detected completion
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (w_completion_events_detected[idx] && !w_has_completion_event) begin
                /* verilator lint_off WIDTHTRUNC */
                w_selected_completion_idx = idx[$clog2(MAX_TRANSACTIONS)-1:0];
                /* verilator lint_on WIDTHTRUNC */
                w_has_completion_event = 1'b1;
            end
        end
    end

    // FIFO write interface - combines all event detections
    always_comb begin
        w_fifo_wr_valid = 1'b0;
        w_fifo_wr_data = '{default: '0};

        // Priority: Error > Timeout > Completion
        if (w_has_error_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeError;
            w_fifo_wr_data.event_code = r_trans_table_local[w_selected_error_idx].error_code;
            w_fifo_wr_data.channel = r_trans_table_local[w_selected_error_idx].channel[5:0];
            /* verilator lint_off WIDTHTRUNC */
            w_fifo_wr_data.data = {{(38-ADDR_WIDTH){1'b0}}, r_trans_table_local[w_selected_error_idx].addr[ADDR_WIDTH-1:0]};
            /* verilator lint_on WIDTHTRUNC */
        end else if (w_has_timeout_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeTimeout;
            w_fifo_wr_data.event_code = r_trans_table_local[w_selected_timeout_idx].error_code;
            w_fifo_wr_data.channel = r_trans_table_local[w_selected_timeout_idx].channel[5:0];
            /* verilator lint_off WIDTHTRUNC */
            w_fifo_wr_data.data = {{(38-ADDR_WIDTH){1'b0}}, r_trans_table_local[w_selected_timeout_idx].addr[ADDR_WIDTH-1:0]};
            /* verilator lint_on WIDTHTRUNC */
        end else if (w_has_completion_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeCompletion;
            w_fifo_wr_data.event_code = EVT_TRANS_COMPLETE;
            w_fifo_wr_data.channel = r_trans_table_local[w_selected_completion_idx].channel[5:0];
            /* verilator lint_off WIDTHTRUNC */
            w_fifo_wr_data.data = {{(38-ADDR_WIDTH){1'b0}}, r_trans_table_local[w_selected_completion_idx].addr[ADDR_WIDTH-1:0]};
            /* verilator lint_on WIDTHTRUNC */
        end
    end

    // FIFO read interface and event processing
    assign w_fifo_rd_ready = i_intrbus_ready && o_intrbus_valid;

    // Event marking signals (combinational)
    logic [MAX_TRANSACTIONS-1:0] w_events_to_mark;
    logic [MAX_TRANSACTIONS-1:0] w_error_events;
    logic [MAX_TRANSACTIONS-1:0] w_completion_events;

    // Active transaction count for threshold detection (combinational)
    logic [7:0] w_active_count_current;
    logic w_active_threshold_detection;

    // Latency threshold detection signals (combinational)
    logic [MAX_TRANSACTIONS-1:0] w_latency_threshold_events;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] w_selected_latency_idx;
    logic w_has_latency_event;

    // Detect events that need to be marked as reported
    always_comb begin
        w_events_to_mark = '0;
        w_error_events = '0;
        w_completion_events = '0;

        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (r_trans_table_local[idx].valid) begin
                if ((r_trans_table_local[idx].state == TRANS_ERROR ||
                        r_trans_table_local[idx].state == TRANS_COMPLETE) &&
                        !r_event_reported[idx] && w_fifo_wr_valid && w_fifo_wr_ready) begin

                    w_events_to_mark[idx] = 1'b1;

                    if (r_trans_table_local[idx].state == TRANS_ERROR) begin
                        w_error_events[idx] = 1'b1;
                    end else if (r_trans_table_local[idx].state == TRANS_COMPLETE) begin
                        w_completion_events[idx] = 1'b1;
                    end
                end
            end
        end
    end

    // Active transaction count calculation
    always_comb begin
        w_active_count_current = '0;

        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (r_trans_table_local[idx].valid &&
                r_trans_table_local[idx].state != TRANS_COMPLETE &&
                r_trans_table_local[idx].state != TRANS_ERROR) begin
                w_active_count_current = w_active_count_current + 1'b1;
            end
        end

        /* verilator lint_off WIDTHEXPAND */
        w_active_threshold_detection = (({8'h0, w_active_count_current} > i_active_trans_threshold) &&
                                        !r_active_threshold_crossed &&
                                        !o_intrbus_valid &&
                                        (w_fifo_rd_valid == 0));
        /* verilator lint_on WIDTHEXPAND */
    end

    // Latency threshold detection
    always_comb begin
        w_latency_threshold_events = '0;
        w_selected_latency_idx = '0;
        w_has_latency_event = 1'b0;

        if (ENABLE_PERF_PACKETS && i_cfg_perf_enable && i_cfg_threshold_enable) begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (r_trans_table_local[idx].valid && r_trans_table_local[idx].state == TRANS_COMPLETE) begin
                    logic [31:0] w_total_latency;
                    if (IS_READ) begin
                        w_total_latency = r_trans_table_local[idx].data_timestamp - r_trans_table_local[idx].addr_timestamp;
                    end else begin
                        w_total_latency = r_trans_table_local[idx].resp_timestamp - r_trans_table_local[idx].addr_timestamp;
                    end

                    if (w_total_latency > i_latency_threshold && !r_latency_threshold_crossed) begin
                        w_latency_threshold_events[idx] = 1'b1;
                    end
                end
            end

            // Priority encoder to select the first latency threshold event
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (w_latency_threshold_events[idx] && !w_has_latency_event) begin
                    /* verilator lint_off WIDTHTRUNC */
                    w_selected_latency_idx = idx[$clog2(MAX_TRANSACTIONS)-1:0];
                    /* verilator lint_on WIDTHTRUNC */
                    w_has_latency_event = 1'b1;
                end
            end
        end
    end

    // Performance packet state and selection (combinational)
    logic w_generate_perf_packet_completed;
    logic w_generate_perf_packet_errors;
    logic [2:0] w_next_perf_report_state;

    always_comb begin
        w_next_perf_report_state = 3'h0;
        w_generate_perf_packet_completed = 1'b0;
        w_generate_perf_packet_errors = 1'b0;

        if (ENABLE_PERF_PACKETS && i_cfg_perf_enable && !o_intrbus_valid && w_fifo_rd_valid == 0) begin
            case (r_perf_report_state)
                3'h0: begin // ADDR_LATENCY
                    w_next_perf_report_state = 3'h1;
                end
                3'h1: begin // DATA_LATENCY
                    w_next_perf_report_state = 3'h2;
                end
                3'h2: begin // TOTAL_LATENCY
                    w_next_perf_report_state = 3'h3;
                end
                3'h3: begin // COMPLETED_COUNT
                    w_next_perf_report_state = 3'h4;
                    if (r_perf_completed_count > 0) begin
                        w_generate_perf_packet_completed = 1'b1;
                    end
                end
                3'h4: begin // ERROR_COUNT
                    w_next_perf_report_state = 3'h0;
                    if (r_perf_error_count > 0) begin
                        w_generate_perf_packet_errors = 1'b1;
                    end
                end
                default: w_next_perf_report_state = 3'h0;
            endcase
        end
    end

    // Event reporting logic - sequential logic only
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            // Reset local table and reporting state
            r_trans_table_local <= '{default: '0};
            o_intrbus_valid <= 1'b0;
            r_event_count <= '0;
            r_event_reported <= '0;
            o_intrbus_packet <= '0;

            // Reset performance counters
            r_perf_completed_count <= '0;
            r_perf_error_count <= '0;

            // Reset threshold flags
            r_active_threshold_crossed <= 1'b0;
            r_latency_threshold_crossed <= 1'b0;

            // Initialize packet construction registers
            r_packet_type <= PktTypeError;
            r_event_code <= EVT_NONE;
            r_event_data <= '0;
            r_event_channel <= '0;

            // Initialize performance report state
            r_perf_report_state <= 3'h0;
        end else begin
            // Update local transaction table element by element to avoid width issues
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_trans_table_local[idx] <= i_trans_table[idx];
            end

            // Handle packet output
            if (o_intrbus_valid && i_intrbus_ready) begin
                o_intrbus_valid <= 1'b0;
            end

            // Present next packet from FIFO
            if (!o_intrbus_valid && w_fifo_rd_valid) begin
                o_intrbus_valid <= 1'b1;
                r_packet_type <= w_fifo_rd_data.packet_type;
                r_event_code <= w_fifo_rd_data.event_code;
                r_event_data <= w_fifo_rd_data.data;
                r_event_channel <= w_fifo_rd_data.channel;
            end

            // Mark events as reported and update counters
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (w_events_to_mark[idx]) begin
                    r_event_reported[idx] <= 1'b1;
                    r_event_count <= r_event_count + 1'b1;
                end

                // Update performance counters
                if (ENABLE_PERF_PACKETS) begin
                    if (w_error_events[idx]) begin
                        r_perf_error_count <= r_perf_error_count + 1'b1;
                    end
                    if (w_completion_events[idx]) begin
                        r_perf_completed_count <= r_perf_completed_count + 1'b1;
                    end
                end
            end

            // Generate threshold packets if enabled
            if (i_cfg_threshold_enable) begin
                // Active transaction count threshold
                if (w_active_threshold_detection) begin
                    o_intrbus_valid <= 1'b1;
                    r_packet_type <= PktTypeThreshold;
                    r_event_code <= THRESH_ACTIVE_COUNT;
                    r_event_data <= {6'h0, {24'h0, w_active_count_current}};  // Zero-extend to 38 bits
                    r_event_channel <= '0;
                    r_active_threshold_crossed <= 1'b1;
                    r_event_count <= r_event_count + 1'b1;
                /* verilator lint_off WIDTHEXPAND */
                end else if (({8'h0, w_active_count_current} <= i_active_trans_threshold)) begin
                /* verilator lint_on WIDTHEXPAND */
                    r_active_threshold_crossed <= 1'b0;
                end

                // Latency threshold - Fixed syntax error
                if (w_has_latency_event && !o_intrbus_valid && w_fifo_rd_valid == 0) begin
                    logic [31:0] w_latency_temp;  // Temporary calculation variable

                    if (IS_READ) begin
                        w_latency_temp = r_trans_table_local[w_selected_latency_idx].data_timestamp -
                                        r_trans_table_local[w_selected_latency_idx].addr_timestamp;
                    end else begin
                        w_latency_temp = r_trans_table_local[w_selected_latency_idx].resp_timestamp -
                                        r_trans_table_local[w_selected_latency_idx].addr_timestamp;
                    end

                    o_intrbus_valid <= 1'b1;
                    r_packet_type <= PktTypeThreshold;
                    r_event_code <= THRESH_LATENCY;
                    /* verilator lint_off WIDTHTRUNC */
                    r_event_data <= {{(38-ADDR_WIDTH){1'b0}}, w_latency_temp[ADDR_WIDTH-1:0]};
                    /* verilator lint_on WIDTHTRUNC */
                    r_event_channel <= r_trans_table_local[w_selected_latency_idx].channel[5:0];
                    r_latency_threshold_crossed <= 1'b1;
                    r_event_count <= r_event_count + 1'b1;
                end
            end

            // Generate performance packets if enabled
            if (w_generate_perf_packet_completed) begin
                o_intrbus_valid <= 1'b1;
                r_packet_type <= PktTypePerf;
                r_event_code <= PERF_COMPLETED_COUNT;
                r_event_data <= {6'h0, {16'h0, r_perf_completed_count}};  // Zero-extend to 38 bits
                r_event_channel <= '0;
            end

            if (w_generate_perf_packet_errors) begin
                o_intrbus_valid <= 1'b1;
                r_packet_type <= PktTypePerf;
                r_event_code <= PERF_ERROR_COUNT;
                r_event_data <= {6'h0, {16'h0, r_perf_error_count}};     // Zero-extend to 38 bits
                r_event_channel <= '0;
            end

            // Update performance report state
            r_perf_report_state <= w_next_perf_report_state;
        end
    end

    // Construct the 64-bit interrupt bus packet
    always_comb begin
        // Initialize to zero
        o_intrbus_packet = '0;

        // 64-bit packet format:
        // - packet_type: 4 bits  [63:60] (error, completion, threshold, etc.)
        // - event_code:  4 bits  [59:56] (specific error or event code)
        // - channel_id:  6 bits  [55:50] (channel ID and AXI ID)
        // - unit_id:     4 bits  [49:46] (subsystem identifier)
        // - agent_id:    8 bits  [45:38] (module identifier)
        // - data:        38 bits [37:0]  (address or metric value)

        o_intrbus_packet[63:60] = r_packet_type;
        o_intrbus_packet[59:56] = r_event_code;
        o_intrbus_packet[55:50] = r_event_channel;
        o_intrbus_packet[49:46] = UNIT_ID[3:0];  // 4-bit Unit ID
        o_intrbus_packet[45:38] = AGENT_ID[7:0]; // 8-bit Agent ID

        // Address/data field (up to 38 bits)
        o_intrbus_packet[37:0] = r_event_data;
    end

endmodule : axi_errmon_reporter
