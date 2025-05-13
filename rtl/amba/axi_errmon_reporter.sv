`timescale 1ns / 1ps
/**
 * AXI Interrupt Bus Reporter
 *
 * This module reports events and errors through a shared interrupt bus.
 * It detects conditions from the AXI transaction table and formats them into
 * standard 64-bit interrupt packet format for system-wide event notification.
 * Optionally tracks performance metrics when ENABLE_PERF_PACKETS is enabled.
 */
module axi_errmon_reporter
#(
    parameter int MAX_TRANSACTIONS    = 16,   // Maximum outstanding transactions
    parameter int ADDR_WIDTH          = 32,   // Width of address bus
    parameter int UNIT_ID             = 9,    // Unit identifier (4 bits used)
    parameter int AGENT_ID            = 99,   // Agent identifier (8 bits used)
    parameter bit IS_READ             = 1,    // 1 for read, 0 for write
    parameter bit ENABLE_PERF_PACKETS = 0,    // Enable performance metrics tracking
    parameter int INTR_FIFO_DEPTH     = 8     // interrupt fifo depth
)
(
    // Global Clock and Reset
    input  logic                     aclk,
    input  logic                     aresetn,

    // Transaction table (read-only access)
    input  axi_errmon_types::axi_transaction_t [MAX_TRANSACTIONS-1:0] i_trans_table,

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

    import axi_errmon_types::*;

    // Local version of transaction table for processing
    axi_transaction_t trans_table_local[MAX_TRANSACTIONS];

    // Flag to track if event has been reported for each transaction
    logic [MAX_TRANSACTIONS-1:0] event_reported;

    // Threshold crossing flags
    logic active_threshold_crossed;
    logic latency_threshold_crossed;

    // Event count
    logic [15:0] event_count;
    assign o_event_count = event_count;

    // Performance metrics counters
    logic [15:0] perf_completed_count;
    logic [15:0] perf_error_count;

    // Assign performance metrics outputs
    assign o_perf_completed_count = perf_completed_count;
    assign o_perf_error_count = perf_error_count;

    // Interrupt FIFO entry type
    typedef struct packed {
        logic [3:0]       packet_type;  // Packet type
        logic [3:0]       event_code;   // Event code or metric type
        logic [5:0]       channel;      // Channel information
        logic [ADDR_WIDTH-1:0] data;    // Address or metric value
    } intrbus_entry_t;

    // FIFO signals
    logic                          fifo_wr_valid;
    logic                          fifo_wr_ready;
    intrbus_entry_t                fifo_wr_data;
    logic                          fifo_rd_valid;
    logic                          fifo_rd_ready;
    intrbus_entry_t                fifo_rd_data;
    logic [$clog2(INTR_FIFO_DEPTH+1)-1:0] fifo_count;

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
        .i_wr_valid(fifo_wr_valid),
        .o_wr_ready(fifo_wr_ready),
        .i_wr_data(fifo_wr_data),
        .i_rd_ready(fifo_rd_ready),
        .ow_count(fifo_count),
        .o_rd_valid(fifo_rd_valid),
        .ow_rd_data(fifo_rd_data),
        .o_rd_data()  // Not used
    );

    // Output registers
    logic [3:0]  packet_type;
    logic [3:0]  event_code;
    logic [ADDR_WIDTH-1:0] event_data;
    logic [5:0]  event_channel;

    // Event detection signals - One for each type of event to report
    logic [MAX_TRANSACTIONS-1:0] error_events_detected;
    logic [MAX_TRANSACTIONS-1:0] timeout_events_detected;
    logic [MAX_TRANSACTIONS-1:0] completion_events_detected;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] selected_error_idx;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] selected_timeout_idx;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] selected_completion_idx;
    logic has_error_event;
    logic has_timeout_event;
    logic has_completion_event;

    // Error event detection
    always_comb begin
        error_events_detected = '0;
        selected_error_idx = '0;
        has_error_event = 1'b0;

        // Scan for error events
        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (trans_table_local[i].valid && !event_reported[i] &&
                trans_table_local[i].state == TRANS_ERROR && i_cfg_error_enable &&
                !(i_cfg_timeout_enable &&
                 (trans_table_local[i].error_code == EVT_ADDR_TIMEOUT ||
                  trans_table_local[i].error_code == EVT_DATA_TIMEOUT ||
                  trans_table_local[i].error_code == EVT_RESP_TIMEOUT))) begin
                error_events_detected[i] = 1'b1;
            end
        end

        // Priority encoder to select the first detected error
        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (error_events_detected[i] && !has_error_event) begin
                selected_error_idx = i[$clog2(MAX_TRANSACTIONS)-1:0];
                has_error_event = 1'b1;
            end
        end
    end

    // Timeout event detection
    always_comb begin
        timeout_events_detected = '0;
        selected_timeout_idx = '0;
        has_timeout_event = 1'b0;

        // Scan for timeout events
        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (trans_table_local[i].valid && !event_reported[i] &&
                trans_table_local[i].state == TRANS_ERROR && i_cfg_timeout_enable &&
                (trans_table_local[i].error_code == EVT_ADDR_TIMEOUT ||
                 trans_table_local[i].error_code == EVT_DATA_TIMEOUT ||
                 trans_table_local[i].error_code == EVT_RESP_TIMEOUT)) begin
                timeout_events_detected[i] = 1'b1;
            end
        end

        // Priority encoder to select the first detected timeout
        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (timeout_events_detected[i] && !has_timeout_event) begin
                selected_timeout_idx = i[$clog2(MAX_TRANSACTIONS)-1:0];
                has_timeout_event = 1'b1;
            end
        end
    end

    // Completion event detection
    always_comb begin
        completion_events_detected = '0;
        selected_completion_idx = '0;
        has_completion_event = 1'b0;

        // Scan for completion events
        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (trans_table_local[i].valid && !event_reported[i] &&
                trans_table_local[i].state == TRANS_COMPLETE && i_cfg_compl_enable) begin
                completion_events_detected[i] = 1'b1;
            end
        end

        // Priority encoder to select the first detected completion
        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (completion_events_detected[i] && !has_completion_event) begin
                selected_completion_idx = i[$clog2(MAX_TRANSACTIONS)-1:0];
                has_completion_event = 1'b1;
            end
        end
    end

    // FIFO write interface - combines all event detections
    always_comb begin
        fifo_wr_valid = 1'b0;
        fifo_wr_data = '{default: '0};

        // Priority: Error > Timeout > Completion
        if (has_error_event) begin
            fifo_wr_valid = 1'b1;
            fifo_wr_data.packet_type = PktTypeError;
            fifo_wr_data.event_code = trans_table_local[selected_error_idx].error_code;
            fifo_wr_data.channel = trans_table_local[selected_error_idx].channel[5:0];
            fifo_wr_data.data = trans_table_local[selected_error_idx].addr[ADDR_WIDTH-1:0];
        end else if (has_timeout_event) begin
            fifo_wr_valid = 1'b1;
            fifo_wr_data.packet_type = PktTypeTimeout;
            fifo_wr_data.event_code = trans_table_local[selected_timeout_idx].error_code;
            fifo_wr_data.channel = trans_table_local[selected_timeout_idx].channel[5:0];
            fifo_wr_data.data = trans_table_local[selected_timeout_idx].addr[ADDR_WIDTH-1:0];
        end else if (has_completion_event) begin
            fifo_wr_valid = 1'b1;
            fifo_wr_data.packet_type = PktTypeCompletion;
            fifo_wr_data.event_code = EVT_TRANS_COMPLETE;
            fifo_wr_data.channel = trans_table_local[selected_completion_idx].channel[5:0];
            fifo_wr_data.data = trans_table_local[selected_completion_idx].addr[ADDR_WIDTH-1:0];
        end
    end

    // FIFO read interface and event processing
    assign fifo_rd_ready = i_intrbus_ready && o_intrbus_valid;

    // Event marking signals
    logic [MAX_TRANSACTIONS-1:0] events_to_mark;
    logic [MAX_TRANSACTIONS-1:0] error_events;
    logic [MAX_TRANSACTIONS-1:0] completion_events;

    // Active transaction count for threshold detection
    logic [7:0] active_count_current;
    logic active_threshold_detection;

    // Latency threshold detection signals
    logic [MAX_TRANSACTIONS-1:0] latency_threshold_events;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] selected_latency_idx;
    logic has_latency_event;

    // Detect events that need to be marked as reported
    always_comb begin
        events_to_mark = '0;
        error_events = '0;
        completion_events = '0;

        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (trans_table_local[i].valid) begin
                if ((trans_table_local[i].state == TRANS_ERROR ||
                        trans_table_local[i].state == TRANS_COMPLETE) &&
                        !event_reported[i] && fifo_wr_valid && fifo_wr_ready) begin

                    events_to_mark[i] = 1'b1;

                    if (trans_table_local[i].state == TRANS_ERROR) begin
                        error_events[i] = 1'b1;
                    end else if (trans_table_local[i].state == TRANS_COMPLETE) begin
                        completion_events[i] = 1'b1;
                    end
                end
            end
        end
    end

    // Active transaction count calculation
    always_comb begin
        active_count_current = '0;

        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (trans_table_local[i].valid &&
                trans_table_local[i].state != TRANS_COMPLETE &&
                trans_table_local[i].state != TRANS_ERROR) begin
                active_count_current = active_count_current + 1'b1;
            end
        end

        active_threshold_detection = (active_count_current > i_active_trans_threshold) &&
                                        !active_threshold_crossed &&
                                        !o_intrbus_valid &&
                                        (fifo_rd_valid == 0);
    end

    // Latency threshold detection
    always_comb begin
        latency_threshold_events = '0;
        selected_latency_idx = '0;
        has_latency_event = 1'b0;

        if (ENABLE_PERF_PACKETS && i_cfg_perf_enable && i_cfg_threshold_enable) begin
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                if (trans_table_local[i].valid && trans_table_local[i].state == TRANS_COMPLETE) begin
                    logic [31:0] total_latency;
                    if (IS_READ) begin
                        total_latency = trans_table_local[i].data_timestamp - trans_table_local[i].addr_timestamp;
                    end else begin
                        total_latency = trans_table_local[i].resp_timestamp - trans_table_local[i].addr_timestamp;
                    end

                    if (total_latency > i_latency_threshold && !latency_threshold_crossed) begin
                        latency_threshold_events[i] = 1'b1;
                    end
                end
            end

            // Priority encoder to select the first latency threshold event
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                if (latency_threshold_events[i] && !has_latency_event) begin
                    selected_latency_idx = i[$clog2(MAX_TRANSACTIONS)-1:0];
                    has_latency_event = 1'b1;
                end
            end
        end
    end

    // Performance packet state and selection
    logic generate_perf_packet_completed;
    logic generate_perf_packet_errors;
    logic [2:0] next_perf_report_state;

    always_comb begin
        next_perf_report_state = 3'h0;
        generate_perf_packet_completed = 1'b0;
        generate_perf_packet_errors = 1'b0;

        if (ENABLE_PERF_PACKETS && i_cfg_perf_enable && !o_intrbus_valid && fifo_rd_valid == 0) begin
            case (perf_report_state)
                3'h0: begin // ADDR_LATENCY
                    next_perf_report_state = 3'h1;
                end
                3'h1: begin // DATA_LATENCY
                    next_perf_report_state = 3'h2;
                end
                3'h2: begin // TOTAL_LATENCY
                    next_perf_report_state = 3'h3;
                end
                3'h3: begin // COMPLETED_COUNT
                    next_perf_report_state = 3'h4;
                    if (perf_completed_count > 0) begin
                        generate_perf_packet_completed = 1'b1;
                    end
                end
                3'h4: begin // ERROR_COUNT
                    next_perf_report_state = 3'h0;
                    if (perf_error_count > 0) begin
                        generate_perf_packet_errors = 1'b1;
                    end
                end
                default: next_perf_report_state = 3'h0;
            endcase
        end
    end

    // Event reporting logic - sequential logic only
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            // Reset local table and reporting state
            trans_table_local <= '{default: '0};
            o_intrbus_valid <= 1'b0;
            event_count <= '0;
            event_reported <= '0;
            o_intrbus_packet <= '0;

            // Reset performance counters
            perf_completed_count <= '0;
            perf_error_count <= '0;

            // Reset threshold flags
            active_threshold_crossed <= 1'b0;
            latency_threshold_crossed <= 1'b0;

            // Initialize packet construction registers
            packet_type <= PktTypeError;
            event_code <= EVT_NONE;
            event_data <= '0;
            event_channel <= '0;

            // Initialize performance report state
            perf_report_state <= 3'h0;
        end else begin
            // Update local transaction table
            trans_table_local <= i_trans_table;

            // Handle packet output
            if (o_intrbus_valid && i_intrbus_ready) begin
                o_intrbus_valid <= 1'b0;
            end

            // Present next packet from FIFO
            if (!o_intrbus_valid && fifo_rd_valid) begin
                o_intrbus_valid <= 1'b1;
                packet_type <= fifo_rd_data.packet_type;
                event_code <= fifo_rd_data.event_code;
                event_data <= fifo_rd_data.data;
                event_channel <= fifo_rd_data.channel;
            end

            // Mark events as reported and update counters
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                if (events_to_mark[i]) begin
                    event_reported[i] <= 1'b1;
                    event_count <= event_count + 1'b1;
                end

                // Update performance counters
                if (ENABLE_PERF_PACKETS) begin
                    if (error_events[i]) begin
                        perf_error_count <= perf_error_count + 1'b1;
                    end
                    if (completion_events[i]) begin
                        perf_completed_count <= perf_completed_count + 1'b1;
                    end
                end
            end

            // Generate threshold packets if enabled
            if (i_cfg_threshold_enable) begin
                // Active transaction count threshold
                if (active_threshold_detection) begin
                    o_intrbus_valid <= 1'b1;
                    packet_type <= PktTypeThreshold;
                    event_code <= THRESH_ACTIVE_COUNT;
                    event_data <= {24'h0, active_count_current};
                    event_channel <= '0;
                    active_threshold_crossed <= 1'b1;
                    event_count <= event_count + 1'b1;
                end else if (active_count_current <= i_active_trans_threshold) begin
                    active_threshold_crossed <= 1'b0;
                end

                // Latency threshold
                if (has_latency_event && !o_intrbus_valid && fifo_rd_valid == 0) begin
                    o_intrbus_valid <= 1'b1;
                    packet_type <= PktTypeThreshold;
                    event_code <= THRESH_LATENCY;

                    if (IS_READ) begin
                        event_data <= (trans_table_local[selected_latency_idx].data_timestamp -
                                        trans_table_local[selected_latency_idx].addr_timestamp)[ADDR_WIDTH-1:0];
                    end else begin
                        event_data <= (trans_table_local[selected_latency_idx].resp_timestamp -
                                        trans_table_local[selected_latency_idx].addr_timestamp)[ADDR_WIDTH-1:0];
                    end

                    event_channel <= trans_table_local[selected_latency_idx].channel[5:0];
                    latency_threshold_crossed <= 1'b1;
                    event_count <= event_count + 1'b1;
                end
            end

            // Generate performance packets if enabled
            if (generate_perf_packet_completed) begin
                o_intrbus_valid <= 1'b1;
                packet_type <= PktTypePerf;
                event_code <= PERF_COMPLETED_COUNT;
                event_data <= {16'h0, perf_completed_count};
                event_channel <= '0;
            end

            if (generate_perf_packet_errors) begin
                o_intrbus_valid <= 1'b1;
                packet_type <= PktTypePerf;
                event_code <= PERF_ERROR_COUNT;
                event_data <= {16'h0, perf_error_count};
                event_channel <= '0;
            end

            // Update performance report state
            perf_report_state <= next_perf_report_state;
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

        o_intrbus_packet[63:60] = packet_type;
        o_intrbus_packet[59:56] = event_code;
        o_intrbus_packet[55:50] = event_channel;
        o_intrbus_packet[49:46] = UNIT_ID[3:0];  // 4-bit Unit ID
        o_intrbus_packet[45:38] = AGENT_ID[7:0]; // 8-bit Agent ID

        // Address/data field (up to 38 bits)
        if (ADDR_WIDTH <= 38) begin
            o_intrbus_packet[37:(38-ADDR_WIDTH)] = event_data;
        end else begin
            o_intrbus_packet[37:0] = event_data[37:0];
        end
    end

endmodule : axi_errmon_reporter
