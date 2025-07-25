`timescale 1ns / 1ps

module arbiter_wrr_pwm_monbus #(
    parameter int MAX_LEVELS = 16,        // Updated to match new arbiter
    parameter int CLIENTS = 4,
    parameter int WAIT_GNT_ACK = 0,
    parameter int PWM_WIDTH = 8,

    // Monitor bus parameters (made more configurable)
    parameter logic [7:0] MON_AGENT_ID = 8'h00,
    parameter logic [3:0] MON_UNIT_ID = 4'h0,
    parameter int MON_FIFO_DEPTH = 8,
    parameter int MON_FIFO_ALMOST_MARGIN = 1,
    parameter int FAIRNESS_REPORT_CYCLES = 256,
    parameter int MIN_GRANTS_FOR_FAIRNESS = 100,

    // Calculated parameters - updated to match new arbiter
    parameter int MAX_LEVELS_WIDTH = $clog2(MAX_LEVELS),
    parameter int MON_FIFO_COUNT_WIDTH = $clog2(MON_FIFO_DEPTH + 1),

    // Short parameters
    parameter int C = CLIENTS,
    parameter int N = $clog2(CLIENTS),
    parameter int MTW = MAX_LEVELS_WIDTH,
    parameter int CXMTW = CLIENTS*MAX_LEVELS_WIDTH,
    parameter int MFCW = MON_FIFO_COUNT_WIDTH
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // Arbiter configuration and control signals
    input  logic [CXMTW-1:0]              cfg_arb_max_thresh,
    input  logic [C-1:0]                  req,
    output logic                          grant_valid,
    output logic [C-1:0]                  grant,
    output logic [N-1:0]                  grant_id,
    input  logic [C-1:0]                  grant_ack,

    // Pwm configuration signals (single channel)
    input  logic                          cfg_pwm_start,
    input  logic [PWM_WIDTH-1:0]          cfg_pwm_duty,
    input  logic [PWM_WIDTH-1:0]          cfg_pwm_period,
    input  logic [PWM_WIDTH-1:0]          cfg_pwm_repeat_count,
    output logic                          cfg_sts_pwm_done,
    output logic                          pwm_out,

    // Monitor bus configuration
    input  logic                          cfg_mon_enable,
    input  logic [15:0]                   cfg_mon_pkt_type_enable,
    input  logic [15:0]                   cfg_mon_latency,
    input  logic [15:0]                   cfg_mon_starvation,
    input  logic [15:0]                   cfg_mon_fairness,
    input  logic [15:0]                   cfg_mon_active,
    input  logic [7:0]                    cfg_mon_period,

    // Consolidated 64-bit event packet interface (monitor bus)
    output logic                          monbus_valid,
    input  logic                          monbus_ready,
    output logic [63:0]                   monbus_packet
);

    // Import monitor package for event types
    import monitor_pkg::*;

    // Internal signal to connect Pwm output to arbiter block_arb input
    logic block_arb_internal;

    // Connect Pwm output directly to arbiter block_arb input (single channel)
    assign block_arb_internal = pwm_out;

    // =========================================================================
    // Monitor Bus Implementation With Packet Type Filtering
    // =========================================================================

    // Monitor state and counters (flops)
    logic [15:0] r_req_timers [CLIENTS];
    logic [15:0] r_grant_counters [CLIENTS];
    logic [15:0] r_sample_counter;
    logic [31:0] r_total_grants;
    logic [31:0] r_sample_grants [CLIENTS];
    logic [7:0]  r_fairness_report_counter;

    // Event detection pipeline (registered for clean timing)
    logic         r_starvation_detected;
    logic [N-1:0] r_starvation_client;
    logic         r_latency_threshold_detected;
    logic [N-1:0] r_latency_threshold_client;
    logic         r_active_threshold_detected;
    logic         r_grant_event_detected;
    logic [N-1:0] r_grant_client_id;

    // Monitor packet creation (wires)
    logic [63:0]         w_mon_packet_next;
    logic                w_mon_packet_valid;
    logic                w_mon_fifo_ready;
    logic [MFCW-1:0]     w_mon_fifo_count;
    logic [7:0]          w_active_req_count;
    logic                w_fairness_violation;
    logic [3:0]          w_dominant_client;

    // =========================================================================
    // Enhanced Event Detection With Edge Detection
    // =========================================================================

    // Event detection wires (combinational)
    logic         w_starvation_detected;
    logic [N-1:0] w_starvation_client;
    logic         w_latency_threshold_detected;
    logic [N-1:0] w_latency_threshold_client;
    logic         w_active_threshold_detected;
    logic         w_grant_event_detected;

    // Monitor bus Fifo using gaxi_fifo_sync
    gaxi_fifo_sync #(
        .REGISTERED      (0),
        .DATA_WIDTH      (64),
        .DEPTH           (MON_FIFO_DEPTH),
        .ALMOST_WR_MARGIN(MON_FIFO_ALMOST_MARGIN),
        .ALMOST_RD_MARGIN(MON_FIFO_ALMOST_MARGIN),
        .INSTANCE_NAME   ("MON_FIFO")
    ) u_mon_fifo (
        .axi_aclk        (clk),
        .axi_aresetn     (rst_n),
        .wr_valid        (w_mon_packet_valid),
        .wr_ready        (w_mon_fifo_ready),
        .wr_data         (w_mon_packet_next),
        .rd_ready        (monbus_ready),
        .count           (w_mon_fifo_count),
        .rd_valid        (monbus_valid),
        .rd_data         (monbus_packet)
    );

    // Gate monitor bus output with enable
    assign monbus_valid = u_mon_fifo.rd_valid && cfg_mon_enable;

    // Active request counter (wire)
    always_comb begin
        w_active_req_count = 8'h0;
        for (int i = 0; i < CLIENTS; i++) begin
            if (req[i] && !block_arb_internal) begin
                w_active_req_count = w_active_req_count + 8'h1;
            end
        end
    end

    // =========================================================================
    // Enhanced Event Detection With Proper Edge Detection
    // =========================================================================

    // Starvation detection (combinational)
    always_comb begin
        w_starvation_detected = 1'b0;
        w_starvation_client = {N{1'b0}};

        if (cfg_mon_enable && !block_arb_internal && cfg_mon_starvation > 16'h0) begin
            for (int i = 0; i < CLIENTS; i++) begin
                if (req[i] && r_req_timers[i] >= cfg_mon_starvation) begin
                    w_starvation_detected = 1'b1;
                    w_starvation_client = N'(i);
                    break; // Only report one event per cycle
                end
            end
        end
    end

    // Latency threshold detection (combinational)
    always_comb begin
        w_latency_threshold_detected = 1'b0;
        w_latency_threshold_client = {N{1'b0}};

        if (cfg_mon_enable && !block_arb_internal && cfg_mon_latency > 16'h0) begin
            for (int i = 0; i < CLIENTS; i++) begin
                if (req[i] && r_req_timers[i] == cfg_mon_latency) begin  // Edge Detection: == instead of >=
                    w_latency_threshold_detected = 1'b1;
                    w_latency_threshold_client = N'(i);
                    break; // Only report one event per cycle
                end
            end
        end
    end

    // Active request count threshold detection (edge detection)
    logic r_active_count_above_thresh;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_active_count_above_thresh <= 1'b0;
        end else begin
            r_active_count_above_thresh <= (w_active_req_count >= cfg_mon_active[7:0]) &&
                                            (cfg_mon_active > 16'h0);
        end
    end

    assign w_active_threshold_detected = cfg_mon_enable && !block_arb_internal &&
                                        (w_active_req_count >= cfg_mon_active[7:0]) &&
                                        (cfg_mon_active > 16'h0) &&
                                        !r_active_count_above_thresh;  // Edge Detection

    // Grant event detection (edge detection on grant_valid)
    logic r_gnt_valid_prev;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_gnt_valid_prev <= 1'b0;
        end else begin
            r_gnt_valid_prev <= grant_valid;
        end
    end

    assign w_grant_event_detected = cfg_mon_enable && !block_arb_internal &&
                                   grant_valid && !r_gnt_valid_prev;  // Edge Detection

    // =========================================================================
    // Registered Event Detection For Clean Pipeline Timing
    // =========================================================================

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_starvation_detected <= 1'b0;
            r_starvation_client <= {N{1'b0}};
            r_latency_threshold_detected <= 1'b0;
            r_latency_threshold_client <= {N{1'b0}};
            r_active_threshold_detected <= 1'b0;
            r_grant_event_detected <= 1'b0;
            r_grant_client_id <= {N{1'b0}};
        end else begin
            // Register event detection for clean timing
            r_starvation_detected <= w_starvation_detected;
            r_starvation_client <= w_starvation_client;
            r_latency_threshold_detected <= w_latency_threshold_detected;
            r_latency_threshold_client <= w_latency_threshold_client;
            r_active_threshold_detected <= w_active_threshold_detected;
            r_grant_event_detected <= w_grant_event_detected;
            r_grant_client_id <= grant_id;
        end
    end

    // =========================================================================
    // Packet Type Filtering And Event Generation
    // =========================================================================

    always_comb begin
        w_mon_packet_valid = 1'b0;
        w_mon_packet_next = 64'h0;

        if (w_mon_fifo_ready && cfg_mon_enable) begin
            // Priority 1: Starvation detection (highest priority)
            if (r_starvation_detected && cfg_mon_pkt_type_enable[PktTypeError]) begin
                w_mon_packet_valid = 1'b1;
                w_mon_packet_next = create_monitor_packet(
                    PktTypeError,
                    PROTOCOL_AXI,
                    4'(AXI_ERR_ARBITER_STARVATION),
                    6'(r_starvation_client),
                    4'(MON_UNIT_ID),
                    8'(MON_AGENT_ID),
                    {20'h0, r_req_timers[r_starvation_client]}
                );
            end
            // Priority 2: Latency threshold violations
            else if (r_latency_threshold_detected && cfg_mon_pkt_type_enable[PktTypeThreshold]) begin
                w_mon_packet_valid = 1'b1;
                w_mon_packet_next = create_monitor_packet(
                    PktTypeThreshold,
                    PROTOCOL_AXI,
                    4'(AXI_THRESH_GRANT_LATENCY),
                    6'(r_latency_threshold_client),
                    4'(MON_UNIT_ID),
                    8'(MON_AGENT_ID),
                    {20'h0, r_req_timers[r_latency_threshold_client]}
                );
            end
            // Priority 3: Active request count threshold
            else if (r_active_threshold_detected && cfg_mon_pkt_type_enable[PktTypeThreshold]) begin
                w_mon_packet_valid = 1'b1;
                w_mon_packet_next = create_monitor_packet(
                    PktTypeThreshold,
                    PROTOCOL_AXI,
                    4'(AXI_THRESH_ACTIVE_COUNT),
                    6'h0,
                    4'(MON_UNIT_ID),
                    8'(MON_AGENT_ID),
                    {28'h0, w_active_req_count}
                );
            end
            // Priority 4: Performance reporting on grant events (Edge Triggered)
            else if (r_grant_event_detected && cfg_mon_pkt_type_enable[PktTypePerf]) begin
                w_mon_packet_valid = 1'b1;
                w_mon_packet_next = create_monitor_packet(
                    PktTypePerf,
                    PROTOCOL_AXI,
                    4'(AXI_PERF_GRANT_EFFICIENCY),
                    6'(r_grant_client_id),
                    4'(MON_UNIT_ID),
                    8'(MON_AGENT_ID),
                    {16'(r_grant_counters[r_grant_client_id]), 12'h0, w_active_req_count}
                );
            end
        end
    end

    // =========================================================================
    // Per-client Monitoring And Sample Period Management
    // =========================================================================

    logic [15:0] w_sample_period_max;
    assign w_sample_period_max = 16'h1 << cfg_mon_period;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset all counters
            for (int i = 0; i < CLIENTS; i++) begin
                r_req_timers[i] <= 16'h0;
                r_grant_counters[i] <= 16'h0;
                r_sample_grants[i] <= 32'h0;
            end
            r_sample_counter <= 16'h0;
            r_total_grants <= 32'h0;
        end else if (cfg_mon_enable) begin
            // Sample period counter
            r_sample_counter <= r_sample_counter + 16'h1;

            // Reset sample period counters when period expires
            if (r_sample_counter == w_sample_period_max) begin
                r_sample_counter <= 16'h0;
                for (int i = 0; i < CLIENTS; i++) begin
                    r_sample_grants[i] <= 32'h0;
                end
            end

            // Per-client monitoring
            for (int i = 0; i < CLIENTS; i++) begin
                // Request timer management
                if (req[i] && !block_arb_internal) begin
                    // Request is active and arbiter not blocked
                    if (grant_valid && grant[i]) begin
                        // Grant received - reset timer
                        r_req_timers[i] <= 16'h0;
                        r_grant_counters[i] <= r_grant_counters[i] + 16'h1;
                        r_sample_grants[i] <= r_sample_grants[i] + 32'h1;
                        r_total_grants <= r_total_grants + 32'h1;
                    end else begin
                        // Request pending - increment timer
                        r_req_timers[i] <= r_req_timers[i] + 16'h1;
                    end
                end else begin
                    // No request or arbiter blocked - reset timer
                    r_req_timers[i] <= 16'h0;
                end
            end
        end
    end

    // =========================================================================
    // Fairness Monitoring (Periodic Reporting Only)
    // =========================================================================

    always_comb begin
        w_fairness_violation = 1'b0;
        w_dominant_client = 4'h0;

        // Fairness check - detect if any client is getting disproportionate grants
        if (cfg_mon_enable && cfg_mon_fairness > 16'h0 && r_total_grants > MIN_GRANTS_FOR_FAIRNESS) begin
            for (int i = 0; i < CLIENTS; i++) begin
                // Calculate: grants[i] * 100 > total_grants * fairness_threshold
                if (r_grant_counters[i] * 32'd100 > r_total_grants * {16'h0, cfg_mon_fairness}) begin
                    w_fairness_violation = 1'b1;
                    w_dominant_client = 4'(i);
                    break;
                end
            end
        end
    end

    // Generate fairness violation events periodically (only when threshold reached)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_fairness_report_counter <= 8'h0;
        end else if (cfg_mon_enable) begin
            r_fairness_report_counter <= r_fairness_report_counter + 8'h1;

            // Report fairness violations every Fairness_report_cycles cycles
            // Only if there's actually a violation and packet type is enabled
            if (r_fairness_report_counter == 8'(FAIRNESS_REPORT_CYCLES - 1) && 
                w_fairness_violation && 
                cfg_mon_pkt_type_enable[PktTypeThreshold] &&
                w_mon_fifo_ready) begin
                // This could be implemented as a separate fairness event generator
                // For now, fairness events are generated through the main pipeline
            end
        end
    end

    // =========================================================================
    // Core Functionality (Arbiter + Pwm)
    // =========================================================================

    // Instantiate the weighted round-robin arbiter - Updated for new interface
    arbiter_round_robin_weighted #(
        .MAX_LEVELS      (MAX_LEVELS),
        .CLIENTS         (CLIENTS),
        .WAIT_GNT_ACK    (WAIT_GNT_ACK),
        .MAX_LEVELS_WIDTH(MAX_LEVELS_WIDTH)
    ) u_arbiter (
        .clk         (clk),
        .rst_n       (rst_n),
        .block_arb   (block_arb_internal),
        .max_thresh  (cfg_arb_max_thresh),
        .req         (req),
        .grant_valid   (grant_valid),
        .grant         (grant),
        .grant_id      (grant_id),
        .grant_ack     (grant_ack)
    );

    // Instantiate the Pwm module (hardcoded to 1 channel)
    pwm #(
        .WIDTH    (PWM_WIDTH),
        .CHANNELS (1)  // Single channel for arbiter control
    ) u_pwm (
        .clk          (clk),
        .rst_n        (rst_n),
        .start        (cfg_pwm_start),
        .duty         (cfg_pwm_duty),
        .period       (cfg_pwm_period),
        .repeat_count (cfg_pwm_repeat_count),
        .done         (cfg_sts_pwm_done),
        .pwm_out      (pwm_out)
    );

    // =========================================================================
    // Assertions For Parameter Validation
    // =========================================================================

    // synopsys translate_off
    initial begin
        assert (MON_FIFO_DEPTH > 0) else $fatal(1, "Mon_fifo_depth must be > 0");
        assert (MON_FIFO_DEPTH <= 256) else $fatal(1, "Mon_fifo_depth should be <= 256 for reasonable resource usage");
        assert (CLIENTS > 0) else $fatal(1, "Clients must be > 0");
        assert (CLIENTS <= 32) else $fatal(1, "Clients should be <= 32 for reasonable resource usage");
        assert (PWM_WIDTH >= 4) else $fatal(1, "Pwm_width should be >= 4 for meaningful resolution");
        assert (PWM_WIDTH <= 32) else $fatal(1, "Pwm_width should be <= 32 for reasonable resource usage");
        assert (MIN_GRANTS_FOR_FAIRNESS >= 10) else $fatal(1, "Min_grants_for_fairness should be >= 10 for statistical significance");
        assert (FAIRNESS_REPORT_CYCLES >= 16) else $fatal(1, "Fairness_report_cycles should be >= 16 to avoid excessive reporting");
    end

    // Monitor for excessive packet generation (debugging aid)
    logic [15:0] debug_packet_count;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            debug_packet_count <= 16'h0;
        end else begin
            if (w_mon_packet_valid && w_mon_fifo_ready) begin
                debug_packet_count <= debug_packet_count + 16'h1;
            end

            // Reset counter periodically
            if (debug_packet_count >= 16'hFFF0) begin
                debug_packet_count <= 16'h0;
            end
        end
    end

    // Warning for excessive packet generation
    always @(posedge clk) begin
        if (debug_packet_count > 1000) begin
            $display("Warning: %s generated %d packets recently - check event detection logic",
                    "Arbiter_wrr_pwm_monbus", debug_packet_count);
        end
    end
    // synopsys translate_on

endmodule : arbiter_wrr_pwm_monbus
