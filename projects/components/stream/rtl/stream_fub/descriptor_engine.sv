//////////////////////////////////////////////////////////////////////////////////
// Company:  Cornami, Inc.
//           Copyright (c) 2025 by Cornami, Inc. All rights reserved.
//
// Engineer: STREAM RTL v1.0 - Adapted from RAPIDS Descriptor Engine
//
// Module Name   : descriptor_engine
// Project Name  : STREAM - Scatter-gather Transfer Rapid Engine for AXI Memory
// Target Devices: ASIC/FPGA
// Tool versions : Verilator compatible
// Description   : Descriptor Engine for STREAM - Adapted from RAPIDS v3.0
//                 - Fetches descriptors from memory via AXI4
//                 - Simplified for STREAM: no RDA packets (APB-only mode)
//                 - 256-bit descriptor format with length in BEATS
//                 - Channel reset support for clean shutdown
//
//////////////////////////////////////////////////////////////////////////////////

`timescale 1ns / 1ps

// Import common STREAM and monitor packages
`include "stream_imports.svh"

module descriptor_engine #(
    parameter int CHANNEL_ID = 0,
    parameter int NUM_CHANNELS = 32,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int FIFO_DEPTH = 8,
    parameter int TIMEOUT_CYCLES = 1000,
    // Monitor Bus Parameters
    parameter logic [7:0] MON_AGENT_ID = 8'h10,      // Descriptor Engine Agent ID
    parameter logic [3:0] MON_UNIT_ID = 4'h1,        // Unit identifier
    parameter logic [5:0] MON_CHANNEL_ID = 6'h0      // Base channel ID
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // APB Programming Interface (for descriptor fetch)
    input  logic                        apb_valid,
    output logic                        apb_ready,
    input  logic [ADDR_WIDTH-1:0]       apb_addr,

    // RDA Packet Interface (from Network Slave)
    input  logic                        rda_valid,
    output logic                        rda_ready,
    input  logic [DATA_WIDTH-1:0]       rda_packet,
    input  logic [CHAN_WIDTH-1:0]       rda_channel,

    // Enhanced Scheduler Interface (with EOS/EOL/EOD support)
    output logic                        descriptor_valid,
    input  logic                        descriptor_ready,
    output logic [DATA_WIDTH-1:0]       descriptor_packet,
    output logic                        descriptor_same,
    output logic                        descriptor_error,
    output logic                        descriptor_is_rda,
    output logic [CHAN_WIDTH-1:0]       descriptor_rda_channel,

    // NEW: Enhanced control signal outputs
    output logic                        descriptor_eos,        // End of Stream
    output logic                        descriptor_eol,        // End of Line
    output logic                        descriptor_eod,        // End of Data
    output logic [1:0]                  descriptor_type,       // Packet type

    // Shared AXI4 Master Read Interface
    output logic                        ar_valid,
    input  logic                        ar_ready,
    output logic [ADDR_WIDTH-1:0]       ar_addr,
    output logic [7:0]                  ar_len,
    output logic [2:0]                  ar_size,
    output logic [1:0]                  ar_burst,
    output logic [AXI_ID_WIDTH-1:0]     ar_id,
    output logic                        ar_lock,
    output logic [3:0]                  ar_cache,
    output logic [2:0]                  ar_prot,
    output logic [3:0]                  ar_qos,
    output logic [3:0]                  ar_region,

    // AXI Read Data Channel (Shared - monitor for our ID)
    input  logic                        r_valid,
    output logic                        r_ready,
    input  logic [DATA_WIDTH-1:0]       r_data,
    input  logic [1:0]                  r_resp,
    input  logic                        r_last,
    input  logic [AXI_ID_WIDTH-1:0]     r_id,

    // Configuration Interface
    input  logic                        cfg_prefetch_enable,
    input  logic [3:0]                  cfg_fifo_threshold,
    input  logic [ADDR_WIDTH-1:0]       cfg_addr0_base,
    input  logic [ADDR_WIDTH-1:0]       cfg_addr0_limit,
    input  logic [ADDR_WIDTH-1:0]       cfg_addr1_base,
    input  logic [ADDR_WIDTH-1:0]       cfg_addr1_limit,

    // FIXED: Channel reset interface
    input  logic                        cfg_channel_reset,

    // Status Interface
    output logic                        descriptor_engine_idle,

    // Monitor Bus Interface
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [63:0]                 mon_packet
);

    //=========================================================================
    // Parameter Validation
    //=========================================================================

    initial begin
        if (AXI_ID_WIDTH < CHAN_WIDTH) begin
            $fatal(1, "AXI_ID_WIDTH (%0d) must be >= CHAN_WIDTH (%0d)", AXI_ID_WIDTH, CHAN_WIDTH);
        end
    end

    //=========================================================================
    // Enhanced Descriptor Structure with EOS/EOL/EOD
    //=========================================================================

    typedef struct packed {
        logic [DATA_WIDTH-1:0]     data;        // Descriptor data
        logic                      same_flag;   // Same descriptor flag
        logic                      is_rda;      // RDA packet indicator
        logic [CHAN_WIDTH-1:0]     rda_channel; // RDA channel ID
        logic                      eos;         // NEW: End of Stream
        logic                      eol;         // NEW: End of Line
        logic                      eod;         // NEW: End of Data
        logic [1:0]                pkt_type;    // NEW: Packet type
    } enhanced_descriptor_t;

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // State machine registers (UPDATED: Use RAPIDS package type instead of local typedef)
    read_engine_state_t r_current_state;
    read_engine_state_t w_next_state;

    // FIXED: Channel reset management
    logic r_channel_reset_active;
    logic w_safe_to_reset;
    logic w_fifos_empty;
    logic w_no_active_operations;

    // APB skid buffer signals
    logic w_apb_skid_valid_in, w_apb_skid_ready_in;
    logic w_apb_skid_valid_out, w_apb_skid_ready_out;
    logic [ADDR_WIDTH-1:0] w_apb_skid_dout;

    // RDA skid buffer signals
    logic w_rda_skid_valid_in, w_rda_skid_ready_in;
    logic w_rda_skid_valid_out, w_rda_skid_ready_out;
    logic [DATA_WIDTH + CHAN_WIDTH - 1:0] w_rda_skid_din, w_rda_skid_dout;

    // Descriptor FIFO signals
    logic w_desc_fifo_wr_valid, w_desc_fifo_wr_ready;
    logic w_desc_fifo_rd_valid, w_desc_fifo_rd_ready;
    enhanced_descriptor_t w_desc_fifo_wr_data, w_desc_fifo_rd_data;

    // Operation tracking
    logic r_apb_operation_active;
    logic r_rda_operation_active;

    // AXI transaction tracking
    logic r_axi_read_active;
    logic [ADDR_WIDTH-1:0] r_axi_read_addr;
    logic [1:0] r_axi_read_resp;

    // Descriptor processing
    logic [DATA_WIDTH-1:0] r_descriptor_data;
    logic [ADDR_WIDTH-1:0] r_saved_next_addr;

    // Enhanced field extraction
    logic w_desc_eos, w_desc_eol, w_desc_eod;
    logic [1:0] w_desc_type;
    logic [ADDR_WIDTH-1:0] w_next_addr;

    // Validation signals
    logic w_validation_passed;
    logic w_addr_range_valid;
    logic w_our_axi_response;
    logic w_axi_response_ok;

    // Error tracking
    logic r_descriptor_error;

    // Monitor packet generation
    logic r_mon_valid;
    logic [63:0] r_mon_packet;

    //=========================================================================
    // FIXED: Channel Reset Management
    //=========================================================================

    // Channel reset active tracking
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_channel_reset_active <= 1'b0;
        end else begin
            r_channel_reset_active <= cfg_channel_reset;
        end
    end

    // Safe to reset conditions
    assign w_fifos_empty = !w_apb_skid_valid_out && !w_rda_skid_valid_out && !w_desc_fifo_rd_valid;
    assign w_no_active_operations = !r_apb_operation_active && !r_rda_operation_active && !r_axi_read_active;
    assign w_safe_to_reset = w_fifos_empty && w_no_active_operations && (r_current_state == read_IDLE);

    // Engine idle signal
    assign descriptor_engine_idle = (r_current_state == read_IDLE) && !r_channel_reset_active && w_fifos_empty;

    //=========================================================================
    // APB Skid Buffer
    //=========================================================================

    // Input side: Accept APB when not in reset
    assign w_apb_skid_valid_in = apb_valid && !r_channel_reset_active;
    assign apb_ready = w_apb_skid_ready_in && !r_channel_reset_active;

    gaxi_skid_buffer #(
        .DATA_WIDTH(ADDR_WIDTH),
        .DEPTH(2),
        .INSTANCE_NAME("APB_ADDR_SKID")
    ) i_apb_skid_buffer (
        .axi_aclk(clk),
        .axi_aresetn(rst_n),
        .wr_valid(w_apb_skid_valid_in),
        .wr_ready(w_apb_skid_ready_in),
        .wr_data(apb_addr),
        .rd_valid(w_apb_skid_valid_out),
        .rd_ready(w_apb_skid_ready_out),
        .rd_data(w_apb_skid_dout),
        .count(),
        .rd_count()
    );

    assign w_apb_skid_ready_out = (r_current_state == read_IDLE) && !r_rda_operation_active && !r_channel_reset_active;

    //=========================================================================
    // RDA Skid Buffer
    //=========================================================================

    // Input side: Accept RDA when not in reset
    assign w_rda_skid_valid_in = rda_valid && !r_channel_reset_active;
    assign rda_ready = w_rda_skid_ready_in && !r_channel_reset_active;
    assign w_rda_skid_din = {rda_packet, rda_channel};

    gaxi_skid_buffer #(
        .DATA_WIDTH(DATA_WIDTH + CHAN_WIDTH),
        .DEPTH(2),
        .INSTANCE_NAME("RDA_PKT_SKID")
    ) i_rda_skid_buffer (
        .axi_aclk(clk),
        .axi_aresetn(rst_n),
        .wr_valid(w_rda_skid_valid_in),
        .wr_ready(w_rda_skid_ready_in),
        .wr_data(w_rda_skid_din),
        .rd_valid(w_rda_skid_valid_out),
        .rd_ready(w_rda_skid_ready_out),
        .rd_data(w_rda_skid_dout),
        .count(),
        .rd_count()
    );

    assign w_rda_skid_ready_out = (r_current_state == read_IDLE) && !r_apb_operation_active && !r_channel_reset_active;

    //=========================================================================
    // Enhanced Descriptor FIFO with EOS/EOL/EOD Support
    //=========================================================================

    // FIFO ready for writes when not in reset
    assign w_desc_fifo_wr_valid = ((r_current_state == read_COMPLETE) || 
                                   (w_rda_skid_valid_out && w_rda_skid_ready_out)) && 
                                   !r_channel_reset_active;

    assign w_desc_fifo_rd_ready = descriptor_ready && !r_channel_reset_active;

    gaxi_fifo_sync #(
        .DATA_WIDTH($bits(enhanced_descriptor_t)),
        .DEPTH(FIFO_DEPTH),
        .INSTANCE_NAME("DESC_FIFO")
    ) i_descriptor_fifo (
        .axi_aclk(clk),
        .axi_aresetn(rst_n),
        .wr_valid(w_desc_fifo_wr_valid),
        .wr_ready(w_desc_fifo_wr_ready),
        .wr_data(w_desc_fifo_wr_data),
        .rd_valid(w_desc_fifo_rd_valid),
        .rd_ready(w_desc_fifo_rd_ready),
        .rd_data(w_desc_fifo_rd_data),
        .count()
    );

    //=========================================================================
    // Enhanced Field Extraction with EOS/EOL/EOD
    //=========================================================================

    // Extract enhanced control fields from descriptor data
    always_comb begin
        // Default values
        w_desc_eos = 1'b0;
        w_desc_eol = 1'b0;
        w_desc_eod = 1'b0;
        w_desc_type = 2'b00;
        w_next_addr = 64'h0;

        // Extract fields based on descriptor format
        // Assuming descriptor has control fields in upper bits
        w_desc_eos = r_descriptor_data[511];        // Bit 511: EOS
        w_desc_eol = r_descriptor_data[510];        // Bit 510: EOL
        w_desc_eod = r_descriptor_data[509];        // Bit 509: EOD
        w_desc_type = r_descriptor_data[508:507];   // Bits 508:507: Type
        w_next_addr = r_descriptor_data[ADDR_WIDTH-1:0]; // Next descriptor address
    end

    //=========================================================================
    // Descriptor Validation
    //=========================================================================

    // Address range validation
    assign w_addr_range_valid = ((r_axi_read_addr >= cfg_addr0_base && r_axi_read_addr <= cfg_addr0_limit) ||
                                 (r_axi_read_addr >= cfg_addr1_base && r_axi_read_addr <= cfg_addr1_limit));

    // Overall validation
    assign w_validation_passed = w_addr_range_valid && w_axi_response_ok;

    //=========================================================================
    // AXI Response Monitoring
    //=========================================================================

    // Check if AXI response is for our channel
    assign w_our_axi_response = r_valid && (r_id[CHAN_WIDTH-1:0] == CHANNEL_ID[CHAN_WIDTH-1:0]);

    // AXI response validation
    assign w_axi_response_ok = (r_resp == 2'b00); // OKAY response

    // We're ready when waiting for our response
    assign r_ready = (r_current_state == read_WAIT_DATA) && w_our_axi_response;

    //=========================================================================
    // FIXED: FSM State Machine with Channel Reset (UPDATED: Use RAPIDS package states)
    //=========================================================================

    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_current_state <= read_IDLE;
        end else begin
            r_current_state <= w_next_state;
        end
    end

    // Next state logic with channel reset support
    always_comb begin
        w_next_state = r_current_state;

        case (r_current_state)
            read_IDLE: begin
                if (r_channel_reset_active) begin
                    w_next_state = read_IDLE; // Stay in idle during reset
                end else if (w_apb_skid_valid_out && w_apb_skid_ready_out) begin
                    w_next_state = read_ISSUE_ADDR;
                end else if (w_rda_skid_valid_out && w_rda_skid_ready_out && w_desc_fifo_wr_ready) begin
                    w_next_state = read_IDLE; // RDA packets processed immediately
                end
            end

            read_ISSUE_ADDR: begin
                if (r_channel_reset_active) begin
                    w_next_state = read_IDLE; // Reset forces return to idle
                end else if (ar_ready) begin
                    w_next_state = read_WAIT_DATA;
                end
            end

            read_WAIT_DATA: begin
                if (r_channel_reset_active) begin
                    w_next_state = read_IDLE; // Reset forces return to idle
                end else if (w_our_axi_response && r_valid) begin
                    if (w_axi_response_ok) begin
                        w_next_state = read_COMPLETE;
                    end else begin
                        w_next_state = read_ERROR;
                    end
                end
            end

            read_COMPLETE: begin
                if (w_desc_fifo_wr_ready) begin
                    w_next_state = read_IDLE;
                end
            end

            read_ERROR: begin
                w_next_state = read_IDLE;
            end

            default: begin
                w_next_state = read_IDLE;
            end
        endcase
    end

    //=========================================================================
    // State Machine Registers and Control
    //=========================================================================

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_apb_operation_active <= 1'b0;
            r_rda_operation_active <= 1'b0;
            r_axi_read_active <= 1'b0;
            r_axi_read_addr <= 64'h0;
            r_axi_read_resp <= 2'b00;
            r_descriptor_data <= '0;
            r_saved_next_addr <= 64'h0;
            r_descriptor_error <= 1'b0;
        end else begin
            case (r_current_state)
                read_IDLE: begin
                    if (w_apb_skid_valid_out && w_apb_skid_ready_out) begin
                        // Start APB operation
                        r_apb_operation_active <= 1'b1;
                        r_axi_read_addr <= w_apb_skid_dout;
                    end else if (w_rda_skid_valid_out && w_rda_skid_ready_out) begin
                        // Process RDA packet immediately
                        r_rda_operation_active <= 1'b1;
                    end
                    r_descriptor_error <= 1'b0;
                end

                read_ISSUE_ADDR: begin
                    if (ar_ready) begin
                        r_axi_read_active <= 1'b1;
                    end
                end

                read_WAIT_DATA: begin
                    if (w_our_axi_response && r_valid) begin
                        r_descriptor_data <= r_data;
                        r_axi_read_resp <= r_resp;
                        r_saved_next_addr <= w_next_addr;
                    end
                end

                read_COMPLETE: begin
                    if (w_desc_fifo_wr_ready) begin
                        r_apb_operation_active <= 1'b0;
                        r_axi_read_active <= 1'b0;
                    end
                end

                read_ERROR: begin
                    r_descriptor_error <= 1'b1;
                    r_apb_operation_active <= 1'b0;
                    r_rda_operation_active <= 1'b0;
                    r_axi_read_active <= 1'b0;
                end

                default: begin
                    // Maintain state
                end
            endcase

            // Handle RDA packet completion
            if (r_rda_operation_active && w_desc_fifo_wr_ready && (r_current_state == read_IDLE)) begin
                r_rda_operation_active <= 1'b0;
            end

            // FIXED: Reset all operations during channel reset
            if (r_channel_reset_active) begin
                r_apb_operation_active <= 1'b0;
                r_rda_operation_active <= 1'b0;
                r_axi_read_active <= 1'b0;
                r_descriptor_error <= 1'b0;
            end
        end
    end

    //=========================================================================
    // Enhanced Descriptor FIFO Write Data Generation
    //=========================================================================

    always_comb begin
        w_desc_fifo_wr_data = '0;

        if (r_current_state == read_COMPLETE) begin
            // APB-fetched descriptor
            w_desc_fifo_wr_data.data = r_descriptor_data;
            w_desc_fifo_wr_data.same_flag = 1'b0; // APB descriptors are never "same"
            w_desc_fifo_wr_data.is_rda = 1'b0;
            w_desc_fifo_wr_data.rda_channel = '0;
            w_desc_fifo_wr_data.eos = w_desc_eos;
            w_desc_fifo_wr_data.eol = w_desc_eol;
            w_desc_fifo_wr_data.eod = w_desc_eod;
            w_desc_fifo_wr_data.pkt_type = w_desc_type;
        end else if (w_rda_skid_valid_out && w_rda_skid_ready_out) begin
            // RDA packet (direct pass-through)
            w_desc_fifo_wr_data.data = w_rda_skid_dout[DATA_WIDTH + CHAN_WIDTH - 1:CHAN_WIDTH];
            w_desc_fifo_wr_data.same_flag = 1'b1; // RDA packets marked as "same"
            w_desc_fifo_wr_data.is_rda = 1'b1;
            w_desc_fifo_wr_data.rda_channel = w_rda_skid_dout[CHAN_WIDTH-1:0];
            // Extract EOS/EOL/EOD from RDA packet
            w_desc_fifo_wr_data.eos = w_rda_skid_dout[DATA_WIDTH + CHAN_WIDTH - 1]; // MSB
            w_desc_fifo_wr_data.eol = w_rda_skid_dout[DATA_WIDTH + CHAN_WIDTH - 2];
            w_desc_fifo_wr_data.eod = w_rda_skid_dout[DATA_WIDTH + CHAN_WIDTH - 3];
            w_desc_fifo_wr_data.pkt_type = w_rda_skid_dout[DATA_WIDTH + CHAN_WIDTH - 4:DATA_WIDTH + CHAN_WIDTH - 5];
        end
    end

    //=========================================================================
    // AXI Read Address Channel Output
    //=========================================================================

    assign ar_valid = (r_current_state == read_ISSUE_ADDR) && !r_axi_read_active;
    assign ar_addr = r_axi_read_addr;
    assign ar_len = 8'h00;           // Single beat transfer
    assign ar_size = 3'b110;         // 64 bytes (512-bit)
    assign ar_burst = 2'b01;         // INCR burst type
    assign ar_id = {{(AXI_ID_WIDTH-CHAN_WIDTH){1'b0}}, CHANNEL_ID[CHAN_WIDTH-1:0]};
    assign ar_lock = 1'b0;           // Normal access
    assign ar_cache = 4'b0010;       // Normal non-cacheable bufferable
    assign ar_prot = 3'b000;         // Data, secure, unprivileged
    assign ar_qos = 4'h0;            // No QoS
    assign ar_region = 4'h0;         // No region

    //=========================================================================
    // Monitor Packet Generation
    //=========================================================================

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_mon_valid <= 1'b0;
            r_mon_packet <= 64'h0;
        end else begin
            // Default: clear monitor packet
            r_mon_valid <= 1'b0;
            r_mon_packet <= 64'h0;

            case (r_current_state)
                read_COMPLETE: begin
                    // Log successful descriptor fetch
                    r_mon_valid <= 1'b1;
                    r_mon_packet <= create_monitor_packet(
                        PktTypeCompletion,
                        PROTOCOL_CORE,
                        CORE_COMPL_DESCRIPTOR_LOADED,
                        MON_CHANNEL_ID,
                        MON_UNIT_ID,
                        MON_AGENT_ID,
                        r_axi_read_addr[34:0]
                    );
                end

                read_ERROR: begin
                    // Log descriptor fetch error
                    r_mon_valid <= 1'b1;
                    r_mon_packet <= create_monitor_packet(
                        PktTypeError,
                        PROTOCOL_CORE,
                        CORE_ERR_DESCRIPTOR_ENGINE,
                        MON_CHANNEL_ID,
                        MON_UNIT_ID,
                        MON_AGENT_ID,
                        {16'h0, r_axi_read_resp, 17'h0}
                    );
                end

                default: begin
                    // No monitor packet
                end
            endcase
        end
    end

    //=========================================================================
    // Output Assignments
    //=========================================================================

    // Enhanced scheduler interface with EOS/EOL/EOD support
    assign descriptor_valid = w_desc_fifo_rd_valid;
    assign descriptor_packet = w_desc_fifo_rd_data.data;
    assign descriptor_same = w_desc_fifo_rd_data.same_flag;
    assign descriptor_is_rda = w_desc_fifo_rd_data.is_rda;
    assign descriptor_rda_channel = w_desc_fifo_rd_data.rda_channel;
    assign descriptor_error = r_descriptor_error;

    // NEW: Enhanced control signal outputs
    assign descriptor_eos = w_desc_fifo_rd_data.eos;
    assign descriptor_eol = w_desc_fifo_rd_data.eol;
    assign descriptor_eod = w_desc_fifo_rd_data.eod;
    assign descriptor_type = w_desc_fifo_rd_data.pkt_type;

    // Monitor bus output
    assign mon_valid = r_mon_valid;
    assign mon_packet = r_mon_packet;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // Operation exclusivity
    property operation_exclusive;
        @(posedge clk) disable iff (!rst_n)
        !(r_apb_operation_active && r_rda_operation_active);
    endproperty
    assert property (operation_exclusive);

    // State machine coverage
    property state_one_hot;
        @(posedge clk) disable iff (!rst_n)
        $onehot(r_current_state);
    endproperty
    assert property (state_one_hot);

    // AXI ID consistency
    property axi_id_matches_channel;
        @(posedge clk) disable iff (!rst_n)
        ar_valid |-> (ar_id[CHAN_WIDTH-1:0] == CHANNEL_ID[CHAN_WIDTH-1:0]);
    endproperty
    assert property (axi_id_matches_channel);

    // Stream control exclusivity (at most one boundary type)
    property stream_boundary_exclusive;
        @(posedge clk) disable iff (!rst_n)
        $countones({w_desc_eos, w_desc_eol, w_desc_eod}) <= 1;
    endproperty
    assert property (stream_boundary_exclusive);

    // FIXED: Channel reset properties
    property channel_reset_blocks_inputs;
        @(posedge clk) disable iff (!rst_n)
        r_channel_reset_active |-> (!w_apb_skid_ready_out && !w_rda_skid_ready_out);
    endproperty
    assert property (channel_reset_blocks_inputs);

    property channel_reset_clears_operations;
        @(posedge clk) disable iff (!rst_n)
        r_channel_reset_active |-> ##[1:10] (!r_apb_operation_active && !r_rda_operation_active);
    endproperty
    assert property (channel_reset_clears_operations);

    property channel_reset_idle_signal;
        @(posedge clk) disable iff (!rst_n)
        descriptor_engine_idle |-> (r_current_state == read_IDLE && !r_channel_reset_active);
    endproperty
    assert property (channel_reset_idle_signal);
    `endif

endmodule : descriptor_engine
