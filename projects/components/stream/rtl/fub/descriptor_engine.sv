// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: descriptor_engine
// Purpose: Autonomous Descriptor Fetch Engine with Chaining Support
//
// Description:
//   Fetches 256-bit STREAM descriptors from memory via AXI4 master interface.
//   Provides two operating modes:
//   1. APB-initiated: Software writes descriptor address → engine fetches
//   2. Autonomous chaining: Engine automatically fetches next_descriptor_ptr
//
// Key Features:
//   - Two-FIFO architecture for decoupling fetch addresses from descriptors
//   - Descriptor address FIFO: Holds addresses to fetch (APB + chaining)
//   - Descriptor data FIFO: Buffers fetched descriptors for scheduler
//   - Address range validation (two configurable ranges)
//   - Autonomous chaining (fetches next_descriptor_ptr without APB)
//   - MonBus event reporting (fetch complete, errors)
//
// Operating Flow:
//   APB Mode:
//     APB write → skid buffer → desc addr FIFO → AXI fetch → desc data FIFO → scheduler
//
//   Chaining Mode:
//     Descriptor complete → extract next_ptr → validate → desc addr FIFO →
//     AXI fetch → desc data FIFO → scheduler (repeat until last=1 or next_ptr=0)
//
// Interface Dependencies:
//   - Requires channel_idle=1 before accepting APB writes (scheduler completed previous)
//   - Shares AXI4 master with other engines (uses CHANNEL_ID in AXI ID field)
//   - Provides enhanced_descriptor_t with EOS/EOL/EOD flags (future use)
//
// Documentation: projects/components/stream_fub/PRD.md
// Subsystem: stream_fub
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Import common STREAM and monitor packages
`include "stream_imports.svh"
`include "reset_defs.svh"

// Import monitor arbiter package for CORE_COMPL_* and CORE_ERR_* constants
import monitor_arbiter_pkg::*;

module descriptor_engine #(
    parameter int CHANNEL_ID = 0,
    parameter int NUM_CHANNELS = 32,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    // DESCRIPTOR_WIDTH is FIXED at 256 bits (removed DATA_WIDTH parameter)
    parameter int AXI_ID_WIDTH = 8,
    parameter int FIFO_DEPTH = 8,
    parameter int DESC_ADDR_FIFO_DEPTH = 2,          // NEW: Descriptor read address FIFO depth
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

    // Scheduler Interface
    input  logic                        channel_idle,          // Scheduler idle (enables APB)
    output logic                        descriptor_valid,
    input  logic                        descriptor_ready,
    output logic [255:0]                descriptor_packet,     // FIXED 256-bit descriptor
    output logic                        descriptor_error,

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

    // AXI Read Data Channel (Shared - monitor for our ID, FIXED 256-bit)
    input  logic                        r_valid,
    output logic                        r_ready,
    input  logic [255:0]                r_data,                // FIXED 256-bit descriptor
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

    // Channel reset interface
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
    // Descriptor Structure with EOS/EOL/EOD
    //=========================================================================

    typedef struct packed {
        logic [255:0]              data;        // Descriptor data (256-bit)
        logic                      eos;         // End of Stream
        logic                      eol;         // End of Line
        logic                      eod;         // End of Data
        logic [1:0]                pkt_type;    // Packet type
    } enhanced_descriptor_t;

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // State machine (reusing RAPIDS read_engine_state_t)
    // States: RD_IDLE → RD_ISSUE_ADDR → RD_WAIT_DATA → RD_COMPLETE → back to RD_IDLE
    // Error path: RD_ERROR → RD_IDLE
    read_engine_state_t r_current_state;
    read_engine_state_t w_next_state;

    // Channel reset management
    // Tracks channel reset state and ensures safe transition to idle
    logic r_channel_reset_active;         // Registered cfg_channel_reset
    logic w_safe_to_reset;                // All operations complete, safe to reset
    logic w_fifos_empty;                  // All FIFOs drained
    logic w_no_active_operations;         // No pending APB or AXI transactions

    // APB skid buffer signals
    // Decouples APB interface from internal processing
    // Input side: APB → skid buffer
    // Output side: skid buffer → descriptor address FIFO
    logic w_apb_skid_valid_in, w_apb_skid_ready_in;
    logic w_apb_skid_valid_out, w_apb_skid_ready_out;
    logic [ADDR_WIDTH-1:0] w_apb_skid_dout;

    // Descriptor Read Address FIFO (autonomous chaining support)
    // Purpose: Queue of descriptor addresses to fetch via AXI
    // Write sources: 1) APB skid buffer (initial kick-off)
    //                2) Autonomous chaining (next_descriptor_ptr)
    // Read sink: FSM in RD_IDLE state pops address for AXI fetch
    logic w_desc_addr_fifo_wr_valid, w_desc_addr_fifo_wr_ready;
    logic w_desc_addr_fifo_rd_valid, w_desc_addr_fifo_rd_ready;
    logic [ADDR_WIDTH-1:0] w_desc_addr_fifo_wr_data, w_desc_addr_fifo_rd_data;
    logic w_desc_addr_fifo_empty;

    // Descriptor Data FIFO
    // Purpose: Buffer fetched descriptors for scheduler
    // Write side: FSM in RD_COMPLETE state pushes fetched descriptor
    // Read side: Scheduler pops when descriptor_ready=1
    logic w_desc_fifo_wr_valid, w_desc_fifo_wr_ready;
    logic w_desc_fifo_rd_valid, w_desc_fifo_rd_ready;
    enhanced_descriptor_t w_desc_fifo_wr_data, w_desc_fifo_rd_data;

    // Operation tracking
    // Flags to track active operations (needed for channel reset)
    logic r_apb_operation_active;         // APB operation in progress

    // AXI transaction tracking
    // State for managing AXI read transaction
    logic r_axi_read_active;              // AXI read request issued
    logic [ADDR_WIDTH-1:0] r_axi_read_addr;    // Address being fetched
    logic [1:0] r_axi_read_resp;          // AXI response (OKAY/ERROR)

    // Descriptor processing
    // Storage for fetched descriptor data
    logic [255:0] r_descriptor_data;           // FIXED 256-bit STREAM descriptor
    logic [ADDR_WIDTH-1:0] r_saved_next_addr;  // next_descriptor_ptr (for logging)

    // Autonomous chaining logic
    // Decision tree for whether to automatically fetch next descriptor
    logic w_chain_condition;              // Basic chaining criteria (next_addr != 0 && !last)
    logic w_next_addr_valid;              // next_addr passes range validation
    logic w_should_chain;                 // Final decision: chain if all conditions met

    // Enhanced field extraction
    // Fields extracted from fetched descriptor (STREAM descriptor format)
    logic w_desc_eos, w_desc_eol, w_desc_eod;  // Stream boundary flags (future use)
    logic w_desc_last;                    // Last descriptor in chain
    logic w_desc_valid;                   // Valid descriptor flag
    logic [1:0] w_desc_type;              // Descriptor type (future use)
    logic [31:0] w_next_addr;             // Next descriptor address (32-bit pointer)

    // Validation signals
    // Combinational checks for descriptor validity
    // logic w_validation_passed;            // Overall validation (address + AXI response) - UNUSED, commented out
    logic w_addr_range_valid;             // Address within configured ranges
    logic w_our_axi_response;             // AXI R channel response matches our ID
    logic w_axi_response_ok;              // AXI R channel response = OKAY

    // Error tracking
    // Sticky error flag for FSM error state
    logic r_descriptor_error;             // Set on validation failure or AXI error

    // APB in-progress flag
    // Set when APB transaction accepted, cleared when channel goes idle
    logic r_apb_ip;                       // APB transaction in progress (prevents duplicate accepts)
    logic r_channel_idle_prev;            // Previous cycle channel_idle for edge detection

    // Monitor packet generation
    // Registered MonBus outputs
    logic r_mon_valid;
    logic [63:0] r_mon_packet;

    //=========================================================================
    // FIXED: Channel Reset Management
    //=========================================================================

    // Channel reset active tracking
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_channel_reset_active <= 1'b0;
        end else begin
            r_channel_reset_active <= cfg_channel_reset;
        end
    )


    // Safe to reset conditions
    assign w_fifos_empty = !w_apb_skid_valid_out && !w_desc_addr_fifo_rd_valid && !w_desc_fifo_rd_valid;
    assign w_no_active_operations = !r_apb_operation_active && !r_axi_read_active;
    assign w_safe_to_reset = w_fifos_empty && w_no_active_operations && (r_current_state == RD_IDLE);

    // Engine idle signal
    assign descriptor_engine_idle = (r_current_state == RD_IDLE) && !r_channel_reset_active && w_fifos_empty;

    //=========================================================================
    // APB Skid Buffer
    //=========================================================================
    // Decouples APB interface from descriptor fetch pipeline
    //
    // APB Acceptance Policy:
    //   Accept new APB write ONLY when ALL of:
    //   1. !r_channel_reset_active - Not in channel reset
    //   2. w_desc_addr_fifo_empty   - No pending descriptor fetches
    //   3. channel_idle             - Scheduler completed all prior descriptors
    //
    // Rationale:
    //   - Policy #2 prevents APB from overwriting autonomous chaining addresses
    //   - Policy #3 ensures scheduler finished processing before new kick-off
    //   - Combined: Ensures clean handoff between APB-initiated and chained descriptors

    // Input side gating: APB → skid buffer
    // Gate APB acceptance with all conditions including apb_ip flag
    // NOTE: Address 0 is INVALID - reject APB requests with addr=0
    logic w_apb_addr_valid;
    assign w_apb_addr_valid = (apb_addr != '0);  // Address 0 is reserved/invalid

    // APB can only be accepted when:
    // 1. Address is valid (non-zero)
    // 2. No channel reset active
    // 3. Descriptor address FIFO is empty
    // 4. Channel is idle (scheduler finished previous work)
    // 5. No APB transaction currently in progress (!r_apb_ip)
    assign w_apb_skid_valid_in = apb_valid && !r_channel_reset_active &&
                                w_desc_addr_fifo_empty && channel_idle && !r_apb_ip;
    assign apb_ready = w_apb_skid_ready_in && !r_channel_reset_active &&
                        w_desc_addr_fifo_empty && channel_idle && !r_apb_ip;

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

    // APB skid output consumed when:
    // - FSM in idle
    // - Descriptor address FIFO has space
    // - Not in channel reset
    assign w_apb_skid_ready_out = (r_current_state == RD_IDLE) &&
                                    w_desc_addr_fifo_wr_ready &&
                                    !r_channel_reset_active;

    //=========================================================================
    // Descriptor Read Address FIFO (Autonomous Chaining)
    //=========================================================================

    // Write side: APB skid OR autonomous chaining logic
    // Read side: FSM pops address to fetch via AXI

    gaxi_fifo_sync #(
        .DATA_WIDTH(ADDR_WIDTH),
        .DEPTH(DESC_ADDR_FIFO_DEPTH),
        .INSTANCE_NAME("DESC_ADDR_FIFO")
    ) i_desc_addr_fifo (
        .axi_aclk(clk),
        .axi_aresetn(rst_n),
        .wr_valid(w_desc_addr_fifo_wr_valid),
        .wr_ready(w_desc_addr_fifo_wr_ready),
        .wr_data(w_desc_addr_fifo_wr_data),
        .rd_valid(w_desc_addr_fifo_rd_valid),
        .rd_ready(w_desc_addr_fifo_rd_ready),
        .rd_data(w_desc_addr_fifo_rd_data),
        .count()
    );

    // FIFO empty when no valid data available (rd_valid = 0)
    assign w_desc_addr_fifo_empty = !w_desc_addr_fifo_rd_valid;

    // Read side: FSM consumes address when in RD_IDLE
    assign w_desc_addr_fifo_rd_ready = (r_current_state == RD_IDLE) && !r_channel_reset_active;

    // Write side: Two sources for descriptor addresses
    // 1. APB skid (initial kick-off)
    // 2. Autonomous chaining (next_addr from completed descriptor)
    always_comb begin
        w_desc_addr_fifo_wr_valid = 1'b0;
        w_desc_addr_fifo_wr_data = '0;

        // Source 1: APB skid buffer (initial descriptor fetch, 64-bit address)
        if (w_apb_skid_valid_out && w_apb_skid_ready_out) begin
            w_desc_addr_fifo_wr_valid = 1'b1;
            w_desc_addr_fifo_wr_data = w_apb_skid_dout;
        end
        // Source 2: Autonomous chaining (next_addr is 32-bit, zero-extend to 64-bit)
        else if (w_should_chain && (r_current_state == RD_COMPLETE)) begin
            w_desc_addr_fifo_wr_valid = 1'b1;
            w_desc_addr_fifo_wr_data = {{(ADDR_WIDTH-32){1'b0}}, w_next_addr};  // Zero-extend 32→64 bit
        end
    end

    //=========================================================================
    // Autonomous Chaining Logic
    //=========================================================================
    // Decides whether to automatically fetch next descriptor without APB intervention
    //
    // Chaining Decision Tree:
    //   Level 1: Basic eligibility (w_chain_condition)
    //     - next_descriptor_ptr != 0 (non-null pointer)
    //     - descriptor.last == 0 (not explicitly marked as last)
    //
    //   Level 2: Address validation (w_next_addr_valid)
    //     - next_addr within cfg_addr0_base..cfg_addr0_limit OR
    //     - next_addr within cfg_addr1_base..cfg_addr1_limit
    //     (Prevents runaway chaining to invalid memory regions)
    //
    //   Level 3: Final decision (w_should_chain)
    //     - Level 1 + Level 2 conditions met
    //     - !r_descriptor_error (no fetch error occurred)
    //     - w_desc_fifo_wr_ready (descriptor FIFO has space)
    //
    // If w_should_chain = 1:
    //   next_addr → descriptor address FIFO → autonomous fetch
    //   Scheduler never sees gap, continuous descriptor flow
    //
    // If w_should_chain = 0:
    //   Engine goes idle, waits for next APB kick-off

    // Address validation for chaining
    // STREAM descriptors use 32-bit next_descriptor_ptr, zero-extend to 64-bit for comparison
    logic [ADDR_WIDTH-1:0] w_next_addr_extended;
    assign w_next_addr_extended = {{(ADDR_WIDTH-32){1'b0}}, w_next_addr};

    // Check if next_addr falls within either configured address range
    assign w_next_addr_valid = (w_next_addr_extended >= cfg_addr0_base && w_next_addr_extended <= cfg_addr0_limit) ||
                                (w_next_addr_extended >= cfg_addr1_base && w_next_addr_extended <= cfg_addr1_limit);

    // Level 1: Basic chaining eligibility
    // Chain if: pointer is non-zero AND last flag not set AND descriptor is valid
    assign w_chain_condition = (w_next_addr != '0) && !w_desc_last && w_desc_valid;

    // Level 3: Final chaining decision
    // Combine all conditions for safe autonomous chaining
    assign w_should_chain = w_chain_condition &&        // Basic eligibility
                            w_next_addr_valid &&         // Address range check
                            !r_descriptor_error &&       // No fetch errors
                            w_desc_fifo_wr_ready;        // FIFO has space

    //=========================================================================
    // Enhanced Descriptor FIFO with EOS/EOL/EOD Support
    //=========================================================================

    // FIFO ready for writes when descriptor fetch completes
    assign w_desc_fifo_wr_valid = (r_current_state == RD_COMPLETE) && !r_channel_reset_active;

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
    // Parses fetched descriptor data to extract control fields
    //
    // STREAM Descriptor Format: 256-bit descriptor (bits [255:0] of 512-bit AXI data)
    //
    // Field Layout (from stream_pkg.sv):
    //   [63:0]    src_addr            - Source memory address (64-bit, must be aligned)
    //   [127:64]  dst_addr            - Destination memory address (64-bit, must be aligned)
    //   [159:128] length              - Transfer length in BEATS (not bytes!)
    //   [191:160] next_descriptor_ptr - Address of next descriptor (32-bit, 0 = last)
    //   [192]     valid               - Descriptor valid flag
    //   [193]     gen_irq             - Generate interrupt on completion
    //   [194]     last                - Last descriptor in chain (explicit termination)
    //   [195]     error               - Descriptor error flag
    //   [199:196] channel_id          - Channel identifier (not used by descriptor engine)
    //   [207:200] priority            - Descriptor priority (not used by descriptor engine)
    //   [255:208] reserved            - Reserved for future use
    //
    // Key Fields for Chaining:
    //   - next_descriptor_ptr: If != 0 AND last == 0, autonomous chaining occurs
    //   - last: Explicit chain termination flag (overrides next_descriptor_ptr)
    //
    // Enhanced Control Signals (future use):
    //   - EOS/EOL/EOD: Stream boundary markers (currently unused, set to 0)
    //   - pkt_type: Descriptor type classification (currently unused, set to 0)

    // Extract enhanced control fields from descriptor data
    always_comb begin
        // Default values for unused/future features
        w_desc_eos = 1'b0;   // End of Stream (future: multi-stream support)
        w_desc_eol = 1'b0;   // End of Line (future: 2D transfer support)
        w_desc_eod = 1'b0;   // End of Data (future: segmented transfer support)
        w_desc_last = 1'b0;
        w_desc_type = 2'b00; // Descriptor type (future: different transfer modes)
        w_next_addr = 32'h0;

        // Extract active fields from STREAM descriptor format
        w_next_addr = r_descriptor_data[191:160];    // Next descriptor pointer (32-bit)
        w_desc_last = r_descriptor_data[194];        // Last flag (explicit chain termination)
        w_desc_valid = r_descriptor_data[192];       // Valid flag - descriptor is valid

        // Boundary flags reserved for future enhancements
        // (e.g., multi-stream, 2D transfers, segmented operations)
        w_desc_eos = 1'b0;
        w_desc_eol = 1'b0;
        w_desc_eod = 1'b0;
        w_desc_type = 2'b00;
    end

    //=========================================================================
    // Descriptor Validation
    //=========================================================================

    // Address range validation
    assign w_addr_range_valid = ((r_axi_read_addr >= cfg_addr0_base && r_axi_read_addr <= cfg_addr0_limit) ||
                                (r_axi_read_addr >= cfg_addr1_base && r_axi_read_addr <= cfg_addr1_limit));

    // Overall validation
    // assign w_validation_passed = w_addr_range_valid && w_axi_response_ok;  // UNUSED, commented out

    //=========================================================================
    // AXI Response Monitoring
    //=========================================================================

    // Check if AXI response is for our channel
    assign w_our_axi_response = r_valid && (r_id[CHAN_WIDTH-1:0] == CHANNEL_ID[CHAN_WIDTH-1:0]);

    // AXI response validation
    assign w_axi_response_ok = (r_resp == 2'b00); // OKAY response

    // We're ready when waiting for our response
    assign r_ready = (r_current_state == RD_WAIT_DATA) && w_our_axi_response;

    //=========================================================================
    // FSM State Machine with Channel Reset (reuses RAPIDS read_engine_state_t)
    //=========================================================================
    // Descriptor fetch FSM
    //
    // State Flow (nominal):
    //   RD_IDLE → RD_ISSUE_ADDR → RD_WAIT_DATA → RD_COMPLETE → RD_IDLE
    //
    // State Flow (error):
    //   RD_WAIT_DATA → RD_ERROR → RD_IDLE
    //
    // State Descriptions:
    //   RD_IDLE:       Waiting for descriptor address in address FIFO
    //                  Sources: 1) APB skid buffer (initial kick-off)
    //                           2) Autonomous chaining (next_descriptor_ptr)
    //                  Action: Pop address, latch to r_axi_read_addr
    //
    //   RD_ISSUE_ADDR: Issue AXI AR transaction for descriptor fetch
    //                  Action: Assert ar_valid, wait for ar_ready
    //
    //   RD_WAIT_DATA:  Wait for AXI R channel response
    //                  Action: Monitor r_valid with matching r_id
    //                          Latch r_data to r_descriptor_data
    //                          Check r_resp for errors
    //
    //   RD_COMPLETE:   Descriptor fetched successfully
    //                  Action: Push descriptor to descriptor FIFO
    //                          Check autonomous chaining conditions
    //                          If chaining, push next_addr to address FIFO
    //
    //   RD_ERROR:      AXI response error (r_resp != OKAY)
    //                  Action: Set r_descriptor_error flag
    //                          Return to idle (discard descriptor)
    //
    // Channel Reset Handling:
    //   During r_channel_reset_active: Force transition to RD_IDLE from any state
    //   This safely aborts in-flight operations

    // State register
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_current_state <= RD_IDLE;
        end else begin
            r_current_state <= w_next_state;
        end
    )

    logic         w_pkt_error;                 // [195] Error flag
    logic         w_pkt_last;                  // [194] Last in chain
    logic         w_pkt_gen_irq;               // [193] Generate interrupt (renamed from 'interrupt' - C++ keyword)
    logic         w_pkt_valid;                 // [192] Valid descriptor
    logic [31:0]  w_pkt_next_descriptor_ptr;   // [191:160] Next descriptor address
    logic [31:0]  w_pkt_length;                // [159:128] Length in BEATS
    logic [63:0]  w_pkt_dst_addr;              // [127:64] Destination address
    logic [63:0]  w_pkt_src_addr;              // [63:0] Source address

    always_comb begin
        w_pkt_error = r_data[195];
        w_pkt_last = r_data[194];
        w_pkt_gen_irq = r_data[193];
        w_pkt_valid = r_data[192];
        w_pkt_next_descriptor_ptr = r_data[191:160];
        w_pkt_length = r_data[159:128];
        w_pkt_dst_addr = r_data[127:64];
        w_pkt_src_addr = r_data[63:0];
    end

    // Next state logic with channel reset support
    always_comb begin
        w_next_state = r_current_state;  // Default: hold state

        case (r_current_state)
            RD_IDLE: begin
                // Wait for descriptor address to fetch
                if (r_channel_reset_active) begin
                    w_next_state = RD_IDLE; // Stay in idle during reset
                end else if (w_desc_addr_fifo_rd_valid && w_desc_addr_fifo_rd_ready) begin
                    w_next_state = RD_ISSUE_ADDR; // Address available, proceed to fetch
                end
            end

            RD_ISSUE_ADDR: begin
                // Issue AXI AR transaction
                if (r_channel_reset_active) begin
                    w_next_state = RD_IDLE; // Reset aborts operation
                end else if (ar_ready) begin
                    w_next_state = RD_WAIT_DATA; // AR accepted, wait for data
                end
                // Note: Stays in ISSUE_ADDR until ar_ready or reset
            end

            RD_WAIT_DATA: begin
                // Wait for AXI R channel response
                if (r_channel_reset_active) begin
                    w_next_state = RD_IDLE; // Reset aborts operation
                end else if (w_our_axi_response && r_valid) begin
                    // Our response arrived (r_id matches CHANNEL_ID)
                    if (w_axi_response_ok) begin
                        w_next_state = RD_COMPLETE;  // OKAY response → complete
                    end else begin
                        w_next_state = RD_ERROR;     // Error response → error state
                    end
                end
                // Note: Stays in WAIT_DATA until response or reset
            end

            RD_COMPLETE: begin
                // Push descriptor to FIFO, check chaining
                if (w_desc_fifo_wr_ready) begin
                    // Descriptor accepted by FIFO
                    // Note: Autonomous chaining logic runs in parallel
                    //       If w_should_chain=1, next_addr pushed to address FIFO
                    w_next_state = RD_IDLE;  // Back to idle (may immediately fetch next)
                end
                // Note: Stays in COMPLETE until FIFO ready
            end

            RD_ERROR: begin
                // AXI error occurred, discard descriptor
                w_next_state = RD_IDLE;  // Return to idle (no descriptor pushed)
            end

            default: begin
                // Safety: undefined state → idle
                w_next_state = RD_IDLE;
            end
        endcase
    end

    //=========================================================================
    // State Machine Registers and Control
    //=========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_apb_operation_active <= 1'b0;
            r_axi_read_active <= 1'b0;
            r_axi_read_addr <= 64'h0;
            r_axi_read_resp <= 2'b00;
            r_descriptor_data <= '0;
            r_saved_next_addr <= 64'h0;
            r_descriptor_error <= 1'b0;
        end else begin
            case (r_current_state)
                RD_IDLE: begin
                    if (w_desc_addr_fifo_rd_valid && w_desc_addr_fifo_rd_ready) begin
                        // Pop address from descriptor address FIFO
                        r_apb_operation_active <= 1'b1;
                        r_axi_read_addr <= w_desc_addr_fifo_rd_data;
                    end
                    r_descriptor_error <= 1'b0;
                end

                RD_ISSUE_ADDR: begin
                    if (ar_ready) begin
                        r_axi_read_active <= 1'b1;
                    end
                end

                RD_WAIT_DATA: begin
                    if (w_our_axi_response && r_valid) begin
                        r_descriptor_data <= r_data;
                        r_axi_read_resp <= r_resp;
                        r_saved_next_addr <= {{(ADDR_WIDTH-32){1'b0}}, w_next_addr};  // Zero-extend 32→64 bit

                        // Check descriptor valid bit - flag error if invalid
                        if (!r_data[192]) begin  // valid bit = 0
                            r_descriptor_error <= 1'b1;
                        end
                    end
                end

                RD_COMPLETE: begin
                    if (w_desc_fifo_wr_ready) begin
                        r_apb_operation_active <= 1'b0;
                        r_axi_read_active <= 1'b0;
                    end
                end

                RD_ERROR: begin
                    r_descriptor_error <= 1'b1;
                    r_apb_operation_active <= 1'b0;
                    r_axi_read_active <= 1'b0;
                end

                default: begin
                    // Maintain state
                end
            endcase

            // Reset all operations during channel reset
            if (r_channel_reset_active) begin
                r_apb_operation_active <= 1'b0;
                r_axi_read_active <= 1'b0;
                r_descriptor_error <= 1'b0;
            end
        end
    )


    //=========================================================================
    // Enhanced Descriptor FIFO Write Data Generation
    //=========================================================================

    always_comb begin
        w_desc_fifo_wr_data = '0;

        if (r_current_state == RD_COMPLETE) begin
            // Fetched descriptor (from APB or chaining)
            w_desc_fifo_wr_data.data = r_descriptor_data;
            w_desc_fifo_wr_data.eos = w_desc_eos;
            w_desc_fifo_wr_data.eol = w_desc_eol;
            w_desc_fifo_wr_data.eod = w_desc_eod;
            w_desc_fifo_wr_data.pkt_type = w_desc_type;
        end
    end

    //=========================================================================
    // AXI Read Address Channel Output
    //=========================================================================

    assign ar_valid = (r_current_state == RD_ISSUE_ADDR) && !r_axi_read_active;
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

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_mon_valid <= 1'b0;
            r_mon_packet <= 64'h0;
        end else begin
            // Default: clear monitor packet
            r_mon_valid <= 1'b0;
            r_mon_packet <= 64'h0;

            case (r_current_state)
                RD_COMPLETE: begin
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

                RD_ERROR: begin
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
    )


    //=========================================================================
    // Address 0 Error Detection
    //=========================================================================
    // Detect invalid APB address 0 and flag as error
    // This prevents silent failures from uninitialized/null descriptor pointers

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            // Error flag cleared on reset (handled in main FSM)
        end else begin
            // Detect APB request with address 0 - this is an error condition
            if (apb_valid && !w_apb_addr_valid) begin
                r_descriptor_error <= 1'b1;
                $display("%t DESC_ENG[%0d] ERROR: APB kick-off with invalid address 0",
                        $time, CHANNEL_ID);
            end
        end
    )

    //=========================================================================
    // APB In-Progress Flag Management
    //=========================================================================
    // Prevents accepting multiple APB transactions before channel completes
    // Set: When APB transaction is accepted (handshake completes)
    // Clear: On falling edge of channel_idle (busy->idle transition)
    //
    // Note: We detect falling edge (idle high->low) which indicates the
    // scheduler has transitioned from idle to busy and back to idle,
    // meaning all descriptor chain processing is complete.

    // Detect falling edge of channel_idle (1->0 transition)
    wire w_channel_idle_falling = r_channel_idle_prev && !channel_idle;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_apb_ip <= 1'b0;
            r_channel_idle_prev <= 1'b1;  // Assume idle at reset
        end else begin
            // Track channel_idle for edge detection
            r_channel_idle_prev <= channel_idle;

            // Set apb_ip when APB transaction accepted
            if (w_apb_skid_valid_in && w_apb_skid_ready_in) begin
                r_apb_ip <= 1'b1;
            end
            // Clear apb_ip on falling edge of channel_idle
            // Falling edge indicates scheduler completed all work and returned to idle
            else if (w_channel_idle_falling && r_apb_ip) begin
                r_apb_ip <= 1'b0;
            end
        end
    )

    //=========================================================================
    // Output Assignments
    //=========================================================================

    // Scheduler interface with EOS/EOL/EOD support
    assign descriptor_valid = w_desc_fifo_rd_valid && !r_descriptor_error;  // Block valid on error
    assign descriptor_packet = w_desc_fifo_rd_data.data;
    assign descriptor_error = r_descriptor_error;

    // Enhanced control signal outputs
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

    // Channel reset properties
    property channel_reset_blocks_inputs;
        @(posedge clk) disable iff (!rst_n)
        r_channel_reset_active |-> !w_apb_skid_ready_out;
    endproperty
    assert property (channel_reset_blocks_inputs);

    property channel_reset_clears_operations;
        @(posedge clk) disable iff (!rst_n)
        r_channel_reset_active |-> ##[1:10] !r_apb_operation_active;
    endproperty
    assert property (channel_reset_clears_operations);

    property channel_reset_idle_signal;
        @(posedge clk) disable iff (!rst_n)
        descriptor_engine_idle |-> (r_current_state == RD_IDLE && !r_channel_reset_active);
    endproperty
    assert property (channel_reset_idle_signal);
    `endif

endmodule : descriptor_engine
